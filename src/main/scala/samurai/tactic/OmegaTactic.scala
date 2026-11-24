package samurai.tactic

import scala.collection.mutable
import scala.util.boundary
import scala.util.boundary.break
import samurai.elab.ElabEnv
import samurai.kernel.*
import samurai.util.{Diagnostic, Span}

/**
 * Sound, proof-producing linear `Nat` arithmetic & inequality decision procedure (`omega` / `lia`).
 *
 * Handles `Le`, `Lt`, `ble`, `blt`, `beq`, `===`, `!==`, `Not`, `False`, `And`, `+`, `*`, `0`, `Nat.Succ`.
 * Every proof step synthesizes an explicit, 100% axiom-free core `Term` checked from scratch
 * by `samurai.kernel.TypeChecker` (using decidability of `ble` for constructive contradiction refutation).
 */
object OmegaTactic {

  private val NatType: Term = Term.Ind("Nat")
  private val BoolType: Term = Term.Ind("Bool")
  private val TrueCtor: Term = Term.Ctor("Bool", "True")
  private val FalseCtor: Term = Term.Ctor("Bool", "False")

  private val RequiredLemmas: List[String] = List(
    "zeroLe", "leRefl", "leTrans", "leAntisym", "leAddRight", "leAddBoth",
    "leAddCancelRight", "leAddIntroRight", "leSuccZeroFalse", "leSuccSelfFalse",
    "leToBle", "bleToLe", "bleFalseToLeSucc", "leSuccToBleFalse",
    "bltFalseToLe", "leToBltFalse", "beqToEq", "eqToBeq", "leTransport"
  )

  private final case class LeFact(lhs: ArithTactic.Poly, rhs: ArithTactic.Poly, proof: Term)
  private final case class DiffEdge(from: Option[List[Term]], to: Option[List[Term]], weight: Int, proof: Term)

  private enum ArithAtom {
    case ATrue
    case AFalse
    case ALe(lhs: Term, rhs: Term)
    case ALt(lhs: Term, rhs: Term) // `Lt(lhs, rhs)` or `blt(lhs, rhs) === true` (definitionally `ble(Succ(lhs), rhs) === true`)
    case ABle(lhs: Term, rhs: Term, expected: Boolean, flipped: Boolean)
    case ABlt(lhs: Term, rhs: Term, expected: Boolean, flipped: Boolean)
    case ABeqTrue(lhs: Term, rhs: Term, flipped: Boolean)
    case ANatEq(lhs: Term, rhs: Term)
  }

  def solve(env: ElabEnv, state: ProofState, span: Span): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    if (!ArithTactic.hasRequiredLemmas(env.kernelEnv)) {
      return Left(Diagnostic(Diagnostic.Severity.Error, "T070", "'omega' requires Nat algebra lemmas (import Nat.*)", span))
    }
    val missing = RequiredLemmas.filterNot(env.kernelEnv.contains)
    if (missing.nonEmpty) {
      return Left(
        Diagnostic(
          Diagnostic.Severity.Error,
          "T070",
          s"'omega' requires Nat ordering lemmas (import Nat.*); missing: ${missing.mkString(", ")}",
          span
        )
      )
    }

    solveGoal(env.kernelEnv, goal.localCtx, goal.targetType) match {
      case Some(proof) =>
        Right((env, state.replaceHead(Nil, _ => proof, state.nextGoalId)))
      case None =>
        Left(
          Diagnostic(
            Diagnostic.Severity.Error,
            "T071",
            s"'omega' could not prove goal:\n${goal.formatHuman(env.kernelEnv)}",
            span
          )
        )
    }
  }

  /** Direct kernel-level entry point reusable from ProofSearch and well-founded decrease proving. */
  def solveGoal(kernelEnv: KernelEnv, localCtx: LocalCtx, targetType: Term): Option[Term] = {
    if (!ArithTactic.hasRequiredLemmas(kernelEnv) || !RequiredLemmas.forall(kernelEnv.contains)) return None
    solveWithDepth(kernelEnv, localCtx, targetType, allowDecidableSplit = true)
  }

  /**
   * Recognize arithmetic propositions BEFORE NbE unfolds `Lt(a, b)` / `blt(a, b)` / `ble(Succ(a), b)` into a `match`,
   * and ALSO recognize already-unfolded `match b { Zero => false; Succ(p) => ble(a, p) }`!
   */
  private def classifyProp(kernelEnv: KernelEnv, localCtx: LocalCtx, propTerm: Term): Option[ArithAtom] = {
    def tryFolded(t: Term): Option[ArithAtom] = {
      val (head, args) = Term.splitApps(t)
      head match {
        case Term.Ind("True")  => Some(ArithAtom.ATrue)
        case Term.Ind("False") => Some(ArithAtom.AFalse)
        case Term.Ind("Le") if args.length == 2 =>
          Some(ArithAtom.ALe(args(0), args(1)))
        case Term.Const("Lt") if args.length == 2 =>
          Some(ArithAtom.ALt(args(0), args(1)))
        case Term.Ind("Eq") if args.length == 3 =>
          val eqTyNorm = NbE.normalize(kernelEnv, localCtx, args(0))
          if (eqTyNorm == NatType) {
            Some(ArithAtom.ANatEq(args(1), args(2)))
          } else if (eqTyNorm == BoolType) {
            classifyBoolEq(args(1), args(2), flipped = false)
              .orElse(classifyBoolEq(args(2), args(1), flipped = true))
          } else None
        case _ => None
      }
    }

    tryFolded(propTerm).orElse {
      val norm = NbE.normalize(kernelEnv, localCtx, propTerm)
      if (norm != propTerm) tryFolded(norm) else None
    }
  }

  private def classifyBoolEq(expr: Term, boolLit: Term, flipped: Boolean): Option[ArithAtom] = {
    if (boolLit != TrueCtor && boolLit != FalseCtor) return None
    val expect = boolLit == TrueCtor
    val (h, as) = Term.splitApps(expr)
    if (isBleHead(h) && as.length == 2) {
      Some(ArithAtom.ABle(as(0), as(1), expect, flipped))
    } else if (isBltHead(h) && as.length == 2) {
      Some(ArithAtom.ABlt(as(0), as(1), expect, flipped))
    } else if (expect && isBeqHead(h) && as.length == 2) {
      Some(ArithAtom.ABeqTrue(as(0), as(1), flipped))
    } else {
      // Recognize unfolded `ble(Succ(a), b)` -> `b match { case Zero => false; case Succ(p) => ble(a, p) }`!
      expr match {
        case Term.Match("Nat", Nil, _, scrutinee, List(MatchBranch("Zero", Nil, FalseCtor), MatchBranch("Succ", List(_), succBody))) =>
          val (bh, bas) = Term.splitApps(succBody)
          if (isBleHead(bh) && bas.length == 2 && bas(1) == Term.Var(0) && !Term.freeVarOccurs(bas(0), 0)) {
            val a = Term.shift(bas(0), -1)
            Some(ArithAtom.ABle(Term.App(Term.Ctor("Nat", "Succ"), a), scrutinee, expect, flipped))
          } else None
        case _ => None
      }
    }
  }

  private def solveWithDepth(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    targetType: Term,
    allowDecidableSplit: Boolean
  ): Option[Term] = boundary {
    val normTarget = NbE.normalize(kernelEnv, localCtx, targetType)

    // Handle `Not(P)` i.e. `P => False` by introducing `P` into context (keeping folded domain when possible!)
    targetType match {
      case Term.App(Term.Const("Not"), innerP) =>
        val freshName = s"_om${localCtx.depth}"
        val innerCtx = localCtx.push(freshName, innerP)
        break(
          solveWithDepth(kernelEnv, innerCtx, Term.Ind("False"), allowDecidableSplit)
            .map(body => Term.Lam(freshName, innerP, body))
        )
      case _ => ()
    }
    normTarget match {
      case Term.Pi(name, dom, Term.Ind("False")) =>
        val freshName = if (name == "_" || name.isEmpty) s"_om${localCtx.depth}" else name
        val innerCtx = localCtx.push(freshName, dom)
        break(
          solveWithDepth(kernelEnv, innerCtx, Term.Ind("False"), allowDecidableSplit)
            .map(body => Term.Lam(freshName, dom, body))
        )
      case _ => ()
    }

    // Handle conjunction `P /\ Q`
    val (tHead, tArgs) = Term.splitApps(normTarget)
    tHead match {
      case Term.Ind("True") =>
        break(Some(Term.Ctor("True", "Intro")))
      case Term.Ind("And") if tArgs.length == 2 =>
        val combined = for {
          p1 <- solveWithDepth(kernelEnv, localCtx, tArgs(0), allowDecidableSplit)
          p2 <- solveWithDepth(kernelEnv, localCtx, tArgs(1), allowDecidableSplit)
        } yield Term.apps(Term.Ctor("And", "Intro"), List(tArgs(0), tArgs(1), p1, p2))
        break(combined)
      case _ => ()
    }

    val solver = new SolverCtx(kernelEnv, localCtx)
    solver.ingestContext()

    // 1. Check if the context itself is already inconsistent!
    solver.deriveFalse().foreach { falsePf =>
      break(Some(mkAbsurd(targetType, falsePf)))
    }

    // 2. Try proving the target directly from the saturated linear system (check folded targetType first!)
    solver.proveProp(targetType).foreach(pf => break(Some(pf)))

    // 3. Constructive proof-by-contradiction using decidability of `ble` on `Nat`!
    if (allowDecidableSplit) {
      extractBleDecisionTarget(kernelEnv, localCtx, targetType).foreach { case (lhs, rhs, wrapTrue, wrapFalseGoal) =>
        val cmpTerm = Term.apps(Term.Const("ble"), List(lhs, rhs))
        val cmp1 = Term.shift(cmpTerm, 1)
        val target1 = Term.shift(targetType, 1)
        val motive = Term.Lam(
          "_b",
          BoolType,
          Term.Pi("_cmpEq", Term.apps(Term.Ind("Eq"), List(BoolType, cmp1, Term.Var(0))), Term.shift(target1, 1))
        )

        val trueCtx = localCtx.push("_cmpEq", Term.apps(Term.Ind("Eq"), List(BoolType, cmpTerm, TrueCtor)))
        val trueProofOpt = wrapTrue(trueCtx, Term.Var(0))

        val falseCtx = localCtx.push("_cmpEq", Term.apps(Term.Ind("Eq"), List(BoolType, cmpTerm, FalseCtor)))
        val falseProofOpt = wrapFalseGoal(falseCtx, Term.Var(0))

        (trueProofOpt, falseProofOpt) match {
          case (Some(tPf), Some(fPf)) =>
            val trueLam = Term.Lam("_cmpEq", Term.apps(Term.Ind("Eq"), List(BoolType, cmpTerm, TrueCtor)), tPf)
            val falseLam = Term.Lam("_cmpEq", Term.apps(Term.Ind("Eq"), List(BoolType, cmpTerm, FalseCtor)), fPf)
            val matchTerm = Term.Match(
              "Bool",
              Nil,
              motive,
              cmpTerm,
              List(MatchBranch("True", Nil, trueLam), MatchBranch("False", Nil, falseLam))
            )
            break(Some(Term.App(matchTerm, Term.apps(Term.Ctor("Eq", "Refl"), List(BoolType, cmpTerm)))))
          case _ => ()
        }
      }
    }

    None
  }

  private def extractBleDecisionTarget(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    targetType: Term
  ): Option[(Term, Term, (LocalCtx, Term) => Option[Term], (LocalCtx, Term) => Option[Term])] = {
    classifyProp(kernelEnv, localCtx, targetType).flatMap {
      case ArithAtom.ALe(a, b) =>
        Some((
          a,
          b,
          (_, eqVar) => Some(Term.apps(Term.Const("bleToLe"), List(Term.shift(a, 1), Term.shift(b, 1), eqVar))),
          (fCtx, _) =>
            solveWithDepth(kernelEnv, fCtx, Term.Ind("False"), allowDecidableSplit = false)
              .map(fp => mkAbsurd(Term.shift(targetType, 1), fp))
        ))

      case ArithAtom.ALt(a, b) =>
        val succA = Term.App(Term.Ctor("Nat", "Succ"), a)
        Some((
          succA,
          b,
          (_, eqVar) => Some(eqVar),
          (fCtx, _) =>
            solveWithDepth(kernelEnv, fCtx, Term.Ind("False"), allowDecidableSplit = false)
              .map(fp => mkAbsurd(Term.shift(targetType, 1), fp))
        ))

      case ArithAtom.ABle(a, b, expectTrue, flipped) =>
        if (expectTrue) {
          Some((
            a,
            b,
            (_, eqVar) =>
              Some(
                if (flipped) mkBoolEqSym(Term.apps(Term.Const("ble"), List(Term.shift(a, 1), Term.shift(b, 1))), TrueCtor, eqVar)
                else eqVar
              ),
            (fCtx, _) =>
              solveWithDepth(kernelEnv, fCtx, Term.Ind("False"), allowDecidableSplit = false)
                .map(fp => mkAbsurd(Term.shift(targetType, 1), fp))
          ))
        } else {
          Some((
            a,
            b,
            (tCtx, _) =>
              solveWithDepth(kernelEnv, tCtx, Term.Ind("False"), allowDecidableSplit = false)
                .map(fp => mkAbsurd(Term.shift(targetType, 1), fp)),
            (_, eqVar) =>
              Some(
                if (flipped) mkBoolEqSym(Term.apps(Term.Const("ble"), List(Term.shift(a, 1), Term.shift(b, 1))), FalseCtor, eqVar)
                else eqVar
              )
          ))
        }

      case ArithAtom.ABlt(a, b, expectTrue, flipped) =>
        val succA = Term.App(Term.Ctor("Nat", "Succ"), a)
        if (expectTrue) {
          Some((
            succA,
            b,
            (_, eqVar) =>
              Some(
                if (flipped) mkBoolEqSym(Term.apps(Term.Const("ble"), List(Term.shift(succA, 1), Term.shift(b, 1))), TrueCtor, eqVar)
                else eqVar
              ),
            (fCtx, _) =>
              solveWithDepth(kernelEnv, fCtx, Term.Ind("False"), allowDecidableSplit = false)
                .map(fp => mkAbsurd(Term.shift(targetType, 1), fp))
          ))
        } else {
          Some((
            succA,
            b,
            (tCtx, _) =>
              solveWithDepth(kernelEnv, tCtx, Term.Ind("False"), allowDecidableSplit = false)
                .map(fp => mkAbsurd(Term.shift(targetType, 1), fp)),
            (_, eqVar) =>
              Some(
                if (flipped) mkBoolEqSym(Term.apps(Term.Const("ble"), List(Term.shift(succA, 1), Term.shift(b, 1))), FalseCtor, eqVar)
                else eqVar
              )
          ))
        }

      case _ => None
    }
  }

  private def isBleHead(h: Term): Boolean = h match {
    case Term.Const("ble") | Term.Fix("ble", _, _, _) => true
    case _                                            => false
  }

  private def isBltHead(h: Term): Boolean = h match {
    case Term.Const("blt") | Term.Fix("blt", _, _, _) => true
    case _                                            => false
  }

  private def isBeqHead(h: Term): Boolean = h match {
    case Term.Const("beq") | Term.Fix("beq", _, _, _) => true
    case _                                            => false
  }

  private def mkAbsurd(targetType: Term, falseProof: Term): Term =
    Term.Match("False", Nil, Term.Lam("_f", Term.Ind("False"), Term.shift(targetType, 1)), falseProof, Nil)

  private def mkBoolEqSym(lhs: Term, rhs: Term, proof: Term): Term = {
    val lhs1 = Term.shift(lhs, 1)
    val lhs2 = Term.shift(lhs, 2)
    val motive = Term.Lam(
      "_y",
      BoolType,
      Term.Lam(
        "_q",
        Term.apps(Term.Ind("Eq"), List(BoolType, lhs1, Term.Var(0))),
        Term.apps(Term.Ind("Eq"), List(BoolType, Term.Var(1), lhs2))
      )
    )
    Term.Match("Eq", List(BoolType, lhs), motive, proof, List(MatchBranch("Refl", Nil, Term.apps(Term.Ctor("Eq", "Refl"), List(BoolType, lhs)))))
  }

  // ===========================================================================
  // Polynomial Multiset Helpers
  // ===========================================================================

  private def monoKey(m: List[Term]): String = m.map(Pretty.show(_)).mkString("*")

  private def compareMonos(m1: List[Term], m2: List[Term]): Int =
    monoKey(m1).compareTo(monoKey(m2))

  private def sortMonos(ms: List[List[Term]]): List[List[Term]] =
    ms.sortWith((a, b) => compareMonos(a, b) < 0)

  private def polyZero: ArithTactic.Poly = ArithTactic.Poly(0, Nil)

  private def polyAdd(a: ArithTactic.Poly, b: ArithTactic.Poly): ArithTactic.Poly =
    ArithTactic.Poly(a.constVal + b.constVal, sortMonos(a.monos ++ b.monos))

  private def polyDiff(a: ArithTactic.Poly, b: ArithTactic.Poly): (ArithTactic.Poly, ArithTactic.Poly, ArithTactic.Poly) = {
    val commonC = math.min(a.constVal, b.constVal)
    val aRem = mutable.ListBuffer.empty[List[Term]]
    val commonM = mutable.ListBuffer.empty[List[Term]]
    val bPool = mutable.ListBuffer.from(b.monos)

    for (m <- a.monos) {
      val idx = bPool.indexWhere(bm => bm == m)
      if (idx >= 0) {
        commonM += m
        bPool.remove(idx)
      } else {
        aRem += m
      }
    }
    (
      ArithTactic.Poly(a.constVal - commonC, sortMonos(aRem.toList)),
      ArithTactic.Poly(b.constVal - commonC, sortMonos(bPool.toList)),
      ArithTactic.Poly(commonC, sortMonos(commonM.toList))
    )
  }

  private def nodePoly(node: Option[List[Term]]): ArithTactic.Poly = node match {
    case None    => polyZero
    case Some(m) => ArithTactic.Poly(0, List(m))
  }

  private def nodeTerm(node: Option[List[Term]]): Term =
    ArithTactic.polyTerm(nodePoly(node))

  private def nodeKey(node: Option[List[Term]]): String = node match {
    case None    => "$ZERO$"
    case Some(m) => monoKey(m)
  }

  // ===========================================================================
  // Proof-Carrying Difference-Constraint & Linear Inequality Solver
  // ===========================================================================

  private final class SolverCtx(kernelEnv: KernelEnv, localCtx: LocalCtx) {

    private val generalFacts = mutable.ListBuffer.empty[LeFact]
    private val negatedProps = mutable.ListBuffer.empty[(Term, Term)]
    private val edges = mutable.Map.empty[(String, String), DiffEdge]
    private val nodes = mutable.Map.empty[String, Option[List[Term]]]
    private var contradictionProof: Option[Term] = None

    nodes(nodeKey(None)) = None

    private def registerNode(n: Option[List[Term]]): Unit =
      nodes.getOrElseUpdate(nodeKey(n), n)

    private def transportLe(a1: Term, a2: Term, b1: Term, b2: Term, pf: Term): Option[Term] = {
      for {
        eqA <- ArithTactic.proveNatEq(kernelEnv, localCtx, a1, a2)
        eqB <- ArithTactic.proveNatEq(kernelEnv, localCtx, b1, b2)
      } yield Term.apps(Term.Const("leTransport"), List(a1, a2, b1, b2, eqA, eqB, pf))
    }

    private def cancelLe(pL: ArithTactic.Poly, pR: ArithTactic.Poly, pf: Term): LeFact = {
      val (lOnly, rOnly, common) = polyDiff(pL, pR)
      if (common.constVal == 0 && common.monos.isEmpty) {
        LeFact(pL, pR, pf)
      } else {
        val tL = ArithTactic.polyTerm(pL)
        val tR = ArithTactic.polyTerm(pR)
        val tLO = ArithTactic.polyTerm(lOnly)
        val tRO = ArithTactic.polyTerm(rOnly)
        val tCom = ArithTactic.polyTerm(common)
        transportLe(tL, ArithTactic.mkAdd(tLO, tCom), tR, ArithTactic.mkAdd(tRO, tCom), pf) match {
          case Some(shifted) =>
            val reduced = Term.apps(Term.Const("leAddCancelRight"), List(tLO, tRO, tCom, shifted))
            LeFact(lOnly, rOnly, reduced)
          case None =>
            LeFact(pL, pR, pf)
        }
      }
    }

    private def checkZeroContradiction(fact: LeFact): Unit = {
      if (contradictionProof.isDefined) return
      if (fact.rhs.constVal == 0 && fact.rhs.monos.isEmpty && fact.lhs.constVal >= 1) {
        val predPoly = ArithTactic.Poly(fact.lhs.constVal - 1, fact.lhs.monos)
        val predTerm = ArithTactic.polyTerm(predPoly)
        val succTerm = Term.App(Term.Ctor("Nat", "Succ"), predTerm)
        transportLe(ArithTactic.polyTerm(fact.lhs), succTerm, ArithTactic.natLit(0), ArithTactic.natLit(0), fact.proof).foreach { pf =>
          contradictionProof = Some(Term.apps(Term.Const("leSuccZeroFalse"), List(predTerm, pf)))
        }
      }
    }

    private def addEdge(from: Option[List[Term]], to: Option[List[Term]], weight: Int, proof: Term): Unit = {
      registerNode(from)
      registerNode(to)
      val kFrom = nodeKey(from)
      val kTo = nodeKey(to)
      if (kFrom == kTo && weight < 0) {
        val k = -weight
        val uPoly = nodePoly(from)
        val lhsPoly = polyAdd(uPoly, ArithTactic.Poly(k, Nil))
        val reduced = cancelLe(lhsPoly, uPoly, proof)
        checkZeroContradiction(reduced)
        return
      }
      if (kFrom == kTo) return
      edges.get((kFrom, kTo)) match {
        case Some(existing) if existing.weight <= weight => ()
        case _ =>
          edges((kFrom, kTo)) = DiffEdge(from, to, weight, proof)
      }
    }

    private def recordLeRaw(lhsTerm: Term, rhsTerm: Term, rawProof: Term): Unit = {
      val (pL, eqL) = ArithTactic.normalizeNat(kernelEnv, localCtx, lhsTerm)
      val (pR, eqR) = ArithTactic.normalizeNat(kernelEnv, localCtx, rhsTerm)
      val canonPf = Term.apps(
        Term.Const("leTransport"),
        List(lhsTerm, ArithTactic.polyTerm(pL), rhsTerm, ArithTactic.polyTerm(pR), eqL, eqR, rawProof)
      )
      recordLePoly(pL, pR, canonPf)
    }

    private def recordLePoly(pL: ArithTactic.Poly, pR: ArithTactic.Poly, pf: Term): Unit = {
      val reduced = cancelLe(pL, pR, pf)
      checkZeroContradiction(reduced)
      if (contradictionProof.isDefined) return

      generalFacts += reduced

      val (l, r, rPf) = (reduced.lhs, reduced.rhs, reduced.proof)
      (l.monos, r.monos) match {
        case (Nil, Nil) =>
          ()
        case (Nil, List(v)) =>
          addDiffEdgeFromFact(None, Some(v), r.constVal - l.constVal, l, r, rPf)
        case (List(u), Nil) =>
          addDiffEdgeFromFact(Some(u), None, r.constVal - l.constVal, l, r, rPf)
        case (List(u), List(v)) =>
          addDiffEdgeFromFact(Some(u), Some(v), r.constVal - l.constVal, l, r, rPf)
        case (uList, List(v)) if uList.length >= 2 =>
          for (idx <- uList.indices) {
            val u = uList(idx)
            val rest = ArithTactic.Poly(0, uList.patch(idx, Nil, 1))
            val subL = ArithTactic.Poly(l.constVal, List(u))
            val subLT = ArithTactic.polyTerm(subL)
            val restT = ArithTactic.polyTerm(rest)
            val introPf = Term.apps(Term.Const("leAddIntroRight"), List(subLT, restT))
            transportLe(subLT, subLT, ArithTactic.mkAdd(subLT, restT), ArithTactic.polyTerm(l), introPf).foreach { step1 =>
              val combined = Term.apps(Term.Const("leTrans"), List(subLT, ArithTactic.polyTerm(l), ArithTactic.polyTerm(r), step1, rPf))
              addDiffEdgeFromFact(Some(u), Some(v), r.constVal - l.constVal, subL, r, combined)
            }
          }
        case (uList, Nil) if uList.length >= 2 =>
          for (idx <- uList.indices) {
            val u = uList(idx)
            val rest = ArithTactic.Poly(0, uList.patch(idx, Nil, 1))
            val subL = ArithTactic.Poly(l.constVal, List(u))
            val subLT = ArithTactic.polyTerm(subL)
            val restT = ArithTactic.polyTerm(rest)
            val introPf = Term.apps(Term.Const("leAddIntroRight"), List(subLT, restT))
            transportLe(subLT, subLT, ArithTactic.mkAdd(subLT, restT), ArithTactic.polyTerm(l), introPf).foreach { step1 =>
              val combined = Term.apps(Term.Const("leTrans"), List(subLT, ArithTactic.polyTerm(l), ArithTactic.polyTerm(r), step1, rPf))
              addDiffEdgeFromFact(Some(u), None, r.constVal - l.constVal, subL, r, combined)
            }
          }
        case _ => ()
      }
    }

    private def addDiffEdgeFromFact(
      from: Option[List[Term]],
      to: Option[List[Term]],
      weight: Int,
      factL: ArithTactic.Poly,
      factR: ArithTactic.Poly,
      factPf: Term
    ): Unit = {
      val (targetL, targetR) = edgeEndpoints(from, to, weight)
      val reduced = cancelLe(factL, factR, factPf)
      checkZeroContradiction(reduced)
      transportLe(ArithTactic.polyTerm(reduced.lhs), ArithTactic.polyTerm(targetL), ArithTactic.polyTerm(reduced.rhs), ArithTactic.polyTerm(targetR), reduced.proof).foreach { edgePf =>
        addEdge(from, to, weight, edgePf)
      }
    }

    private def edgeEndpoints(from: Option[List[Term]], to: Option[List[Term]], weight: Int): (ArithTactic.Poly, ArithTactic.Poly) = {
      if (weight >= 0) (nodePoly(from), polyAdd(nodePoly(to), ArithTactic.Poly(weight, Nil)))
      else (polyAdd(nodePoly(from), ArithTactic.Poly(-weight, Nil)), nodePoly(to))
    }

    private def composeEdges(e1: DiffEdge, e2: DiffEdge): Option[DiffEdge] = {
      val (l1, r1) = edgeEndpoints(e1.from, e1.to, e1.weight)
      val (l2, r2) = edgeEndpoints(e2.from, e2.to, e2.weight)
      val midConst = math.max(r1.constVal, l2.constVal)
      val pad1 = midConst - r1.constVal
      val pad2 = midConst - l2.constVal

      val p1L = polyAdd(l1, ArithTactic.Poly(pad1, Nil))
      val p1R = polyAdd(r1, ArithTactic.Poly(pad1, Nil))
      val p2L = polyAdd(l2, ArithTactic.Poly(pad2, Nil))
      val p2R = polyAdd(r2, ArithTactic.Poly(pad2, Nil))

      val pf1Padded =
        if (pad1 == 0) Some(e1.proof)
        else {
          val raw = Term.apps(Term.Const("leAddRight"), List(ArithTactic.polyTerm(l1), ArithTactic.polyTerm(r1), ArithTactic.natLit(pad1), e1.proof))
          transportLe(ArithTactic.mkAdd(ArithTactic.polyTerm(l1), ArithTactic.natLit(pad1)), ArithTactic.polyTerm(p1L), ArithTactic.mkAdd(ArithTactic.polyTerm(r1), ArithTactic.natLit(pad1)), ArithTactic.polyTerm(p1R), raw)
        }

      val pf2Padded =
        if (pad2 == 0) Some(e2.proof)
        else {
          val raw = Term.apps(Term.Const("leAddRight"), List(ArithTactic.polyTerm(l2), ArithTactic.polyTerm(r2), ArithTactic.natLit(pad2), e2.proof))
          transportLe(ArithTactic.mkAdd(ArithTactic.polyTerm(l2), ArithTactic.natLit(pad2)), ArithTactic.polyTerm(p2L), ArithTactic.mkAdd(ArithTactic.polyTerm(r2), ArithTactic.natLit(pad2)), ArithTactic.polyTerm(p2R), raw)
        }

      for {
        f1 <- pf1Padded
        f2 <- pf2Padded
        transPf = Term.apps(Term.Const("leTrans"), List(ArithTactic.polyTerm(p1L), ArithTactic.polyTerm(p1R), ArithTactic.polyTerm(p2R), f1, f2))
        reduced = cancelLe(p1L, p2R, transPf)
        _ = checkZeroContradiction(reduced)
        newW = e1.weight + e2.weight
        (tL, tR) = edgeEndpoints(e1.from, e2.to, newW)
        finalPf <-
          if (nodeKey(e1.from) == nodeKey(e2.to)) None
          else transportLe(ArithTactic.polyTerm(reduced.lhs), ArithTactic.polyTerm(tL), ArithTactic.polyTerm(reduced.rhs), ArithTactic.polyTerm(tR), reduced.proof)
      } yield DiffEdge(e1.from, e2.to, newW, finalPf)
    }

    private def ingestHypothesis(hypTerm: Term, hypType: Term, depth: Int): Unit = {
      if (depth <= 0 || contradictionProof.isDefined) return

      // Check folded `Not(P)` first so `Lt(a, b)` inside `Not(Lt(a, b))` stays folded!
      hypType match {
        case Term.App(Term.Const("Not"), innerP) =>
          negatedProps += ((innerP, hypTerm))
          return
        case _ => ()
      }

      classifyProp(kernelEnv, localCtx, hypType) match {
        case Some(ArithAtom.AFalse) =>
          contradictionProof = Some(hypTerm)

        case Some(ArithAtom.ALe(a, b)) =>
          recordLeRaw(a, b, hypTerm)

        case Some(ArithAtom.ALt(a, b)) =>
          val succA = Term.App(Term.Ctor("Nat", "Succ"), a)
          recordLeRaw(succA, b, Term.apps(Term.Const("bleToLe"), List(succA, b, hypTerm)))

        case Some(ArithAtom.ANatEq(lhs, rhs)) =>
          val leLR = Term.apps(
            Term.Const("leTransport"),
            List(lhs, lhs, lhs, rhs, ArithTactic.mkRefl(lhs), hypTerm, Term.App(Term.Const("leRefl"), lhs))
          )
          val leRL = Term.apps(
            Term.Const("leTransport"),
            List(lhs, rhs, lhs, lhs, hypTerm, ArithTactic.mkRefl(lhs), Term.App(Term.Const("leRefl"), lhs))
          )
          recordLeRaw(lhs, rhs, leLR)
          recordLeRaw(rhs, lhs, leRL)

        case Some(ArithAtom.ABle(a, b, true, flipped)) =>
          val pf = if (flipped) mkBoolEqSym(TrueCtor, Term.apps(Term.Const("ble"), List(a, b)), hypTerm) else hypTerm
          recordLeRaw(a, b, Term.apps(Term.Const("bleToLe"), List(a, b, pf)))

        case Some(ArithAtom.ABle(a, b, false, flipped)) =>
          val pf = if (flipped) mkBoolEqSym(FalseCtor, Term.apps(Term.Const("ble"), List(a, b)), hypTerm) else hypTerm
          val succB = Term.App(Term.Ctor("Nat", "Succ"), b)
          recordLeRaw(succB, a, Term.apps(Term.Const("bleFalseToLeSucc"), List(a, b, pf)))

        case Some(ArithAtom.ABlt(a, b, true, flipped)) =>
          val succA = Term.App(Term.Ctor("Nat", "Succ"), a)
          val pf = if (flipped) mkBoolEqSym(TrueCtor, Term.apps(Term.Const("ble"), List(succA, b)), hypTerm) else hypTerm
          recordLeRaw(succA, b, Term.apps(Term.Const("bleToLe"), List(succA, b, pf)))

        case Some(ArithAtom.ABlt(a, b, false, flipped)) =>
          val pf = if (flipped) mkBoolEqSym(FalseCtor, Term.apps(Term.Const("blt"), List(a, b)), hypTerm) else hypTerm
          recordLeRaw(b, a, Term.apps(Term.Const("bltFalseToLe"), List(a, b, pf)))

        case Some(ArithAtom.ABeqTrue(a, b, flipped)) =>
          val pf = if (flipped) mkBoolEqSym(TrueCtor, Term.apps(Term.Const("beq"), List(a, b)), hypTerm) else hypTerm
          val eqPf = Term.apps(Term.Const("beqToEq"), List(a, b, pf))
          ingestHypothesis(eqPf, Term.apps(Term.Ind("Eq"), List(NatType, a, b)), depth - 1)

        case Some(ArithAtom.ATrue) => ()

        case None =>
          val normTy = NbE.normalize(kernelEnv, localCtx, hypType)
          val (head, args) = Term.splitApps(normTy)
          head match {
            case Term.Ind("And") if args.length == 2 =>
              val (pTy, qTy) = (args(0), args(1))
              val leftPf = Term.Match(
                "And",
                List(pTy, qTy),
                Term.Lam("_a", normTy, Term.shift(pTy, 1)),
                hypTerm,
                List(MatchBranch("Intro", List("_l", "_r"), Term.Var(1)))
              )
              val rightPf = Term.Match(
                "And",
                List(pTy, qTy),
                Term.Lam("_a", normTy, Term.shift(qTy, 1)),
                hypTerm,
                List(MatchBranch("Intro", List("_l", "_r"), Term.Var(0)))
              )
              ingestHypothesis(leftPf, pTy, depth - 1)
              ingestHypothesis(rightPf, qTy, depth - 1)
            case _ =>
              normTy match {
                case Term.Pi(_, dom, Term.Ind("False")) =>
                  negatedProps += ((dom, hypTerm))
                case _ => ()
              }
          }
      }
    }

    def ingestContext(): Unit = {
      for (idx <- localCtx.entries.indices) {
        localCtx.lookupType(idx).foreach { ty =>
          ingestHypothesis(Term.Var(idx), ty, depth = 4)
        }
      }
      saturateGraph()
    }

    private def saturateGraph(): Unit = {
      if (contradictionProof.isDefined) return
      val allNodes = nodes.values.toList
      for (n <- allNodes if n.isDefined) {
        val t = nodeTerm(n)
        addEdge(None, n, 0, Term.App(Term.Const("zeroLe"), t))
      }

      val nodeKeys = nodes.keys.toList
      if (nodeKeys.length <= 24) {
        var changed = true
        var round = 0
        while (changed && round <= nodeKeys.length && contradictionProof.isEmpty) {
          changed = false
          round += 1
          val snapshot = edges.values.toList
          for (e1 <- snapshot if contradictionProof.isEmpty) {
            val kMid = nodeKey(e1.to)
            for (e2 <- snapshot if contradictionProof.isEmpty && nodeKey(e2.from) == kMid) {
              val kFrom = nodeKey(e1.from)
              val kTo = nodeKey(e2.to)
              val candW = e1.weight + e2.weight
              val isBetter =
                if (kFrom == kTo) candW < 0
                else edges.get((kFrom, kTo)).forall(candW < _.weight)
              if (isBetter) {
                composeEdges(e1, e2).foreach { composed =>
                  val prev = edges.get((kFrom, kTo)).map(_.weight)
                  addEdge(composed.from, composed.to, composed.weight, composed.proof)
                  if (contradictionProof.isDefined || edges.get((kFrom, kTo)).map(_.weight) != prev) {
                    changed = true
                  }
                }
              }
            }
          }
        }
      }
    }

    def deriveFalse(): Option[Term] = boundary {
      contradictionProof.foreach(pf => break(Some(pf)))
      for ((negP, hTerm) <- negatedProps) {
        proveProp(negP).foreach { pfP =>
          val fp = Term.App(hTerm, pfP)
          contradictionProof = Some(fp)
          break(Some(fp))
        }
      }
      None
    }

    def proveProp(propTerm: Term): Option[Term] = {
      // Check definitional reflexivity `x === x` on any type (e.g. `true === true` after `by_cases`)!
      val normP = NbE.normalize(kernelEnv, localCtx, propTerm)
      val (pHead, pArgs) = Term.splitApps(normP)
      if (pHead == Term.Ind("Eq") && pArgs.length == 3 && pArgs(1) == pArgs(2)) {
        return Some(Term.apps(Term.Ctor("Eq", "Refl"), List(pArgs(0), pArgs(1))))
      }
      classifyProp(kernelEnv, localCtx, propTerm).flatMap {
        case ArithAtom.ATrue =>
          Some(Term.Ctor("True", "Intro"))
        case ArithAtom.AFalse =>
          contradictionProof
        case ArithAtom.ALe(a, b) =>
          proveLeTerms(a, b)
        case ArithAtom.ALt(a, b) =>
          val succA = Term.App(Term.Ctor("Nat", "Succ"), a)
          proveLeTerms(succA, b).map(pf => Term.apps(Term.Const("leToBle"), List(succA, b, pf)))
        case ArithAtom.ANatEq(lhs, rhs) =>
          proveNatEq(lhs, rhs)
        case ArithAtom.ABle(a, b, true, flipped) =>
          proveLeTerms(a, b).map { pf =>
            val direct = Term.apps(Term.Const("leToBle"), List(a, b, pf))
            if (flipped) mkBoolEqSym(Term.apps(Term.Const("ble"), List(a, b)), TrueCtor, direct) else direct
          }
        case ArithAtom.ABle(a, b, false, flipped) =>
          val succB = Term.App(Term.Ctor("Nat", "Succ"), b)
          proveLeTerms(succB, a).map { pf =>
            val direct = Term.apps(Term.Const("leSuccToBleFalse"), List(a, b, pf))
            if (flipped) mkBoolEqSym(Term.apps(Term.Const("ble"), List(a, b)), FalseCtor, direct) else direct
          }
        case ArithAtom.ABlt(a, b, true, flipped) =>
          val succA = Term.App(Term.Ctor("Nat", "Succ"), a)
          proveLeTerms(succA, b).map { pf =>
            val direct = Term.apps(Term.Const("leToBle"), List(succA, b, pf))
            if (flipped) mkBoolEqSym(Term.apps(Term.Const("ble"), List(succA, b)), TrueCtor, direct) else direct
          }
        case ArithAtom.ABlt(a, b, false, flipped) =>
          proveLeTerms(b, a).map { pf =>
            val direct = Term.apps(Term.Const("leToBltFalse"), List(a, b, pf))
            if (flipped) mkBoolEqSym(Term.apps(Term.Const("blt"), List(a, b)), FalseCtor, direct) else direct
          }
        case ArithAtom.ABeqTrue(a, b, flipped) =>
          proveNatEq(a, b).map { pf =>
            val direct = Term.apps(Term.Const("eqToBeq"), List(a, b, pf))
            if (flipped) mkBoolEqSym(Term.apps(Term.Const("beq"), List(a, b)), TrueCtor, direct) else direct
          }
      }
    }

    private def proveNatEq(lhs: Term, rhs: Term): Option[Term] = {
      ArithTactic.proveNatEq(kernelEnv, localCtx, lhs, rhs).orElse {
        for {
          leLR <- proveLeTerms(lhs, rhs)
          leRL <- proveLeTerms(rhs, lhs)
        } yield Term.apps(Term.Const("leAntisym"), List(lhs, rhs, leLR, leRL))
      }
    }

    private def proveLeTerms(lhs: Term, rhs: Term): Option[Term] = {
      val (pL, eqL) = ArithTactic.normalizeNat(kernelEnv, localCtx, lhs)
      val (pR, eqR) = ArithTactic.normalizeNat(kernelEnv, localCtx, rhs)
      proveLePolys(pL, pR).map { canonPf =>
        Term.apps(
          Term.Const("leTransport"),
          List(
            ArithTactic.polyTerm(pL),
            lhs,
            ArithTactic.polyTerm(pR),
            rhs,
            ArithTactic.mkSym(lhs, ArithTactic.polyTerm(pL), eqL),
            ArithTactic.mkSym(rhs, ArithTactic.polyTerm(pR), eqR),
            canonPf
          )
        )
      }
    }

    private def proveLePolys(pL: ArithTactic.Poly, pR: ArithTactic.Poly): Option[Term] = {
      val (lOnly, rOnly, common) = polyDiff(pL, pR)
      val corePfOpt: Option[Term] =
        if (lOnly.constVal == 0 && lOnly.monos.isEmpty) {
          Some(Term.App(Term.Const("zeroLe"), ArithTactic.polyTerm(rOnly)))
        } else {
          proveReducedLe(lOnly, rOnly)
        }

      corePfOpt.flatMap { corePf =>
        if (common.constVal == 0 && common.monos.isEmpty) {
          Some(corePf)
        } else {
          val tLO = ArithTactic.polyTerm(lOnly)
          val tRO = ArithTactic.polyTerm(rOnly)
          val tCom = ArithTactic.polyTerm(common)
          val lifted = Term.apps(Term.Const("leAddRight"), List(tLO, tRO, tCom, corePf))
          transportLe(ArithTactic.mkAdd(tLO, tCom), ArithTactic.polyTerm(pL), ArithTactic.mkAdd(tRO, tCom), ArithTactic.polyTerm(pR), lifted)
        }
      }
    }

    private def proveReducedLe(lOnly: ArithTactic.Poly, rOnly: ArithTactic.Poly): Option[Term] = boundary {
      if (lOnly.monos.length <= 1 && rOnly.monos.length <= 1) {
        val u = lOnly.monos.headOption
        val v = rOnly.monos.headOption
        proveNodeBound(u, v, rOnly.constVal - lOnly.constVal, lOnly, rOnly).foreach(pf => break(Some(pf)))
      }

      for (fact <- generalFacts) {
        val (fL, fR, fPf) = (fact.lhs, fact.rhs, fact.proof)
        if (lOnly == fL && rOnly == fR) break(Some(fPf))
        val (lExtra, lPad, _) = polyDiff(lOnly, fL)
        val (rMissing, rPad, _) = polyDiff(fR, rOnly)
        if (lExtra.constVal == 0 && lExtra.monos.isEmpty && rMissing.constVal == 0 && rMissing.monos.isEmpty) {
          val tL = ArithTactic.polyTerm(lOnly)
          val tFL = ArithTactic.polyTerm(fL)
          val tFR = ArithTactic.polyTerm(fR)
          val tR = ArithTactic.polyTerm(rOnly)
          val step1Opt =
            if (lPad.constVal == 0 && lPad.monos.isEmpty) Some(Term.App(Term.Const("leRefl"), tL))
            else {
              val raw = Term.apps(Term.Const("leAddIntroRight"), List(tL, ArithTactic.polyTerm(lPad)))
              transportLe(tL, tL, ArithTactic.mkAdd(tL, ArithTactic.polyTerm(lPad)), tFL, raw)
            }
          val step2Opt =
            if (rPad.constVal == 0 && rPad.monos.isEmpty) Some(Term.App(Term.Const("leRefl"), tFR))
            else {
              val raw = Term.apps(Term.Const("leAddIntroRight"), List(tFR, ArithTactic.polyTerm(rPad)))
              transportLe(tFR, tFR, ArithTactic.mkAdd(tFR, ArithTactic.polyTerm(rPad)), tR, raw)
            }
          (step1Opt, step2Opt) match {
            case (Some(s1), Some(s2)) =>
              val p12 = Term.apps(Term.Const("leTrans"), List(tL, tFL, tFR, s1, fPf))
              break(Some(Term.apps(Term.Const("leTrans"), List(tL, tFR, tR, p12, s2))))
            case _ => ()
          }
        }
      }

      if (lOnly.monos.nonEmpty) {
        proveAdditiveMatching(lOnly, rOnly).foreach(pf => break(Some(pf)))
      }

      None
    }

    private def proveNodeBound(
      u: Option[List[Term]],
      v: Option[List[Term]],
      allowedSlack: Int,
      targetL: ArithTactic.Poly,
      targetR: ArithTactic.Poly
    ): Option[Term] = {
      val kU = nodeKey(u)
      val kV = nodeKey(v)
      if (kU == kV) {
        if (allowedSlack >= 0) {
          val tL = ArithTactic.polyTerm(targetL)
          val raw = Term.apps(Term.Const("leAddIntroRight"), List(tL, ArithTactic.natLit(allowedSlack)))
          return transportLe(tL, tL, ArithTactic.mkAdd(tL, ArithTactic.natLit(allowedSlack)), ArithTactic.polyTerm(targetR), raw)
        } else return None
      }
      edges.get((kU, kV)).flatMap { edge =>
        if (edge.weight <= allowedSlack) {
          val slackDiff = allowedSlack - edge.weight
          val (eL, eR) = edgeEndpoints(u, v, edge.weight)
          val shiftBoth = math.max(0, targetL.constVal - eL.constVal)
          val liftedL = polyAdd(eL, ArithTactic.Poly(shiftBoth, Nil))
          val liftedR = polyAdd(eR, ArithTactic.Poly(shiftBoth, Nil))
          val liftedPfOpt =
            if (shiftBoth == 0) Some(edge.proof)
            else {
              val raw = Term.apps(Term.Const("leAddRight"), List(ArithTactic.polyTerm(eL), ArithTactic.polyTerm(eR), ArithTactic.natLit(shiftBoth), edge.proof))
              transportLe(
                ArithTactic.mkAdd(ArithTactic.polyTerm(eL), ArithTactic.natLit(shiftBoth)),
                ArithTactic.polyTerm(liftedL),
                ArithTactic.mkAdd(ArithTactic.polyTerm(eR), ArithTactic.natLit(shiftBoth)),
                ArithTactic.polyTerm(liftedR),
                raw
              )
            }
          liftedPfOpt.flatMap { liftedPf =>
            if (slackDiff == 0) {
              transportLe(ArithTactic.polyTerm(liftedL), ArithTactic.polyTerm(targetL), ArithTactic.polyTerm(liftedR), ArithTactic.polyTerm(targetR), liftedPf)
            } else {
              val tLR = ArithTactic.polyTerm(liftedR)
              val padPf = Term.apps(Term.Const("leAddIntroRight"), List(tLR, ArithTactic.natLit(slackDiff)))
              val combined = Term.apps(
                Term.Const("leTrans"),
                List(ArithTactic.polyTerm(liftedL), tLR, ArithTactic.mkAdd(tLR, ArithTactic.natLit(slackDiff)), liftedPf, padPf)
              )
              transportLe(
                ArithTactic.polyTerm(liftedL),
                ArithTactic.polyTerm(targetL),
                ArithTactic.mkAdd(tLR, ArithTactic.natLit(slackDiff)),
                ArithTactic.polyTerm(targetR),
                combined
              )
            }
          }
        } else None
      }
    }

    private def proveAdditiveMatching(lOnly: ArithTactic.Poly, rOnly: ArithTactic.Poly): Option[Term] = boundary {
      val remainingR = mutable.ListBuffer.from(rOnly.monos)
      val matchedPairs = mutable.ListBuffer.empty[(ArithTactic.Poly, ArithTactic.Poly, Term)]
      var totalWeight = 0

      for (u <- lOnly.monos) {
        var bestIdx = -2
        var bestEdgeOpt: Option[DiffEdge] = None

        for ((v, idx) <- remainingR.zipWithIndex) {
          edges.get((nodeKey(Some(u)), nodeKey(Some(v)))).foreach { e =>
            if (bestEdgeOpt.forall(e.weight < _.weight)) {
              bestEdgeOpt = Some(e)
              bestIdx = idx
            }
          }
        }
        edges.get((nodeKey(Some(u)), nodeKey(None))).foreach { e =>
          if (bestEdgeOpt.forall(e.weight < _.weight)) {
            bestEdgeOpt = Some(e)
            bestIdx = -1
          }
        }

        bestEdgeOpt match {
          case None => break(None)
          case Some(e) =>
            if (bestIdx >= 0) remainingR.remove(bestIdx)
            val (eL, eR) = edgeEndpoints(e.from, e.to, e.weight)
            matchedPairs += ((eL, eR, e.proof))
            totalWeight += e.weight
        }
      }

      if (totalWeight > rOnly.constVal - lOnly.constVal) break(None)

      var accL = matchedPairs.head._1
      var accR = matchedPairs.head._2
      var accPf = matchedPairs.head._3
      for ((nL, nR, nPf) <- matchedPairs.tail) {
        val sumL = polyAdd(accL, nL)
        val sumR = polyAdd(accR, nR)
        val raw = Term.apps(
          Term.Const("leAddBoth"),
          List(ArithTactic.polyTerm(accL), ArithTactic.polyTerm(accR), ArithTactic.polyTerm(nL), ArithTactic.polyTerm(nR), accPf, nPf)
        )
        transportLe(
          ArithTactic.mkAdd(ArithTactic.polyTerm(accL), ArithTactic.polyTerm(nL)),
          ArithTactic.polyTerm(sumL),
          ArithTactic.mkAdd(ArithTactic.polyTerm(accR), ArithTactic.polyTerm(nR)),
          ArithTactic.polyTerm(sumR),
          raw
        ) match {
          case Some(normPf) =>
            accL = sumL; accR = sumR; accPf = normPf
          case None =>
            break(None)
        }
      }

      val shiftBoth = math.max(0, lOnly.constVal - accL.constVal)
      val liftedL = polyAdd(accL, ArithTactic.Poly(shiftBoth, Nil))
      val liftedR = polyAdd(accR, ArithTactic.Poly(shiftBoth, Nil))
      val liftedPf =
        if (shiftBoth == 0) accPf
        else {
          val raw = Term.apps(Term.Const("leAddRight"), List(ArithTactic.polyTerm(accL), ArithTactic.polyTerm(accR), ArithTactic.natLit(shiftBoth), accPf))
          transportLe(
            ArithTactic.mkAdd(ArithTactic.polyTerm(accL), ArithTactic.natLit(shiftBoth)),
            ArithTactic.polyTerm(liftedL),
            ArithTactic.mkAdd(ArithTactic.polyTerm(accR), ArithTactic.natLit(shiftBoth)),
            ArithTactic.polyTerm(liftedR),
            raw
          ) match {
            case Some(p) => p
            case None    => break(None)
          }
        }

      val extraConstL = liftedL.constVal - lOnly.constVal
      val (alignedL, alignedR, alignedPf) =
        if (extraConstL > 0) {
          val tL = ArithTactic.polyTerm(lOnly)
          val tLL = ArithTactic.polyTerm(liftedL)
          val tLR = ArithTactic.polyTerm(liftedR)
          val intro = Term.apps(Term.Const("leAddIntroRight"), List(tL, ArithTactic.natLit(extraConstL)))
          val step1 = transportLe(tL, tL, ArithTactic.mkAdd(tL, ArithTactic.natLit(extraConstL)), tLL, intro) match {
            case Some(p) => p
            case None    => break(None)
          }
          (lOnly, liftedR, Term.apps(Term.Const("leTrans"), List(tL, tLL, tLR, step1, liftedPf)))
        } else {
          (liftedL, liftedR, liftedPf)
        }

      val (rMissing, rExtra, _) = polyDiff(alignedR, rOnly)
      if (rMissing.constVal > 0 || rMissing.monos.nonEmpty) break(None)
      if (rExtra.constVal == 0 && rExtra.monos.isEmpty) {
        transportLe(ArithTactic.polyTerm(alignedL), ArithTactic.polyTerm(lOnly), ArithTactic.polyTerm(alignedR), ArithTactic.polyTerm(rOnly), alignedPf)
      } else {
        val tAR = ArithTactic.polyTerm(alignedR)
        val tExtra = ArithTactic.polyTerm(rExtra)
        val pad = Term.apps(Term.Const("leAddIntroRight"), List(tAR, tExtra))
        val combined = Term.apps(Term.Const("leTrans"), List(ArithTactic.polyTerm(alignedL), tAR, ArithTactic.mkAdd(tAR, tExtra), alignedPf, pad))
        transportLe(ArithTactic.polyTerm(alignedL), ArithTactic.polyTerm(lOnly), ArithTactic.mkAdd(tAR, tExtra), ArithTactic.polyTerm(rOnly), combined)
      }
    }
  }
}
