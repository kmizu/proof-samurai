package samurai.tactic

import samurai.elab.ElabEnv
import samurai.kernel.*
import samurai.util.{Diagnostic, Span}

/**
 * Sound, proof-producing commutative semiring solver (`arith` / `ring`) for `Nat` equalities.
 *
 * Normalizes both sides of `lhs === rhs` (over `0`, `Nat.Succ`, `+`, `*`, and arbitrary `Nat` atoms)
 * into canonical sorted sums of sorted products, synthesizing an explicit, 100% axiom-free
 * kernel proof term verified by `samurai.kernel.TypeChecker`.
 */
object ArithTactic {

  private val NatType: Term = Term.Ind("Nat")
  private val AddConst: Term = Term.Const("add")
  private val MulConst: Term = Term.Const("mul")

  private final case class Poly(constVal: Int, monos: List[List[Term]])

  private val RequiredLemmas: List[String] = List(
    "addZeroRight", "addComm", "addAssoc",
    "mulZeroRight", "mulOneLeft", "mulOneRight", "mulComm", "mulAssoc", "mulDistribRight"
  )

  def solve(env: ElabEnv, state: ProofState, span: Span): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val missing = RequiredLemmas.filterNot(env.kernelEnv.contains)
    if (missing.nonEmpty) {
      return Left(
        Diagnostic(
          Diagnostic.Severity.Error,
          "T060",
          s"'arith' requires Nat algebra lemmas (import Nat.*); missing: ${missing.mkString(", ")}",
          span
        )
      )
    }

    Tactics.extractEqGoal(env.kernelEnv, goal.localCtx, goal.targetType) match {
      case Some((eqType, lhsRaw, rhsRaw)) =>
        val eqTypeNorm = NbE.normalize(env.kernelEnv, goal.localCtx, eqType)
        if (eqTypeNorm != NatType) {
          return Left(
            Diagnostic(
              Diagnostic.Severity.Error,
              "T061",
              s"'arith' applies to Nat equalities, found equality on '${Pretty.show(eqTypeNorm, goal.localCtx.names)}'",
              span
            )
          )
        }
        val (polyL, proofL) = normalizeNat(env.kernelEnv, goal.localCtx, lhsRaw)
        val (polyR, proofR) = normalizeNat(env.kernelEnv, goal.localCtx, rhsRaw)
        if (polyL == polyR) {
          val canon = polyTerm(polyL)
          val fullProof = mkTrans(lhsRaw, canon, rhsRaw, proofL, mkSym(rhsRaw, canon, proofR))
          Right((env, state.replaceHead(Nil, _ => fullProof, state.nextGoalId)))
        } else {
          val canonL = Pretty.show(polyTerm(polyL), goal.localCtx.names)
          val canonR = Pretty.show(polyTerm(polyR), goal.localCtx.names)
          Left(
            Diagnostic(
              Diagnostic.Severity.Error,
              "T062",
              s"'arith' could not prove equality:\n  left normal form:  $canonL\n  right normal form: $canonR",
              span
            )
          )
        }

      case None =>
        Left(Diagnostic(Diagnostic.Severity.Error, "T061", "'arith' requires a Nat equality goal ('===')", span))
    }
  }

  // ===========================================================================
  // Core Proof Combinators (100% Pure Kernel Terms)
  // ===========================================================================

  private def natLit(n: Int): Term =
    if (n <= 0) Term.Ctor("Nat", "Zero")
    else Term.App(Term.Ctor("Nat", "Succ"), natLit(n - 1))

  private def mkAdd(a: Term, b: Term): Term = Term.apps(AddConst, List(a, b))
  private def mkMul(a: Term, b: Term): Term = Term.apps(MulConst, List(a, b))

  private def mkRefl(t: Term): Term =
    Term.apps(Term.Ctor("Eq", "Refl"), List(NatType, t))

  private def mkSym(a: Term, b: Term, proofAB: Term): Term = {
    val a1 = Term.shift(a, 1)
    val a2 = Term.shift(a, 2)
    val motive = Term.Lam(
      "_y",
      NatType,
      Term.Lam(
        "_q",
        Term.apps(Term.Ind("Eq"), List(NatType, a1, Term.Var(0))),
        Term.apps(Term.Ind("Eq"), List(NatType, Term.Var(1), a2))
      )
    )
    Term.Match("Eq", List(NatType, a), motive, proofAB, List(MatchBranch("Refl", Nil, mkRefl(a))))
  }

  private def mkTrans(a: Term, b: Term, c: Term, proofAB: Term, proofBC: Term): Term = {
    val b1 = Term.shift(b, 1)
    val a2 = Term.shift(a, 2)
    val motive = Term.Lam(
      "_y",
      NatType,
      Term.Lam(
        "_q",
        Term.apps(Term.Ind("Eq"), List(NatType, b1, Term.Var(0))),
        Term.apps(Term.Ind("Eq"), List(NatType, a2, Term.Var(1)))
      )
    )
    Term.Match("Eq", List(NatType, b), motive, proofBC, List(MatchBranch("Refl", Nil, proofAB)))
  }

  private def mkCongrBinOp(op: Term, a1: Term, a2: Term, b1: Term, b2: Term, pA: Term, pB: Term): Term = {
    val lhs = Term.apps(op, List(a1, b1))
    val mid = Term.apps(op, List(a2, b1))
    val rhs = Term.apps(op, List(a2, b2))

    val mLeft = Term.Lam(
      "_y",
      NatType,
      Term.Lam(
        "_q",
        Term.apps(Term.Ind("Eq"), List(NatType, Term.shift(a1, 1), Term.Var(0))),
        Term.apps(
          Term.Ind("Eq"),
          List(NatType, Term.shift(lhs, 2), Term.apps(op, List(Term.Var(1), Term.shift(b1, 2))))
        )
      )
    )
    val stepLeft = Term.Match("Eq", List(NatType, a1), mLeft, pA, List(MatchBranch("Refl", Nil, mkRefl(lhs))))

    val mRight = Term.Lam(
      "_y",
      NatType,
      Term.Lam(
        "_q",
        Term.apps(Term.Ind("Eq"), List(NatType, Term.shift(b1, 1), Term.Var(0))),
        Term.apps(
          Term.Ind("Eq"),
          List(NatType, Term.shift(mid, 2), Term.apps(op, List(Term.shift(a2, 2), Term.Var(1))))
        )
      )
    )
    val stepRight = Term.Match("Eq", List(NatType, b1), mRight, pB, List(MatchBranch("Refl", Nil, mkRefl(mid))))

    mkTrans(lhs, mid, rhs, stepLeft, stepRight)
  }

  private def mkCongrAdd(a1: Term, a2: Term, b1: Term, b2: Term, pA: Term, pB: Term): Term =
    mkCongrBinOp(AddConst, a1, a2, b1, b2, pA, pB)

  private def mkCongrMul(a1: Term, a2: Term, b1: Term, b2: Term, pA: Term, pB: Term): Term =
    mkCongrBinOp(MulConst, a1, a2, b1, b2, pA, pB)

  private def lemAddZeroRight(x: Term): Term = Term.App(Term.Const("addZeroRight"), x)
  private def lemAddComm(x: Term, y: Term): Term = Term.apps(Term.Const("addComm"), List(x, y))
  private def lemAddAssoc(x: Term, y: Term, z: Term): Term = Term.apps(Term.Const("addAssoc"), List(x, y, z))
  private def lemMulZeroRight(x: Term): Term = Term.App(Term.Const("mulZeroRight"), x)
  private def lemMulOneLeft(x: Term): Term = Term.App(Term.Const("mulOneLeft"), x)
  private def lemMulOneRight(x: Term): Term = Term.App(Term.Const("mulOneRight"), x)
  private def lemMulComm(x: Term, y: Term): Term = Term.apps(Term.Const("mulComm"), List(x, y))
  private def lemMulAssoc(x: Term, y: Term, z: Term): Term = Term.apps(Term.Const("mulAssoc"), List(x, y, z))
  private def lemMulDistribRight(a: Term, b: Term, c: Term): Term =
    Term.apps(Term.Const("mulDistribRight"), List(a, b, c))

  /** Prove `a * (b + c) === a * b + a * c` from `mulComm` and `mulDistribRight`. */
  private def lemMulDistribLeft(a: Term, b: Term, c: Term): Term = {
    val lhs = mkMul(a, mkAdd(b, c))
    val m1 = mkMul(mkAdd(b, c), a)
    val m2 = mkAdd(mkMul(b, a), mkMul(c, a))
    val rhs = mkAdd(mkMul(a, b), mkMul(a, c))
    val p1 = lemMulComm(a, mkAdd(b, c))
    val p2 = lemMulDistribRight(b, c, a)
    val p3 = mkCongrAdd(mkMul(b, a), mkMul(a, b), mkMul(c, a), mkMul(a, c), lemMulComm(b, a), lemMulComm(c, a))
    mkTrans(lhs, m1, rhs, p1, mkTrans(m1, m2, rhs, p2, p3))
  }

  // ===========================================================================
  // Canonical Polynomial Representation & Ordering
  // ===========================================================================

  private def atomKey(t: Term): String = Pretty.show(t)

  private def compareAtoms(a: Term, b: Term): Int =
    atomKey(a).compareTo(atomKey(b))

  private def compareMonos(m1: List[Term], m2: List[Term]): Int = (m1, m2) match {
    case (Nil, Nil)       => 0
    case (Nil, _)         => -1
    case (_, Nil)         => 1
    case (h1 :: t1, h2 :: t2) =>
      val c = compareAtoms(h1, h2)
      if (c != 0) c else compareMonos(t1, t2)
  }

  private def monoTerm(atoms: List[Term]): Term = atoms match {
    case Nil          => natLit(1)
    case single :: Nil => single
    case head :: tail => mkMul(head, monoTerm(tail))
  }

  private def sumMonosTerm(monos: List[List[Term]]): Term = monos match {
    case Nil           => natLit(0)
    case single :: Nil => monoTerm(single)
    case head :: tail  => mkAdd(monoTerm(head), sumMonosTerm(tail))
  }

  private def polyTerm(p: Poly): Term = (p.constVal, p.monos) match {
    case (k, Nil) => natLit(k)
    case (0, ms)  => sumMonosTerm(ms)
    case (k, ms)  => mkAdd(natLit(k), sumMonosTerm(ms))
  }

  // ===========================================================================
  // Proof-Producing Semiring Operations
  // ===========================================================================

  /** Prove `atom * monoTerm(sorted) === monoTerm(result)` for non-empty `sorted`. */
  private def insertAtom(atom: Term, sorted: List[Term]): (List[Term], Term) = sorted match {
    case Nil => (List(atom), lemMulOneRight(atom))
    case head :: tail =>
      if (compareAtoms(atom, head) <= 0) {
        (atom :: sorted, mkRefl(mkMul(atom, monoTerm(sorted))))
      } else {
        tail match {
          case Nil =>
            (List(head, atom), lemMulComm(atom, head))
          case _ =>
            val tTail = monoTerm(tail)
            val lhs = mkMul(atom, mkMul(head, tTail))
            val m1 = mkMul(mkMul(atom, head), tTail)
            val m2 = mkMul(mkMul(head, atom), tTail)
            val m3 = mkMul(head, mkMul(atom, tTail))
            val (insertedTail, pTail) = insertAtom(atom, tail)
            val rhs = mkMul(head, monoTerm(insertedTail))
            val p1 = mkSym(m1, lhs, lemMulAssoc(atom, head, tTail))
            val p2 = mkCongrMul(mkMul(atom, head), mkMul(head, atom), tTail, tTail, lemMulComm(atom, head), mkRefl(tTail))
            val p3 = lemMulAssoc(head, atom, tTail)
            val p4 = mkCongrMul(head, head, mkMul(atom, tTail), monoTerm(insertedTail), mkRefl(head), pTail)
            val pf = mkTrans(lhs, m1, rhs, p1, mkTrans(m1, m2, rhs, p2, mkTrans(m2, m3, rhs, p3, p4)))
            (head :: insertedTail, pf)
        }
      }
  }

  /** Prove `monoTerm(m1) * monoTerm(m2) === monoTerm(merged)` for non-empty `m1, m2`. */
  private def mergeMonosMul(m1: List[Term], m2: List[Term]): (List[Term], Term) = m1 match {
    case Nil          => (m2, lemMulOneLeft(monoTerm(m2)))
    case single :: Nil => insertAtom(single, m2)
    case head :: tail =>
      val tTail = monoTerm(tail)
      val t2 = monoTerm(m2)
      val lhs = mkMul(mkMul(head, tTail), t2)
      val mMid1 = mkMul(head, mkMul(tTail, t2))
      val (mergedTail, pTail) = mergeMonosMul(tail, m2)
      val mMid2 = mkMul(head, monoTerm(mergedTail))
      val (finalMono, pIns) = insertAtom(head, mergedTail)
      val rhs = monoTerm(finalMono)
      val p1 = lemMulAssoc(head, tTail, t2)
      val p2 = mkCongrMul(head, head, mkMul(tTail, t2), monoTerm(mergedTail), mkRefl(head), pTail)
      val pf = mkTrans(lhs, mMid1, rhs, p1, mkTrans(mMid1, mMid2, rhs, p2, pIns))
      (finalMono, pf)
  }

  /** Prove `monoTerm(mono) + sumMonosTerm(sorted) === sumMonosTerm(inserted)` for non-empty `sorted`. */
  private def insertMonoAdd(mono: List[Term], sorted: List[List[Term]]): (List[List[Term]], Term) = sorted match {
    case Nil => (List(mono), lemAddZeroRight(monoTerm(mono)))
    case head :: tail =>
      val tM = monoTerm(mono)
      val tH = monoTerm(head)
      if (compareMonos(mono, head) <= 0) {
        (mono :: sorted, mkRefl(mkAdd(tM, sumMonosTerm(sorted))))
      } else {
        tail match {
          case Nil =>
            (List(head, mono), lemAddComm(tM, tH))
          case _ =>
            val tTail = sumMonosTerm(tail)
            val lhs = mkAdd(tM, mkAdd(tH, tTail))
            val m1 = mkAdd(mkAdd(tM, tH), tTail)
            val m2 = mkAdd(mkAdd(tH, tM), tTail)
            val m3 = mkAdd(tH, mkAdd(tM, tTail))
            val (insTail, pTail) = insertMonoAdd(mono, tail)
            val rhs = mkAdd(tH, sumMonosTerm(insTail))
            val p1 = mkSym(m1, lhs, lemAddAssoc(tM, tH, tTail))
            val p2 = mkCongrAdd(mkAdd(tM, tH), mkAdd(tH, tM), tTail, tTail, lemAddComm(tM, tH), mkRefl(tTail))
            val p3 = lemAddAssoc(tH, tM, tTail)
            val p4 = mkCongrAdd(tH, tH, mkAdd(tM, tTail), sumMonosTerm(insTail), mkRefl(tH), pTail)
            val pf = mkTrans(lhs, m1, rhs, p1, mkTrans(m1, m2, rhs, p2, mkTrans(m2, m3, rhs, p3, p4)))
            (head :: insTail, pf)
        }
      }
  }

  /** Prove `sumMonosTerm(ms1) + sumMonosTerm(ms2) === sumMonosTerm(merged)`. */
  private def mergeMonoSums(ms1: List[List[Term]], ms2: List[List[Term]]): (List[List[Term]], Term) = (ms1, ms2) match {
    case (Nil, _) => (ms2, mkRefl(sumMonosTerm(ms2)))
    case (_, Nil) => (ms1, lemAddZeroRight(sumMonosTerm(ms1)))
    case (single :: Nil, _) => insertMonoAdd(single, ms2)
    case (head :: tail, _) =>
      val tH = monoTerm(head)
      val tTail = sumMonosTerm(tail)
      val t2 = sumMonosTerm(ms2)
      val lhs = mkAdd(mkAdd(tH, tTail), t2)
      val m1 = mkAdd(tH, mkAdd(tTail, t2))
      val (mergedTail, pTail) = mergeMonoSums(tail, ms2)
      val m2 = mkAdd(tH, sumMonosTerm(mergedTail))
      val (finalSum, pIns) = insertMonoAdd(head, mergedTail)
      val rhs = sumMonosTerm(finalSum)
      val p1 = lemAddAssoc(tH, tTail, t2)
      val p2 = mkCongrAdd(tH, tH, mkAdd(tTail, t2), sumMonosTerm(mergedTail), mkRefl(tH), pTail)
      val pf = mkTrans(lhs, m1, rhs, p1, mkTrans(m1, m2, rhs, p2, pIns))
      (finalSum, pf)
  }

  /** Prove `polyTerm(p1) + polyTerm(p2) === polyTerm(result)`. */
  private def addPolys(p1: Poly, p2: Poly): (Poly, Term) = {
    val t1 = polyTerm(p1)
    val t2 = polyTerm(p2)
    (p1, p2) match {
      case (Poly(0, Nil), _) =>
        (p2, mkRefl(t2)) // 0 + t2 === t2 definitionally
      case (_, Poly(0, Nil)) =>
        (p1, lemAddZeroRight(t1))
      case (Poly(k1, Nil), Poly(k2, Nil)) =>
        (Poly(k1 + k2, Nil), mkRefl(natLit(k1 + k2))) // natLit(k1) + natLit(k2) === natLit(k1 + k2) definitionally
      case (Poly(k1, Nil), Poly(0, ms2)) =>
        (Poly(k1, ms2), mkRefl(mkAdd(natLit(k1), sumMonosTerm(ms2))))
      case (Poly(0, ms1), Poly(k2, Nil)) =>
        (Poly(k2, ms1), lemAddComm(sumMonosTerm(ms1), natLit(k2)))
      case (Poly(k1, Nil), Poly(k2, ms2)) =>
        val s2 = sumMonosTerm(ms2)
        val lhs = mkAdd(natLit(k1), mkAdd(natLit(k2), s2))
        val m1 = mkAdd(mkAdd(natLit(k1), natLit(k2)), s2)
        val rhs = mkAdd(natLit(k1 + k2), s2)
        val pAssocRev = mkSym(m1, lhs, lemAddAssoc(natLit(k1), natLit(k2), s2))
        (Poly(k1 + k2, ms2), pAssocRev)
      case (Poly(k1, ms1), Poly(k2, Nil)) =>
        val (res, pSwapped) = addPolys(p2, p1)
        (res, mkTrans(mkAdd(t1, t2), mkAdd(t2, t1), polyTerm(res), lemAddComm(t1, t2), pSwapped))
      case (Poly(0, ms1), Poly(0, ms2)) =>
        val (merged, pM) = mergeMonoSums(ms1, ms2)
        (Poly(0, merged), pM)
      case (Poly(k1, ms1), Poly(0, ms2)) =>
        val s1 = sumMonosTerm(ms1)
        val s2 = sumMonosTerm(ms2)
        val lhs = mkAdd(mkAdd(natLit(k1), s1), s2)
        val m1 = mkAdd(natLit(k1), mkAdd(s1, s2))
        val (merged, pM) = mergeMonoSums(ms1, ms2)
        val rhs = mkAdd(natLit(k1), sumMonosTerm(merged))
        val p1 = lemAddAssoc(natLit(k1), s1, s2)
        val p2 = mkCongrAdd(natLit(k1), natLit(k1), mkAdd(s1, s2), sumMonosTerm(merged), mkRefl(natLit(k1)), pM)
        (Poly(k1, merged), mkTrans(lhs, m1, rhs, p1, p2))
      case (Poly(0, ms1), Poly(k2, ms2)) =>
        val (res, pSwapped) = addPolys(p2, p1)
        (res, mkTrans(mkAdd(t1, t2), mkAdd(t2, t1), polyTerm(res), lemAddComm(t1, t2), pSwapped))
      case (Poly(k1, ms1), Poly(k2, ms2)) =>
        // (k1 + s1) + (k2 + s2) === k1 + (s1 + (k2 + s2)) === k1 + ((k2 + s2) + s1) === ...
        val s1 = sumMonosTerm(ms1)
        val s2 = sumMonosTerm(ms2)
        val k1T = natLit(k1)
        val k2T = natLit(k2)
        val lhs = mkAdd(mkAdd(k1T, s1), mkAdd(k2T, s2))
        val m1 = mkAdd(k1T, mkAdd(s1, mkAdd(k2T, s2)))
        val (innerPoly, pInner) = addPolys(Poly(0, ms1), Poly(k2, ms2))
        val m2 = mkAdd(k1T, polyTerm(innerPoly))
        val (finalPoly, pOuter) = addPolys(Poly(k1, Nil), innerPoly)
        val rhs = polyTerm(finalPoly)
        val step1 = lemAddAssoc(k1T, s1, mkAdd(k2T, s2))
        val step2 = mkCongrAdd(k1T, k1T, mkAdd(s1, mkAdd(k2T, s2)), polyTerm(innerPoly), mkRefl(k1T), pInner)
        (finalPoly, mkTrans(lhs, m1, rhs, step1, mkTrans(m1, m2, rhs, step2, pOuter)))
    }
  }

  /** Prove `natLit(k) * polyTerm(p) === polyTerm(scaled)`. */
  private def scalePolyByConst(k: Int, p: Poly): (Poly, Term) = {
    val tP = polyTerm(p)
    if (k <= 0) {
      (Poly(0, Nil), mkRefl(natLit(0))) // 0 * tP === 0 definitionally
    } else if (k == 1) {
      (p, lemMulOneLeft(tP))
    } else {
      // Succ(k-1) * tP === tP + (k-1) * tP definitionally!
      val (restPoly, pRest) = scalePolyByConst(k - 1, p)
      val m1 = mkAdd(tP, mkMul(natLit(k - 1), tP))
      val m2 = mkAdd(tP, polyTerm(restPoly))
      val (finalPoly, pAdd) = addPolys(p, restPoly)
      val step1 = mkCongrAdd(tP, tP, mkMul(natLit(k - 1), tP), polyTerm(restPoly), mkRefl(tP), pRest)
      (finalPoly, mkTrans(m1, m2, polyTerm(finalPoly), step1, pAdd))
    }
  }

  /** Prove `monoTerm(m) * polyTerm(p) === polyTerm(res)`. */
  private def mulMonoByPoly(m: List[Term], p: Poly): (Poly, Term) = {
    val tM = monoTerm(m)
    p match {
      case Poly(0, Nil) =>
        (Poly(0, Nil), lemMulZeroRight(tM))
      case Poly(k, Nil) =>
        val lhs = mkMul(tM, natLit(k))
        val m1 = mkMul(natLit(k), tM)
        val (scaled, pScale) = scalePolyByConst(k, Poly(0, List(m)))
        (scaled, mkTrans(lhs, m1, polyTerm(scaled), lemMulComm(tM, natLit(k)), pScale))
      case Poly(0, single :: Nil) =>
        val (merged, pMul) = mergeMonosMul(m, single)
        (Poly(0, List(merged)), pMul)
      case Poly(0, head :: tail) =>
        val tH = monoTerm(head)
        val tTail = sumMonosTerm(tail)
        val lhs = mkMul(tM, mkAdd(tH, tTail))
        val m1 = mkAdd(mkMul(tM, tH), mkMul(tM, tTail))
        val (pHead, pfHead) = mergeMonosMul(m, head)
        val (pTail, pfTail) = mulMonoByPoly(m, Poly(0, tail))
        val m2 = mkAdd(monoTerm(pHead), polyTerm(pTail))
        val (finalPoly, pfAdd) = addPolys(Poly(0, List(pHead)), pTail)
        val s1 = lemMulDistribLeft(tM, tH, tTail)
        val s2 = mkCongrAdd(mkMul(tM, tH), monoTerm(pHead), mkMul(tM, tTail), polyTerm(pTail), pfHead, pfTail)
        (finalPoly, mkTrans(lhs, m1, polyTerm(finalPoly), s1, mkTrans(m1, m2, polyTerm(finalPoly), s2, pfAdd)))
      case Poly(k, ms) =>
        val kT = natLit(k)
        val sT = sumMonosTerm(ms)
        val lhs = mkMul(tM, mkAdd(kT, sT))
        val m1 = mkAdd(mkMul(tM, kT), mkMul(tM, sT))
        val (pLeft, pfLeft) = mulMonoByPoly(m, Poly(k, Nil))
        val (pRight, pfRight) = mulMonoByPoly(m, Poly(0, ms))
        val m2 = mkAdd(polyTerm(pLeft), polyTerm(pRight))
        val (finalPoly, pfAdd) = addPolys(pLeft, pRight)
        val s1 = lemMulDistribLeft(tM, kT, sT)
        val s2 = mkCongrAdd(mkMul(tM, kT), polyTerm(pLeft), mkMul(tM, sT), polyTerm(pRight), pfLeft, pfRight)
        (finalPoly, mkTrans(lhs, m1, polyTerm(finalPoly), s1, mkTrans(m1, m2, polyTerm(finalPoly), s2, pfAdd)))
    }
  }

  /** Prove `polyTerm(p1) * polyTerm(p2) === polyTerm(res)`. */
  private def mulPolys(p1: Poly, p2: Poly): (Poly, Term) = {
    val t2 = polyTerm(p2)
    p1 match {
      case Poly(0, Nil) =>
        (Poly(0, Nil), mkRefl(natLit(0)))
      case Poly(k, Nil) =>
        scalePolyByConst(k, p2)
      case Poly(0, single :: Nil) =>
        mulMonoByPoly(single, p2)
      case Poly(0, head :: tail) =>
        val tH = monoTerm(head)
        val tTail = sumMonosTerm(tail)
        val lhs = mkMul(mkAdd(tH, tTail), t2)
        val m1 = mkAdd(mkMul(tH, t2), mkMul(tTail, t2))
        val (pHead, pfHead) = mulMonoByPoly(head, p2)
        val (pTail, pfTail) = mulPolys(Poly(0, tail), p2)
        val m2 = mkAdd(polyTerm(pHead), polyTerm(pTail))
        val (finalPoly, pfAdd) = addPolys(pHead, pTail)
        val s1 = lemMulDistribRight(tH, tTail, t2)
        val s2 = mkCongrAdd(mkMul(tH, t2), polyTerm(pHead), mkMul(tTail, t2), polyTerm(pTail), pfHead, pfTail)
        (finalPoly, mkTrans(lhs, m1, polyTerm(finalPoly), s1, mkTrans(m1, m2, polyTerm(finalPoly), s2, pfAdd)))
      case Poly(k, ms) =>
        val kT = natLit(k)
        val sT = sumMonosTerm(ms)
        val lhs = mkMul(mkAdd(kT, sT), t2)
        val m1 = mkAdd(mkMul(kT, t2), mkMul(sT, t2))
        val (pLeft, pfLeft) = scalePolyByConst(k, p2)
        val (pRight, pfRight) = mulPolys(Poly(0, ms), p2)
        val m2 = mkAdd(polyTerm(pLeft), polyTerm(pRight))
        val (finalPoly, pfAdd) = addPolys(pLeft, pRight)
        val s1 = lemMulDistribRight(kT, sT, t2)
        val s2 = mkCongrAdd(mkMul(kT, t2), polyTerm(pLeft), mkMul(sT, t2), polyTerm(pRight), pfLeft, pfRight)
        (finalPoly, mkTrans(lhs, m1, polyTerm(finalPoly), s1, mkTrans(m1, m2, polyTerm(finalPoly), s2, pfAdd)))
    }
  }

  // ===========================================================================
  // Top-Level Recursive Normalizer from Core Nat Terms
  // ===========================================================================

  private def isAddHead(head: Term): Boolean = head match {
    case Term.Const("add")        => true
    case Term.Fix("add", _, _, _) => true
    case _                        => false
  }

  private def isMulHead(head: Term): Boolean = head match {
    case Term.Const("mul")        => true
    case Term.Fix("mul", _, _, _) => true
    case _                        => false
  }

  private def normalizeNat(kernelEnv: KernelEnv, localCtx: LocalCtx, term: Term): (Poly, Term) = {
    val norm = NbE.normalize(kernelEnv, localCtx, term)
    val (p, pfNorm) = normalizeNormNat(norm)
    // Because `term` and `norm` are definitionally equal, `pfNorm` already has type `term === polyTerm(p)`!
    (p, pfNorm)
  }

  private def normalizeNormNat(term: Term): (Poly, Term) = term match {
    case Term.Ctor("Nat", "Zero") =>
      (Poly(0, Nil), mkRefl(natLit(0)))

    case Term.App(Term.Ctor("Nat", "Succ"), inner) =>
      // Nat.Succ(inner) === add(1, inner) definitionally!
      val (pInner, pfInner) = normalizeNormNat(inner)
      val m1 = mkAdd(natLit(1), polyTerm(pInner))
      val (pSum, pfSum) = addPolys(Poly(1, Nil), pInner)
      val step1 = mkCongrAdd(natLit(1), natLit(1), inner, polyTerm(pInner), mkRefl(natLit(1)), pfInner)
      (pSum, mkTrans(term, m1, polyTerm(pSum), step1, pfSum))

    case app @ Term.App(_, _) =>
      val (head, args) = Term.splitApps(app)
      if (isAddHead(head) && args.length == 2) {
        val (pA, pfA) = normalizeNormNat(args(0))
        val (pB, pfB) = normalizeNormNat(args(1))
        val mid = mkAdd(polyTerm(pA), polyTerm(pB))
        val (pSum, pfSum) = addPolys(pA, pB)
        val step1 = mkCongrAdd(args(0), polyTerm(pA), args(1), polyTerm(pB), pfA, pfB)
        (pSum, mkTrans(term, mid, polyTerm(pSum), step1, pfSum))
      } else if (isMulHead(head) && args.length == 2) {
        val (pA, pfA) = normalizeNormNat(args(0))
        val (pB, pfB) = normalizeNormNat(args(1))
        val mid = mkMul(polyTerm(pA), polyTerm(pB))
        val (pProd, pfProd) = mulPolys(pA, pB)
        val step1 = mkCongrMul(args(0), polyTerm(pA), args(1), polyTerm(pB), pfA, pfB)
        (pProd, mkTrans(term, mid, polyTerm(pProd), step1, pfProd))
      } else {
        (Poly(0, List(List(term))), mkRefl(term))
      }

    case atom =>
      (Poly(0, List(List(atom))), mkRefl(atom))
  }
}
