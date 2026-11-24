package samurai.tactic

import scala.collection.mutable
import scala.util.boundary
import scala.util.boundary.break
import samurai.elab.ElabEnv
import samurai.kernel.*
import samurai.util.{Diagnostic, Span}

/**
 * Proof-producing Congruence Closure decision procedure (`cc`).
 *
 * Builds an equivalence graph over subterms from all local equality hypotheses (`a === b`),
 * saturates with reflexivity, symmetry, transitivity, application congruence (`f ~ g, a ~ b |- f(a) ~ g(b)`),
 * constructor injectivity (`C(a) === C(b) |- a === b`), and constructor disjointness (`C1(...) === C2(...) |- False`).
 * Synthesizes a 100% axiom-free core `Term` checked from scratch by `samurai.kernel.TypeChecker`.
 */
object CongruenceClosure {

  private final case class EqEdge(to: Term, eqType: Term, proof: Term)

  def solve(env: ElabEnv, state: ProofState, span: Span): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    solveGoal(env.kernelEnv, goal.localCtx, goal.targetType) match {
      case Some(proof) =>
        Right((env, state.replaceHead(Nil, _ => proof, state.nextGoalId)))
      case None =>
        Left(
          Diagnostic(
            Diagnostic.Severity.Error,
            "T075",
            s"'cc' could not close goal via congruence closure:\n${goal.formatHuman(env.kernelEnv)}",
            span
          )
        )
    }
  }

  /** Direct kernel-level entry point reusable from ProofSearch and suggest. */
  def solveGoal(kernelEnv: KernelEnv, localCtx: LocalCtx, targetType: Term): Option[Term] = boundary {
    val normTarget = NbE.normalize(kernelEnv, localCtx, targetType)

    // Handle `Not(P)` (`P => False`) by introducing `P` into context!
    normTarget match {
      case Term.Pi(name, dom, Term.Ind("False")) =>
        val freshName = if (name == "_" || name.isEmpty) s"_cc${localCtx.depth}" else name
        val innerCtx = localCtx.push(freshName, dom)
        break(solveGoal(kernelEnv, innerCtx, Term.Ind("False")).map(body => Term.Lam(freshName, dom, body)))
      case _ => ()
    }

    val engine = new CcEngine(kernelEnv, localCtx)
    engine.ingestContext()
    engine.collectSubterms(normTarget)
    engine.saturate()

    // 1. Check if context derived a contradiction (e.g. `0 === Succ(n)` or `true === false`)
    engine.contradictionProof.foreach { falsePf =>
      break(Some(mkAbsurd(targetType, falsePf)))
    }

    // 2. Check equality goal `lhs === rhs`
    val (head, args) = Term.splitApps(normTarget)
    head match {
      case Term.Ind("Eq") if args.length == 3 =>
        val (eqType, lhs, rhs) = (args(0), args(1), args(2))
        engine.findProof(lhs, rhs, eqType)
      case Term.Ind("True") =>
        Some(Term.Ctor("True", "Intro"))
      case _ =>
        None
    }
  }

  private def mkAbsurd(targetType: Term, falseProof: Term): Term =
    Term.Match("False", Nil, Term.Lam("_f", Term.Ind("False"), Term.shift(targetType, 1)), falseProof, Nil)

  private def mkRefl(eqType: Term, t: Term): Term =
    Term.apps(Term.Ctor("Eq", "Refl"), List(eqType, t))

  private def mkSym(eqType: Term, a: Term, b: Term, proofAB: Term): Term = {
    val ty1 = Term.shift(eqType, 1)
    val a1 = Term.shift(a, 1)
    val ty2 = Term.shift(eqType, 2)
    val a2 = Term.shift(a, 2)
    val motive = Term.Lam(
      "_y",
      eqType,
      Term.Lam(
        "_q",
        Term.apps(Term.Ind("Eq"), List(ty1, a1, Term.Var(0))),
        Term.apps(Term.Ind("Eq"), List(ty2, Term.Var(1), a2))
      )
    )
    Term.Match("Eq", List(eqType, a), motive, proofAB, List(MatchBranch("Refl", Nil, mkRefl(eqType, a))))
  }

  private def mkTrans(eqType: Term, a: Term, b: Term, c: Term, proofAB: Term, proofBC: Term): Term = {
    val ty1 = Term.shift(eqType, 1)
    val b1 = Term.shift(b, 1)
    val ty2 = Term.shift(eqType, 2)
    val a2 = Term.shift(a, 2)
    val motive = Term.Lam(
      "_y",
      eqType,
      Term.Lam(
        "_q",
        Term.apps(Term.Ind("Eq"), List(ty1, b1, Term.Var(0))),
        Term.apps(Term.Ind("Eq"), List(ty2, a2, Term.Var(1)))
      )
    )
    Term.Match("Eq", List(eqType, b), motive, proofBC, List(MatchBranch("Refl", Nil, proofAB)))
  }

  /** Synthesize `f(a) === f(b)` from `pfArg : a === b` (non-dependent function `f : A -> B`). */
  private def mkCongrArg(domTy: Term, codTy: Term, fn: Term, a: Term, b: Term, pfArg: Term): Term = {
    val dom1 = Term.shift(domTy, 1)
    val a1 = Term.shift(a, 1)
    val cod2 = Term.shift(codTy, 2)
    val fa2 = Term.shift(Term.App(fn, a), 2)
    val fn2 = Term.shift(fn, 2)
    val motive = Term.Lam(
      "_y",
      domTy,
      Term.Lam(
        "_q",
        Term.apps(Term.Ind("Eq"), List(dom1, a1, Term.Var(0))),
        Term.apps(Term.Ind("Eq"), List(cod2, fa2, Term.App(fn2, Term.Var(1))))
      )
    )
    Term.Match("Eq", List(domTy, a), motive, pfArg, List(MatchBranch("Refl", Nil, mkRefl(codTy, Term.App(fn, a)))))
  }

  /** Synthesize `f(x) === g(x)` from `pfFn : f === g` (`f, g : fnTy`). */
  private def mkCongrFn(fnTy: Term, codTy: Term, f: Term, g: Term, arg: Term, pfFn: Term): Term = {
    val fn1 = Term.shift(fnTy, 1)
    val f1 = Term.shift(f, 1)
    val cod2 = Term.shift(codTy, 2)
    val fx2 = Term.shift(Term.App(f, arg), 2)
    val arg2 = Term.shift(arg, 2)
    val motive = Term.Lam(
      "_y",
      fnTy,
      Term.Lam(
        "_q",
        Term.apps(Term.Ind("Eq"), List(fn1, f1, Term.Var(0))),
        Term.apps(Term.Ind("Eq"), List(cod2, fx2, Term.App(Term.Var(1), arg2)))
      )
    )
    Term.Match("Eq", List(fnTy, f), motive, pfFn, List(MatchBranch("Refl", Nil, mkRefl(codTy, Term.App(f, arg)))))
  }

  private final class CcEngine(kernelEnv: KernelEnv, localCtx: LocalCtx) {
    private val adj = mutable.Map.empty[Term, mutable.ListBuffer[EqEdge]]
    private val subterms = mutable.LinkedHashSet.empty[Term]
    private val appTerms = mutable.LinkedHashSet.empty[Term]
    private val ctorTerms = mutable.LinkedHashSet.empty[Term]
    private val typeCache = mutable.Map.empty[Term, Option[Term]]
    var contradictionProof: Option[Term] = None

    private def norm(t: Term): Term = NbE.normalize(kernelEnv, localCtx, t)

    private def inferType(t: Term): Option[Term] =
      typeCache.getOrElseUpdate(t, TypeChecker.infer(kernelEnv, localCtx, t).toOption.map(norm))

    def collectSubterms(t: Term): Unit = {
      val n = norm(t)
      if (!subterms.add(n)) return
      n match {
        case Term.App(f, a) =>
          appTerms += n
          val (h, _) = Term.splitApps(n)
          h match {
            case Term.Ctor(_, _) => ctorTerms += n
            case _               => ()
          }
          collectSubterms(f)
          collectSubterms(a)
        case Term.Ctor(_, _) =>
          ctorTerms += n
        case _ => ()
      }
    }

    private def addEdge(aRaw: Term, bRaw: Term, eqTypeRaw: Term, proofAB: Term): Boolean = {
      val a = norm(aRaw)
      val b = norm(bRaw)
      val eqType = norm(eqTypeRaw)
      collectSubterms(a)
      collectSubterms(b)
      if (a == b) return false
      if (findProof(a, b, eqType).isDefined) return false

      val bufA = adj.getOrElseUpdate(a, mutable.ListBuffer.empty)
      bufA += EqEdge(b, eqType, proofAB)
      val bufB = adj.getOrElseUpdate(b, mutable.ListBuffer.empty)
      bufB += EqEdge(a, eqType, mkSym(eqType, a, b, proofAB))
      true
    }

    def findProof(srcRaw: Term, dstRaw: Term, eqTypeRaw: Term): Option[Term] = boundary {
      val src = norm(srcRaw)
      val dst = norm(dstRaw)
      val eqType = norm(eqTypeRaw)
      if (src == dst) break(Some(mkRefl(eqType, src)))

      // BFS shortest path for compact proof terms
      val visited = mutable.Set[Term](src)
      val queue = mutable.Queue[(Term, Term)]()
      for (edge <- adj.getOrElse(src, Nil)) {
        if (edge.to == dst) break(Some(edge.proof))
        if (visited.add(edge.to)) {
          queue.enqueue((edge.to, edge.proof))
        }
      }
      while (queue.nonEmpty) {
        val (cur, pfSrcCur) = queue.dequeue()
        for (edge <- adj.getOrElse(cur, Nil)) {
          if (visited.add(edge.to)) {
            val combined = mkTrans(eqType, src, cur, edge.to, pfSrcCur, edge.proof)
            if (edge.to == dst) break(Some(combined))
            queue.enqueue((edge.to, combined))
          }
        }
      }
      None
    }

    private def ingestHypothesis(hypTerm: Term, hypType: Term, depth: Int): Unit = {
      if (depth <= 0 || contradictionProof.isDefined) return
      val normTy = norm(hypType)
      val (head, args) = Term.splitApps(normTy)
      head match {
        case Term.Ind("False") =>
          contradictionProof = Some(hypTerm)

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

        case Term.Ind("Eq") if args.length == 3 =>
          addEdge(args(1), args(2), args(0), hypTerm)

        case _ => ()
      }
    }

    def ingestContext(): Unit = {
      for (idx <- localCtx.entries.indices) {
        localCtx.lookupType(idx).foreach { ty =>
          ingestHypothesis(Term.Var(idx), ty, depth = 4)
        }
      }
    }

    def saturate(): Unit = {
      var changed = true
      var rounds = 0
      while (changed && rounds < 12 && contradictionProof.isEmpty) {
        changed = false
        rounds += 1

        // 1. Check constructor disjointness & injectivity across equivalent constructor terms
        val ctors = ctorTerms.toList
        for (i <- ctors.indices if contradictionProof.isEmpty) {
          val t1 = ctors(i)
          val (h1, args1) = Term.splitApps(t1)
          h1 match {
            case Term.Ctor(ind1, ctor1) =>
              for (j <- (i + 1) until ctors.length if contradictionProof.isEmpty) {
                val t2 = ctors(j)
                val (h2, args2) = Term.splitApps(t2)
                h2 match {
                  case Term.Ctor(ind2, ctor2) if ind1 == ind2 =>
                    inferType(t1).foreach { ty1 =>
                      findProof(t1, t2, ty1).foreach { eqPf =>
                        if (ctor1 != ctor2) {
                          // Disjoint constructors in the same equivalence class -> False!
                          synthesizeDisjointFalse(ind1, ctor1, ctor2, ty1, t1, t2, eqPf).foreach { fp =>
                            contradictionProof = Some(fp)
                          }
                        } else if (args1.length == args2.length) {
                          // Same constructor -> injectivity on computational fields!
                          kernelEnv.inductives.get(ind1).foreach { ind =>
                            ind.ctor(ctor1).foreach { cDecl =>
                              val fieldArgs1 = args1.drop(ind.numParams)
                              val fieldArgs2 = args2.drop(ind.numParams)
                              if (fieldArgs1.length == cDecl.arity && fieldArgs2.length == cDecl.arity) {
                                for (k <- fieldArgs1.indices) {
                                  if (fieldArgs1(k) != fieldArgs2(k)) {
                                    synthesizeInjection(ind, cDecl, ty1, t1, t2, k, fieldArgs1(k), fieldArgs2(k), eqPf).foreach {
                                      case (fTy, injPf) =>
                                        if (addEdge(fieldArgs1(k), fieldArgs2(k), fTy, injPf)) changed = true
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  case _ => ()
                }
              }
            case _ => ()
          }
        }

        if (contradictionProof.isDefined) return

        // 2. Application congruence: `f1 ~ f2` and `a1 ~ a2` => `f1(a1) ~ f2(a2)`
        val apps = appTerms.toList
        if (apps.length <= 80) {
          for (i <- apps.indices) {
            apps(i) match {
              case app1 @ Term.App(f1, a1) =>
                for (j <- (i + 1) until apps.length) {
                  apps(j) match {
                    case app2 @ Term.App(f2, a2) =>
                      (inferType(app1), inferType(app2), inferType(f1), inferType(a1)) match {
                        case (Some(cod1), Some(cod2), Some(fnTy1), Some(dom1)) if cod1 == cod2 =>
                          // Only apply non-dependent congruence when `f1 : dom1 -> cod1` (codomain doesn't depend on arg)
                          val isNonDependent = fnTy1 match {
                            case Term.Pi(_, d, c) if d == dom1 && !Term.freeVarOccurs(c, 0) => true
                            case _                                                          => false
                          }
                          if (isNonDependent && findProof(app1, app2, cod1).isEmpty) {
                            (findProof(f1, f2, fnTy1), findProof(a1, a2, dom1)) match {
                              case (Some(pfFn), Some(pfArg)) =>
                                // f1(a1) === f1(a2) === f2(a2)
                                val step1 =
                                  if (a1 == a2) mkRefl(cod1, app1)
                                  else mkCongrArg(dom1, cod1, f1, a1, a2, pfArg)
                                val mid = Term.App(f1, a2)
                                val step2 =
                                  if (f1 == f2) mkRefl(cod1, mid)
                                  else mkCongrFn(fnTy1, cod1, f1, f2, a2, pfFn)
                                val fullPf = mkTrans(cod1, app1, mid, app2, step1, step2)
                                if (addEdge(app1, app2, cod1, fullPf)) changed = true
                              case _ => ()
                            }
                          }
                        case _ => ()
                      }
                    case _ => ()
                  }
                }
              case _ => ()
            }
          }
        }
      }
    }

    private def synthesizeDisjointFalse(
      indName: String,
      ctor1: String,
      ctor2: String,
      indTypeTerm: Term,
      t1: Term,
      t2: Term,
      eqPf: Term
    ): Option[Term] = {
      val _ = (ctor2, t2)
      kernelEnv.inductives.get(indName).flatMap { ind =>
        if (ind.numIndices > 0 || !kernelEnv.inductives.contains("True") || !kernelEnv.inductives.contains("False")) {
          None
        } else {
          val (_, typeArgs) = Term.splitApps(indTypeTerm)
          val params = typeArgs.take(ind.numParams)
          val discMotive = Term.Lam("_d", indTypeTerm, Term.USort(Sort.Prop))
          val discBranches = ind.constructors.map { c =>
            val body = if (c.name == ctor1) Term.Ind("True") else Term.Ind("False")
            MatchBranch(c.name, c.fields.map(_.name), body)
          }
          val discFn = Term.Lam("_x", indTypeTerm, Term.Match(indName, params, discMotive, Term.Var(0), discBranches))
          val eqMotive = Term.Lam(
            "_y",
            indTypeTerm,
            Term.Lam(
              "_q",
              Term.apps(Term.Ind("Eq"), List(Term.shift(indTypeTerm, 1), Term.shift(t1, 1), Term.Var(0))),
              Term.App(Term.shift(discFn, 2), Term.Var(1))
            )
          )
          val falseProof = Term.Match("Eq", List(indTypeTerm, t1), eqMotive, eqPf, List(MatchBranch("Refl", Nil, Term.Ctor("True", "Intro"))))
          if (TypeChecker.check(kernelEnv, localCtx, falseProof, Term.Ind("False")).isRight) Some(falseProof)
          else None
        }
      }
    }

    private def synthesizeInjection(
      ind: IndEntry,
      cDecl: CtorEntry,
      indTypeTerm: Term,
      t1: Term,
      t2: Term,
      fieldIdx: Int,
      f1: Term,
      f2: Term,
      eqPf: Term
    ): Option[(Term, Term)] = {
      val _ = t2
      if (ind.numIndices > 0) return None
      inferType(f1).flatMap { fTy =>
        val (_, typeArgs) = Term.splitApps(indTypeTerm)
        val params = typeArgs.take(ind.numParams)
        val projMotive = Term.Lam("_p", indTypeTerm, Term.shift(fTy, 1))
        val projBranches = ind.constructors.map { c =>
          val body =
            if (c.name == cDecl.name) Term.Var(c.arity - 1 - fieldIdx)
            else Term.shift(f1, c.arity)
          MatchBranch(c.name, c.fields.map(_.name), body)
        }
        val projFn = Term.Lam("_x", indTypeTerm, Term.Match(ind.name, params, projMotive, Term.Var(0), projBranches))
        val eqPfOut = mkCongrArg(indTypeTerm, fTy, projFn, t1, t2, eqPf)
        val expectedTy = Term.apps(Term.Ind("Eq"), List(fTy, f1, f2))
        if (TypeChecker.check(kernelEnv, localCtx, eqPfOut, expectedTy).isRight) Some((fTy, eqPfOut))
        else None
      }
    }
  }
}
