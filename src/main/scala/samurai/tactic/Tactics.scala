package samurai.tactic

import scala.util.boundary
import scala.util.boundary.break
import samurai.elab.{ElabEnv, Elaborator, HoleInfo, MetaContext}
import samurai.kernel.*
import samurai.syntax.*
import samurai.util.{Diagnostic, Span}

/**
 * LCF-style tactic engine for Proof Samurai.
 *
 * Every tactic transforms an immutable `ProofState` and records a proof-term combinator.
 * No tactic is trusted for soundness: the final reconstructed core `Term` is always
 * independently verified by `samurai.kernel.TypeChecker`.
 */
object Tactics {

  def runScript(
    env: ElabEnv,
    initialState: ProofState,
    tactics: List[TacticStmt]
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    boundary {
      var curEnv = env
      var curState = initialState
      for (stmt <- tactics) {
        step(curEnv, curState, stmt) match {
          case Left(err) => break(Left(err))
          case Right((nextEnv, nextState)) =>
            curEnv = nextEnv
            curState = nextState
        }
      }
      Right((curEnv, curState))
    }
  }

  def step(
    env: ElabEnv,
    state: ProofState,
    stmt: TacticStmt
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    if (state.isSolved) {
      stmt match {
        case TacticStmt.Try(_, _) | TacticStmt.Repeat(_, _, _) | TacticStmt.AllGoals(_, _) =>
          return Right((env, state))
        case _ =>
          return Left(Diagnostic(Diagnostic.Severity.Error, "T001", s"No open goals remaining for tactic", stmt.span))
      }
    }

    stmt match {
      case TacticStmt.Intro(names, span)                => tacticIntro(env, state, names, span)
      case TacticStmt.Exact(expr, span)                 => tacticExact(env, state, expr, span)
      case TacticStmt.Apply(expr, span)                 => tacticApply(env, state, expr, span)
      case TacticStmt.Refl(span)                        => tacticRefl(env, state, span)
      case TacticStmt.Symmetry(span)                    => tacticSymmetry(env, state, span)
      case TacticStmt.Trans(midExpr, span)              => tacticTrans(env, state, midExpr, span)
      case TacticStmt.Rewrite(lemmas, rev, target, span)         => tacticRewriteTarget(env, state, lemmas, rev, target, span)
      case TacticStmt.Congr(span)                                => tacticCongr(env, state, span)
      case TacticStmt.Induction(target, cases, span)             => tacticInduction(env, state, target, cases, span)
      case TacticStmt.Cases(target, eqName, cases, span)         => tacticCases(env, state, target, eqName, cases, span)
      case TacticStmt.ByCases(cond, eqName, cases, span)         => tacticCases(env, state, cond, eqName.orElse(Some("hCase")), cases, span)
      case TacticStmt.Obtain(binders, source, span)              => tacticObtain(env, state, binders, source, span)
      case TacticStmt.Revert(names, span)                        => tacticRevert(env, state, names, span)
      case TacticStmt.Rename(oldName, newName, span)             => tacticRename(env, state, oldName, newName, span)
      case TacticStmt.Exfalso(span)                              => tacticExfalso(env, state, span)
      case TacticStmt.Subst(hyp, span)                           => tacticSubst(env, state, hyp, span)
      case TacticStmt.Specialize(hypName, args, span)            => tacticSpecialize(env, state, hypName, args, span)
      case TacticStmt.Split(span)                                => tacticSplit(env, state, span)
      case TacticStmt.LeftBranch(span)                           => tacticLeftOrRight(env, state, isLeft = true, span)
      case TacticStmt.RightBranch(span)                          => tacticLeftOrRight(env, state, isLeft = false, span)
      case TacticStmt.ExistsWitness(witness, span)               => tacticExists(env, state, witness, span)
      case TacticStmt.Contradiction(span)                        => tacticContradiction(env, state, span)
      case TacticStmt.Discriminate(hypOpt, span)                 => tacticDiscriminate(env, state, hypOpt, span)
      case TacticStmt.Injection(hypExpr, names, span)            => tacticInjection(env, state, hypExpr, names, span)
      case TacticStmt.Have(name, propTy, proof, span)            => tacticHave(env, state, name, propTy, proof, span)
      case TacticStmt.Unfold(defName, span)                      => tacticUnfold(env, state, defName, span)
      case TacticStmt.Simp(extras, useLocals, target, span)      => tacticSimpTarget(env, state, extras, useLocals, target, span)
      case TacticStmt.Arith(span)                                => ArithTactic.solve(env, state, span)
      case TacticStmt.Omega(span)                                => OmegaTactic.solve(env, state, span)
      case TacticStmt.CongruenceClosure(span)                    => CongruenceClosure.solve(env, state, span)
      case TacticStmt.Tauto(span)                                => tacticTauto(env, state, span)
      case TacticStmt.Trivial(span)                              => tacticTrivial(env, state, span)
      case TacticStmt.Auto(depthOpt, span)                       => ProofSearch.tacticAuto(env, state, depthOpt.getOrElse(5), span)
      case TacticStmt.Decide(span)                               => tacticDecide(env, state, span)
      case TacticStmt.Assumption(span)                           => tacticAssumption(env, state, span)
      case TacticStmt.Try(body, span)                            => tacticTry(env, state, body, span)
      case TacticStmt.Repeat(body, maxSteps, span)               => tacticRepeat(env, state, body, maxSteps.getOrElse(32), span)
      case TacticStmt.AllGoals(body, span)                       => tacticAllGoals(env, state, body, span)
      case TacticStmt.First(branches, span)                      => tacticFirst(env, state, branches, span)
      case TacticStmt.SeqAll(first, after, span)                 => tacticSeqAll(env, state, first, after, span)
      case TacticStmt.Block(stmts, _)                            => runScript(env, state, stmts)
      case TacticStmt.Sorry(span)                                => tacticSorry(env, state, span)
      case TacticStmt.Hole(nameOpt, span)                        => tacticHole(env, state, nameOpt, span)
    }
  }

  // ===========================================================================
  // Core Tactics
  // ===========================================================================

  private def tacticIntro(
    env: ElabEnv,
    state: ProofState,
    names: List[String],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    if (names.isEmpty) {
      // Introduce one binder using its default name
      introSingle(env, state, None, span)
    } else {
      boundary {
        var curEnv = env
        var curState = state
        for (name <- names) {
          introSingle(curEnv, curState, Some(name), span) match {
            case Left(err)        => break(Left(err))
            case Right((e, next)) => curEnv = e; curState = next
          }
        }
        Right((curEnv, curState))
      }
    }
  }

  private def introSingle(
    env: ElabEnv,
    state: ProofState,
    nameOpt: Option[String],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(env.kernelEnv, goal.localCtx, fuel)
    NbE.evaluate(env.kernelEnv, evalEnv, goal.targetType, fuel) match {
      case Value.VPi(defaultName, domVal, codClosure) =>
        val chosenName = nameOpt.getOrElse(if (defaultName == "_" || defaultName.isEmpty) s"h${goal.localCtx.depth}" else defaultName)
        val domTerm = NbE.quote(env.kernelEnv, goal.localCtx.depth, domVal, fuel)
        val freshVar = Value.VNeutral(NeutralHead.NVar(goal.localCtx.depth), Nil)
        val codTerm = NbE.quote(env.kernelEnv, goal.localCtx.depth + 1, NbE.applyClosure(env.kernelEnv, codClosure, freshVar, fuel), fuel)
        val subId = state.nextGoalId
        val subGoal = ProofGoal(subId, goal.label, goal.localCtx.push(chosenName, domTerm), codTerm)
        val nextState = state.replaceHead(
          List(subGoal),
          sols => Term.Lam(chosenName, domTerm, sols(subId)),
          subId + 1
        )
        Right((env, nextState))

      case _ =>
        Left(
          Diagnostic(
            Diagnostic.Severity.Error,
            "T002",
            s"Cannot apply 'intro': goal '${Pretty.show(goal.targetType, goal.localCtx.names)}' is not a function or forall type",
            span
          )
        )
    }
  }

  private def tacticExact(
    env: ElabEnv,
    state: ProofState,
    expr: SurfaceExpr,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val metaCtx = new MetaContext()
    Elaborator.checkExpr(env, metaCtx, goal.localCtx, expr, goal.targetType).flatMap { case (term, nextEnv) =>
      val zonked = metaCtx.zonk(term, goal.localCtx.depth)
      if (metaCtx.unsolvedEntries.nonEmpty) {
        Left(Diagnostic(Diagnostic.Severity.Error, "T003", "Unsolved metavariables in 'exact' argument", span))
      } else {
        Right((nextEnv, state.replaceHead(Nil, _ => zonked, state.nextGoalId)))
      }
    }
  }

  private def tacticAssumption(
    env: ElabEnv,
    state: ProofState,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = boundary {
    val goal = state.openGoals.head
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(env.kernelEnv, goal.localCtx, fuel)
    val targetVal = NbE.evaluate(env.kernelEnv, evalEnv, goal.targetType, fuel)

    for (idx <- goal.localCtx.entries.indices) {
      val hypTy = goal.localCtx.lookupType(idx).get
      val hypVal = NbE.evaluate(env.kernelEnv, evalEnv, hypTy, fuel)
      if (NbE.isSubtype(env.kernelEnv, goal.localCtx.depth, hypVal, targetVal, fuel)) {
        break(Right((env, state.replaceHead(Nil, _ => Term.Var(idx), state.nextGoalId))))
      }
    }
    Left(Diagnostic(Diagnostic.Severity.Error, "T004", "No hypothesis in context matches the current goal", span))
  }

  private def tacticApply(
    env: ElabEnv,
    state: ProofState,
    expr: SurfaceExpr,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val metaCtx = new MetaContext()
    Elaborator.inferExpr(env, metaCtx, goal.localCtx, expr).flatMap { case (baseTerm, baseType, nextEnv) =>
      applyCoreTerm(nextEnv, state, goal, metaCtx, baseTerm, baseType, span)
    }
  }

  def applyCoreTerm(
    env: ElabEnv,
    state: ProofState,
    goal: ProofGoal,
    metaCtx: MetaContext,
    baseTerm: Term,
    baseType: Term,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(env.kernelEnv, goal.localCtx, fuel)

    // Try unifying directly first, otherwise peel Pi binders one by one creating fresh metas!
    var curTerm = baseTerm
    var curType = metaCtx.zonk(baseType, goal.localCtx.depth)
    val argMetas = List.newBuilder[(Int, String, Term)] // (metaId, binderName, domainType)

    var matched = false
    var attempts = 0
    var lastUnifyError = ""
    while (!matched && attempts < 32) {
      metaCtx.unify(env.kernelEnv, goal.localCtx, curType, goal.targetType, allowSubtyping = true) match {
        case Right(()) =>
          matched = true
        case Left(uErr) =>
          lastUnifyError = uErr
          val zonkedCur = metaCtx.zonk(curType, goal.localCtx.depth)
          zonkedCur match {
            case Term.Pi(binderName, domTerm, codTerm) =>
              // Peel Pi syntactically first so transparent definitions (e.g. Lt, blt, length) stay folded for unification!
              val metaTerm = metaCtx.freshMeta(goal.localCtx.depth, domTerm, Some(binderName))
              val metaId = MetaContext.parseMetaId(metaTerm.asInstanceOf[Term.Const].name).get
              argMetas += ((metaId, binderName, domTerm))
              curTerm = Term.App(curTerm, metaTerm)
              curType = Term.subst(codTerm, 0, metaTerm)
              attempts += 1
            case _ =>
              val tyVal = NbE.evaluate(env.kernelEnv, evalEnv, zonkedCur, fuel)
              tyVal match {
                case Value.VPi(binderName, domVal, codClosure) =>
                  val domTerm = NbE.quote(env.kernelEnv, goal.localCtx.depth, domVal, fuel)
                  val metaTerm = metaCtx.freshMeta(goal.localCtx.depth, domTerm, Some(binderName))
                  val metaId = MetaContext.parseMetaId(metaTerm.asInstanceOf[Term.Const].name).get
                  argMetas += ((metaId, binderName, domTerm))
                  curTerm = Term.App(curTerm, metaTerm)
                  val metaVal = NbE.evaluate(env.kernelEnv, evalEnv, metaTerm, fuel)
                  curType = NbE.quote(env.kernelEnv, goal.localCtx.depth, NbE.applyClosure(env.kernelEnv, codClosure, metaVal, fuel), fuel)
                  attempts += 1
                case _ =>
                  return Left(
                    Diagnostic(
                      Diagnostic.Severity.Error,
                      "T005",
                      s"Cannot apply term of type '${Pretty.show(metaCtx.zonk(baseType, goal.localCtx.depth), goal.localCtx.names)}' " +
                        s"to goal '${Pretty.show(goal.targetType, goal.localCtx.names)}' ($lastUnifyError)",
                      span
                    )
                  )
              }
          }
      }
    }

    if (!matched) {
      return Left(Diagnostic(Diagnostic.Severity.Error, "T005", "Failed to unify conclusion in 'apply'", span))
    }

    // Any remaining unsolved arg metas become new subgoals!
    val allArgMetas = argMetas.result()
    val subgoals = List.newBuilder[ProofGoal]
    val metaToGoalId = scala.collection.mutable.Map.empty[Int, Int]
    var nextId = state.nextGoalId

    for ((metaId, binderName, domTerm) <- allArgMetas) {
      if (!metaCtx.isSolved(metaId)) {
        val zonkedDom = metaCtx.zonk(domTerm, goal.localCtx.depth)
        subgoals += ProofGoal(nextId, s"arg:$binderName", goal.localCtx, zonkedDom)
        metaToGoalId(metaId) = nextId
        nextId += 1
      }
    }

    // Verify no non-argument metas remain unsolved
    val remainingUnsolved = metaCtx.unsolvedEntries.filterNot(e => metaToGoalId.contains(e.id))
    if (remainingUnsolved.nonEmpty) {
      return Left(Diagnostic(Diagnostic.Severity.Error, "T005", "Could not infer implicit argument(s) during 'apply'", span))
    }

    val templateTerm = metaCtx.zonk(curTerm, goal.localCtx.depth)
    val metaMapImmutable = metaToGoalId.toMap

    val nextState = state.replaceHead(
      subgoals.result(),
      solutions => substituteGoalMetas(templateTerm, metaMapImmutable, solutions, 0),
      nextId
    )
    Right((env, nextState))
  }

  private def substituteGoalMetas(
    term: Term,
    metaToGoal: Map[Int, Int],
    solutions: Map[Int, Term],
    depthOffset: Int
  ): Term = term match {
    case Term.Const(name) =>
      MetaContext.parseMetaId(name).flatMap(metaToGoal.get) match {
        case Some(goalId) => Term.shift(solutions(goalId), depthOffset)
        case None         => term
      }
    case Term.USort(_) | Term.Var(_) | Term.Ind(_) | Term.Ctor(_, _) => term
    case Term.Pi(n, d, c) =>
      Term.Pi(n, substituteGoalMetas(d, metaToGoal, solutions, depthOffset), substituteGoalMetas(c, metaToGoal, solutions, depthOffset + 1))
    case Term.Lam(n, d, b) =>
      Term.Lam(n, substituteGoalMetas(d, metaToGoal, solutions, depthOffset), substituteGoalMetas(b, metaToGoal, solutions, depthOffset + 1))
    case Term.App(f, a) =>
      Term.App(substituteGoalMetas(f, metaToGoal, solutions, depthOffset), substituteGoalMetas(a, metaToGoal, solutions, depthOffset))
    case Term.Let(n, ty, v, b) =>
      Term.Let(
        n,
        substituteGoalMetas(ty, metaToGoal, solutions, depthOffset),
        substituteGoalMetas(v, metaToGoal, solutions, depthOffset),
        substituteGoalMetas(b, metaToGoal, solutions, depthOffset + 1)
      )
    case Term.Match(ind, ps, m, s, brs) =>
      Term.Match(
        ind,
        ps.map(substituteGoalMetas(_, metaToGoal, solutions, depthOffset)),
        substituteGoalMetas(m, metaToGoal, solutions, depthOffset),
        substituteGoalMetas(s, metaToGoal, solutions, depthOffset),
        brs.map(br => br.copy(body = substituteGoalMetas(br.body, metaToGoal, solutions, depthOffset + br.arity)))
      )
    case Term.Fix(n, r, ty, b) =>
      Term.Fix(n, r, substituteGoalMetas(ty, metaToGoal, solutions, depthOffset), substituteGoalMetas(b, metaToGoal, solutions, depthOffset + 1))
    case Term.MutualFix(defs, sel) =>
      val k = defs.length
      Term.MutualFix(
        defs.map(d =>
          d.copy(
            ty = substituteGoalMetas(d.ty, metaToGoal, solutions, depthOffset),
            body = substituteGoalMetas(d.body, metaToGoal, solutions, depthOffset + k)
          )
        ),
        sel
      )
  }

  // ===========================================================================
  // Equality Tactics: refl, symmetry, trans, rewrite, congr
  // ===========================================================================

  def extractEqGoal(kernelEnv: KernelEnv, localCtx: LocalCtx, term: Term): Option[(Term, Term, Term)] = {
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(kernelEnv, localCtx, fuel)
    NbE.evaluate(kernelEnv, evalEnv, term, fuel) match {
      case Value.VInd("Eq", List(eqTyVal, lhsVal, rhsVal)) =>
        Some((
          NbE.quote(kernelEnv, localCtx.depth, eqTyVal, fuel),
          NbE.quote(kernelEnv, localCtx.depth, lhsVal, fuel),
          NbE.quote(kernelEnv, localCtx.depth, rhsVal, fuel)
        ))
      case _ => None
    }
  }

  private def tacticRefl(env: ElabEnv, state: ProofState, span: Span): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    extractEqGoal(env.kernelEnv, goal.localCtx, goal.targetType) match {
      case Some((eqType, lhs, rhs)) =>
        val fuel = new NbE.Fuel()
        val evalEnv = NbE.buildEvalEnv(env.kernelEnv, goal.localCtx, fuel)
        val lVal = NbE.evaluate(env.kernelEnv, evalEnv, lhs, fuel)
        val rVal = NbE.evaluate(env.kernelEnv, evalEnv, rhs, fuel)
        if (NbE.areConvertible(env.kernelEnv, goal.localCtx.depth, lVal, rVal, fuel)) {
          val reflProof = Term.apps(Term.Ctor("Eq", "Refl"), List(eqType, lhs))
          Right((env, state.replaceHead(Nil, _ => reflProof, state.nextGoalId)))
        } else {
          Left(
            Diagnostic(
              Diagnostic.Severity.Error,
              "T010",
              s"Reflexivity failed: '${Pretty.show(lhs, goal.localCtx.names)}' is not definitionally equal to '${Pretty.show(rhs, goal.localCtx.names)}'",
              span
            )
          )
        }
      case None =>
        Left(Diagnostic(Diagnostic.Severity.Error, "T011", s"Goal is not an equality ('===') for 'refl'", span))
    }
  }

  private def buildSymProof(eqType: Term, lhs: Term, rhs: Term, proof: Term): Term = {
    val eqType1 = Term.shift(eqType, 1)
    val lhs1 = Term.shift(lhs, 1)
    val eqType2 = Term.shift(eqType, 2)
    val lhs2 = Term.shift(lhs, 2)
    val symMotive = Term.Lam(
      "_y",
      eqType,
      Term.Lam(
        "_q",
        Term.apps(Term.Ind("Eq"), List(eqType1, lhs1, Term.Var(0))),
        Term.apps(Term.Ind("Eq"), List(eqType2, Term.Var(1), lhs2))
      )
    )
    Term.Match(
      "Eq",
      List(eqType, lhs),
      symMotive,
      proof,
      List(MatchBranch("Refl", Nil, Term.apps(Term.Ctor("Eq", "Refl"), List(eqType, lhs))))
    )
  }

  private def tacticSymmetry(env: ElabEnv, state: ProofState, span: Span): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    extractEqGoal(env.kernelEnv, goal.localCtx, goal.targetType) match {
      case Some((eqType, lhs, rhs)) =>
        val subId = state.nextGoalId
        val swappedTarget = Term.apps(Term.Ind("Eq"), List(eqType, rhs, lhs))
        val subGoal = ProofGoal(subId, goal.label, goal.localCtx, swappedTarget)
        val nextState = state.replaceHead(
          List(subGoal),
          sols => buildSymProof(eqType, rhs, lhs, sols(subId)),
          subId + 1
        )
        Right((env, nextState))
      case None =>
        Left(Diagnostic(Diagnostic.Severity.Error, "T012", "Goal is not an equality ('===') for 'symmetry'", span))
    }
  }

  private def tacticTrans(
    env: ElabEnv,
    state: ProofState,
    midExpr: SurfaceExpr,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    extractEqGoal(env.kernelEnv, goal.localCtx, goal.targetType) match {
      case Some((eqType, lhs, rhs)) =>
        val metaCtx = new MetaContext()
        Elaborator.checkExpr(env, metaCtx, goal.localCtx, midExpr, eqType).map { case (midRaw, nextEnv) =>
          val mid = metaCtx.zonk(midRaw, goal.localCtx.depth)
          val id1 = state.nextGoalId
          val id2 = state.nextGoalId + 1
          val g1 = ProofGoal(id1, "trans:left", goal.localCtx, Term.apps(Term.Ind("Eq"), List(eqType, lhs, mid)))
          val g2 = ProofGoal(id2, "trans:right", goal.localCtx, Term.apps(Term.Ind("Eq"), List(eqType, mid, rhs)))
          val eqType1 = Term.shift(eqType, 1)
          val mid1 = Term.shift(mid, 1)
          val eqType2 = Term.shift(eqType, 2)
          val lhs2 = Term.shift(lhs, 2)
          val transMotive = Term.Lam(
            "_y",
            eqType,
            Term.Lam(
              "_q",
              Term.apps(Term.Ind("Eq"), List(eqType1, mid1, Term.Var(0))),
              Term.apps(Term.Ind("Eq"), List(eqType2, lhs2, Term.Var(1)))
            )
          )
          val nextState = state.replaceHead(
            List(g1, g2),
            sols =>
              Term.Match(
                "Eq",
                List(eqType, mid),
                transMotive,
                sols(id2),
                List(MatchBranch("Refl", Nil, sols(id1)))
              ),
            id2 + 1
          )
          (nextEnv, nextState)
        }
      case None =>
        Left(Diagnostic(Diagnostic.Severity.Error, "T013", "Goal is not an equality ('===') for 'trans'", span))
    }
  }

  private def tacticRewriteTarget(
    env: ElabEnv,
    state: ProofState,
    lemmas: List[SurfaceExpr],
    reverse: Boolean,
    target: Option[String],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = target match {
    case None =>
      tacticRewriteMany(env, state, lemmas, reverse, span)
    case Some("*") =>
      boundary {
        var curEnv = env
        var curState = state
        for (lemmaExpr <- lemmas) {
          var anyChange = false
          val skipNameOpt = lemmaExpr match {
            case SurfaceExpr.VarExpr(n, _) => Some(n)
            case _                         => None
          }
          val hypNames = curState.openGoals.head.localCtx.entries.map(_.name).distinct.filterNot(n => skipNameOpt.contains(n))
          for (hName <- hypNames) {
            tacticRewriteInHyp(curEnv, curState, lemmaExpr, reverse, hName, span) match {
              case Right((nextEnv, nextState)) =>
                curEnv = nextEnv; curState = nextState; anyChange = true
              case Left(_) => ()
            }
          }
          tacticRewrite(curEnv, curState, lemmaExpr, reverse, span) match {
            case Right((nextEnv, nextState)) =>
              curEnv = nextEnv; curState = nextState; anyChange = true
            case Left(_) => ()
          }
          if (!anyChange) {
            break(Left(Diagnostic(Diagnostic.Severity.Error, "T015", "'rewrite(...) in *' did not match any hypothesis or the goal", span)))
          }
        }
        Right((curEnv, curState))
      }
    case Some(hypName) =>
      boundary {
        var curEnv = env
        var curState = state
        for (lemmaExpr <- lemmas) {
          tacticRewriteInHyp(curEnv, curState, lemmaExpr, reverse, hypName, span) match {
            case Left(err) => break(Left(err))
            case Right((nextEnv, nextState)) =>
              curEnv = nextEnv; curState = nextState
          }
        }
        Right((curEnv, curState))
      }
  }

  private def tacticRewriteInHyp(
    env: ElabEnv,
    state: ProofState,
    lemmaExpr: SurfaceExpr,
    reverse: Boolean,
    hypName: String,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val metaCtx = new MetaContext()
    Elaborator.inferExpr(env, metaCtx, goal.localCtx, lemmaExpr).flatMap { case (rawProof, rawType, nextEnv) =>
      rewriteInHypWithCoreLemma(nextEnv, state, goal, metaCtx, rawProof, rawType, reverse, hypName, span)
    }
  }

  private def lookupHyp(localCtx: LocalCtx, hypName: String): Option[(Int, Term)] = {
    val idx = localCtx.entries.indexWhere(_.name == hypName)
    if (idx < 0) None
    else localCtx.lookupType(idx).map(ty => (idx, ty))
  }

  def rewriteInHypWithCoreLemma(
    env: ElabEnv,
    state: ProofState,
    goal: ProofGoal,
    metaCtx: MetaContext,
    rawProof: Term,
    rawType: Term,
    reverse: Boolean,
    hypName: String,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val (hypIdx, rawHypTy) = lookupHyp(goal.localCtx, hypName) match {
      case Some(pair) => pair
      case None =>
        return Left(Diagnostic(Diagnostic.Severity.Error, "T015", s"Unknown hypothesis '$hypName' in 'rewrite ... in $hypName'", span))
    }

    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(env.kernelEnv, goal.localCtx, fuel)
    var curProof = rawProof
    var curType = metaCtx.zonk(rawType, goal.localCtx.depth)
    var peeled = 0
    while (peeled < 16) {
      NbE.evaluate(env.kernelEnv, evalEnv, curType, fuel) match {
        case Value.VPi(bName, domVal, codClosure) =>
          val domTerm = NbE.quote(env.kernelEnv, goal.localCtx.depth, domVal, fuel)
          val meta = metaCtx.freshMeta(goal.localCtx.depth, domTerm, Some(bName))
          curProof = Term.App(curProof, meta)
          val metaVal = NbE.evaluate(env.kernelEnv, evalEnv, meta, fuel)
          curType = NbE.quote(env.kernelEnv, goal.localCtx.depth, NbE.applyClosure(env.kernelEnv, codClosure, metaVal, fuel), fuel)
          peeled += 1
        case _ =>
          peeled = 16
      }
    }

    val (eqTypeRaw, lhsRaw, rhsRaw) = extractEqGoal(env.kernelEnv, goal.localCtx, curType) match {
      case Some(triple) => triple
      case None =>
        return Left(
          Diagnostic(
            Diagnostic.Severity.Error,
            "T014",
            s"Rewrite lemma must have an equality type ('==='), found '${Pretty.show(curType, goal.localCtx.names)}'",
            span
          )
        )
    }

    val searchPattern = if (reverse) rhsRaw else lhsRaw
    val normalizedHypTy = NbE.normalize(env.kernelEnv, goal.localCtx, rawHypTy)

    val normPattern = NbE.normalize(env.kernelEnv, goal.localCtx, metaCtx.zonk(searchPattern, goal.localCtx.depth))
    normPattern match {
      case Term.Const(m) if MetaContext.isMeta(m) =>
        return Left(Diagnostic(Diagnostic.Severity.Error, "T015", "Rewrite pattern reduces to a bare metavariable", span))
      case _ => ()
    }

    if (metaCtx.unsolvedEntries.nonEmpty) {
      if (!unifyWithAnySubterm(env.kernelEnv, goal.localCtx, metaCtx, searchPattern, eqTypeRaw, normalizedHypTy)) {
        return Left(
          Diagnostic(
            Diagnostic.Severity.Error,
            "T015",
            s"Rewrite pattern '${Pretty.show(metaCtx.zonk(searchPattern, goal.localCtx.depth), goal.localCtx.names)}' " +
              s"did not match any subterm of hypothesis '$hypName : ${Pretty.show(normalizedHypTy, goal.localCtx.names)}'",
            span
          )
        )
      }
    }

    val eqType = metaCtx.zonk(eqTypeRaw, goal.localCtx.depth)
    val lhs = metaCtx.zonk(lhsRaw, goal.localCtx.depth)
    val rhs = metaCtx.zonk(rhsRaw, goal.localCtx.depth)
    val lemmaProof = metaCtx.zonk(curProof, goal.localCtx.depth)

    if (metaCtx.unsolvedEntries.nonEmpty) {
      return Left(Diagnostic(Diagnostic.Severity.Error, "T015", "Could not instantiate all arguments of rewrite lemma", span))
    }

    // Forward transport on hypothesis `h : P(fromTerm)` using `fwdProof : fromTerm === toTerm` -> `P(toTerm)`!
    val (fromTerm, toTerm, fwdProof) =
      if (!reverse) (lhs, rhs, lemmaProof)
      else (rhs, lhs, buildSymProof(eqType, lhs, rhs, lemmaProof))

    val (motiveBody, replacedCount) = abstractSubterm(
      env.kernelEnv,
      goal.localCtx,
      normalizedHypTy,
      fromTerm,
      replacementVarIdx = 1,
      extraDepth = 2
    )

    if (replacedCount == 0) {
      return Left(
        Diagnostic(
          Diagnostic.Severity.Error,
          "T015",
          s"Rewrite target '${Pretty.show(fromTerm, goal.localCtx.names)}' does not occur in hypothesis '$hypName'",
          span
        )
      )
    }

    val eqType1 = Term.shift(eqType, 1)
    val fromTerm1 = Term.shift(fromTerm, 1)
    val motive = Term.Lam(
      "_z",
      eqType,
      Term.Lam(
        "_p",
        Term.apps(Term.Ind("Eq"), List(eqType1, fromTerm1, Term.Var(0))),
        motiveBody
      )
    )

    val newHypTy = NbE.normalize(
      env.kernelEnv,
      goal.localCtx,
      Term.apps(motive, List(toTerm, fwdProof))
    )
    val newHypProof = Term.Match(
      "Eq",
      List(eqType, fromTerm),
      motive,
      fwdProof,
      List(MatchBranch("Refl", Nil, Term.Var(hypIdx)))
    )

    val subId = state.nextGoalId
    val subCtx = goal.localCtx.push(hypName, newHypTy, Some(newHypProof))
    val subGoal = ProofGoal(subId, goal.label, subCtx, Term.shift(goal.targetType, 1))
    val nextState = state.replaceHead(
      List(subGoal),
      sols => Term.Let(hypName, newHypTy, newHypProof, sols(subId)),
      subId + 1
    )
    Right((env, nextState))
  }

  private def tacticRewriteMany(
    env: ElabEnv,
    state: ProofState,
    lemmas: List[SurfaceExpr],
    reverse: Boolean,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = boundary {
    var curEnv = env
    var curState = state
    for (lemmaExpr <- lemmas) {
      tacticRewrite(curEnv, curState, lemmaExpr, reverse, span) match {
        case Left(err) => break(Left(err))
        case Right((nextEnv, nextState)) =>
          curEnv = nextEnv
          curState = nextState
      }
    }
    Right((curEnv, curState))
  }

  private def tacticRewrite(
    env: ElabEnv,
    state: ProofState,
    lemmaExpr: SurfaceExpr,
    reverse: Boolean,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val metaCtx = new MetaContext()
    Elaborator.inferExpr(env, metaCtx, goal.localCtx, lemmaExpr).flatMap { case (rawProof, rawType, nextEnv) =>
      rewriteWithCoreLemma(nextEnv, state, goal, metaCtx, rawProof, rawType, reverse, span)
    }
  }

  def rewriteWithCoreLemma(
    env: ElabEnv,
    state: ProofState,
    goal: ProofGoal,
    metaCtx: MetaContext,
    rawProof: Term,
    rawType: Term,
    reverse: Boolean,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    // Peel leading Pi binders into fresh metavariables so `rewrite(addZeroRight)` works without explicit args!
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(env.kernelEnv, goal.localCtx, fuel)
    var curProof = rawProof
    var curType = metaCtx.zonk(rawType, goal.localCtx.depth)
    var peeled = 0
    while (peeled < 16) {
      NbE.evaluate(env.kernelEnv, evalEnv, curType, fuel) match {
        case Value.VPi(bName, domVal, codClosure) =>
          val domTerm = NbE.quote(env.kernelEnv, goal.localCtx.depth, domVal, fuel)
          val meta = metaCtx.freshMeta(goal.localCtx.depth, domTerm, Some(bName))
          curProof = Term.App(curProof, meta)
          val metaVal = NbE.evaluate(env.kernelEnv, evalEnv, meta, fuel)
          curType = NbE.quote(env.kernelEnv, goal.localCtx.depth, NbE.applyClosure(env.kernelEnv, codClosure, metaVal, fuel), fuel)
          peeled += 1
        case _ =>
          peeled = 16
      }
    }

    val (eqTypeRaw, lhsRaw, rhsRaw) = extractEqGoal(env.kernelEnv, goal.localCtx, curType) match {
      case Some(triple) => triple
      case None =>
        return Left(
          Diagnostic(
            Diagnostic.Severity.Error,
            "T014",
            s"Rewrite lemma must have an equality type ('==='), found '${Pretty.show(curType, goal.localCtx.names)}'",
            span
          )
        )
    }

    val searchPattern = if (reverse) rhsRaw else lhsRaw
    val normalizedTarget = NbE.normalize(env.kernelEnv, goal.localCtx, goal.targetType)

    // Reject bare metavariable rewrite patterns (e.g., from `0 + x === x` normalizing LHS to `?x`)
    val normPattern = NbE.normalize(env.kernelEnv, goal.localCtx, metaCtx.zonk(searchPattern, goal.localCtx.depth))
    normPattern match {
      case Term.Const(m) if MetaContext.isMeta(m) =>
        return Left(Diagnostic(Diagnostic.Severity.Error, "T015", "Rewrite pattern reduces to a bare metavariable", span))
      case _ => ()
    }

    // If `searchPattern` has unsolved metas, match it against a subterm of `normalizedTarget` of matching type!
    if (metaCtx.unsolvedEntries.nonEmpty) {
      if (!unifyWithAnySubterm(env.kernelEnv, goal.localCtx, metaCtx, searchPattern, eqTypeRaw, normalizedTarget)) {
        return Left(
          Diagnostic(
            Diagnostic.Severity.Error,
            "T015",
            s"Rewrite pattern '${Pretty.show(metaCtx.zonk(searchPattern, goal.localCtx.depth), goal.localCtx.names)}' " +
              s"did not match any subterm of goal '${Pretty.show(normalizedTarget, goal.localCtx.names)}'",
            span
          )
        )
      }
    }

    val eqType = metaCtx.zonk(eqTypeRaw, goal.localCtx.depth)
    val lhs = metaCtx.zonk(lhsRaw, goal.localCtx.depth)
    val rhs = metaCtx.zonk(rhsRaw, goal.localCtx.depth)
    val lemmaProof = metaCtx.zonk(curProof, goal.localCtx.depth)

    if (metaCtx.unsolvedEntries.nonEmpty) {
      return Left(Diagnostic(Diagnostic.Severity.Error, "T015", "Could not instantiate all arguments of rewrite lemma", span))
    }

    val (fromTerm, toTerm, transportProof) =
      if (!reverse) (lhs, rhs, buildSymProof(eqType, lhs, rhs, lemmaProof))
      else (rhs, lhs, lemmaProof)

    // Abstract all occurrences of `fromTerm` in `normalizedTarget` -> Var(1) inside motive (z: eqType) => (_p: Eq(eqType, toTerm, z)) => ...
    val (motiveBody, replacedCount) = abstractSubterm(
      env.kernelEnv,
      goal.localCtx,
      normalizedTarget,
      fromTerm,
      replacementVarIdx = 1,
      extraDepth = 2
    )

    if (replacedCount == 0) {
      return Left(
        Diagnostic(
          Diagnostic.Severity.Error,
          "T015",
          s"Rewrite target '${Pretty.show(fromTerm, goal.localCtx.names)}' does not occur in goal '${Pretty.show(normalizedTarget, goal.localCtx.names)}'",
          span
        )
      )
    }

    val eqType1 = Term.shift(eqType, 1)
    val toTerm1 = Term.shift(toTerm, 1)
    val motive = Term.Lam(
      "_z",
      eqType,
      Term.Lam(
        "_p",
        Term.apps(Term.Ind("Eq"), List(eqType1, toTerm1, Term.Var(0))),
        motiveBody
      )
    )

    // New goal is `motive(toTerm, Refl)`
    val newTarget = NbE.normalize(
      env.kernelEnv,
      goal.localCtx,
      Term.apps(motive, List(toTerm, Term.apps(Term.Ctor("Eq", "Refl"), List(eqType, toTerm))))
    )

    val subId = state.nextGoalId
    val subGoal = ProofGoal(subId, goal.label, goal.localCtx, newTarget)
    val nextState = state.replaceHead(
      List(subGoal),
      sols =>
        Term.Match(
          "Eq",
          List(eqType, toTerm),
          motive,
          transportProof,
          List(MatchBranch("Refl", Nil, sols(subId)))
        ),
      subId + 1
    )
    Right((env, nextState))
  }

  private def unifyWithAnySubterm(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    metaCtx: MetaContext,
    pattern: Term,
    expectedSubtermType: Term,
    target: Term
  ): Boolean = {
    val snap = metaCtx.snapshot()
    val matchedHere = TypeChecker.infer(kernelEnv, localCtx, target) match {
      case Right(inferredTy) =>
        metaCtx.unify(kernelEnv, localCtx, inferredTy, expectedSubtermType).isRight &&
          metaCtx.unify(kernelEnv, localCtx, pattern, target).isRight &&
          metaCtx.unsolvedEntries.isEmpty
      case Left(_) => false
    }
    if (matchedHere) return true
    metaCtx.restore(snap)

    target match {
      case Term.App(fn, arg) =>
        unifyWithAnySubterm(kernelEnv, localCtx, metaCtx, pattern, expectedSubtermType, fn) ||
          unifyWithAnySubterm(kernelEnv, localCtx, metaCtx, pattern, expectedSubtermType, arg)
      case Term.Match(_, ps, _, s, _) =>
        ps.exists(unifyWithAnySubterm(kernelEnv, localCtx, metaCtx, pattern, expectedSubtermType, _)) ||
          unifyWithAnySubterm(kernelEnv, localCtx, metaCtx, pattern, expectedSubtermType, s)
      case _ => false
    }
  }

  private def abstractSubterm(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    term: Term,
    needle: Term,
    replacementVarIdx: Int,
    extraDepth: Int
  ): (Term, Int) = {
    val needleNorm = NbE.normalize(kernelEnv, localCtx, needle)

    def go(cur: Term, bindDepth: Int): (Term, Int) = {
      val shiftedNeedle = Term.shift(needleNorm, bindDepth)
      if (Term.alphaEq(cur, shiftedNeedle)) {
        return (Term.Var(replacementVarIdx + bindDepth), 1)
      }
      cur match {
        case Term.USort(_) | Term.Const(_) | Term.Ind(_) | Term.Ctor(_, _) =>
          (cur, 0)
        case Term.Var(i) =>
          val shifted = if (i >= bindDepth) Term.Var(i + extraDepth) else cur
          (shifted, 0)
        case Term.App(f, a) =>
          val (f2, c1) = go(f, bindDepth)
          val (a2, c2) = go(a, bindDepth)
          (Term.App(f2, a2), c1 + c2)
        case Term.Pi(n, d, c) =>
          val (d2, c1) = go(d, bindDepth)
          val (c2, c2Cnt) = go(c, bindDepth + 1)
          (Term.Pi(n, d2, c2), c1 + c2Cnt)
        case Term.Lam(n, d, b) =>
          val (d2, c1) = go(d, bindDepth)
          val (b2, c2) = go(b, bindDepth + 1)
          (Term.Lam(n, d2, b2), c1 + c2)
        case Term.Let(n, ty, v, b) =>
          val (ty2, c1) = go(ty, bindDepth)
          val (v2, c2) = go(v, bindDepth)
          val (b2, c3) = go(b, bindDepth + 1)
          (Term.Let(n, ty2, v2, b2), c1 + c2 + c3)
        case Term.Match(ind, ps, m, s, brs) =>
          var total = 0
          val ps2 = ps.map { p => val (r, c) = go(p, bindDepth); total += c; r }
          val (m2, cm) = go(m, bindDepth); total += cm
          val (s2, cs) = go(s, bindDepth); total += cs
          val brs2 = brs.map { br =>
            val (b2, cb) = go(br.body, bindDepth + br.arity); total += cb
            br.copy(body = b2)
          }
          (Term.Match(ind, ps2, m2, s2, brs2), total)
        case Term.Fix(n, r, ty, b) =>
          val (ty2, c1) = go(ty, bindDepth)
          val (b2, c2) = go(b, bindDepth + 1)
          (Term.Fix(n, r, ty2, b2), c1 + c2)
        case Term.MutualFix(defs, sel) =>
          val k = defs.length
          var total = 0
          val defs2 = defs.map { d =>
            val (ty2, c1) = go(d.ty, bindDepth)
            val (b2, c2) = go(d.body, bindDepth + k)
            total += c1 + c2
            d.copy(ty = ty2, body = b2)
          }
          (Term.MutualFix(defs2, sel), total)
      }
    }

    go(term, 0)
  }

  private def tacticCongr(env: ElabEnv, state: ProofState, span: Span): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    extractEqGoal(env.kernelEnv, goal.localCtx, goal.targetType) match {
      case Some((eqType, lhs, rhs)) =>
        val (lHead, lArgs) = Term.splitApps(lhs)
        val (rHead, rArgs) = Term.splitApps(rhs)
        if (lHead != rHead || lArgs.length != rArgs.length || lArgs.isEmpty) {
          return Left(Diagnostic(Diagnostic.Severity.Error, "T016", "Congruence requires both sides to apply the same head function", span))
        }
        val diffIndices = lArgs.zip(rArgs).zipWithIndex.collect {
          case ((la, ra), idx) if la != ra => idx
        }
        if (diffIndices.isEmpty) {
          val reflProof = Term.apps(Term.Ctor("Eq", "Refl"), List(eqType, lhs))
          return Right((env, state.replaceHead(Nil, _ => reflProof, state.nextGoalId)))
        }
        // Handle single differing argument directly via J-elimination (multi-arg chains via first diff!)
        val diffIdx = diffIndices.head
        val aLeft = lArgs(diffIdx)
        val aRight = rArgs(diffIdx)
        val aType = TypeChecker.infer(env.kernelEnv, goal.localCtx, aLeft) match {
          case Right(t) => t
          case Left(e)  => return Left(Diagnostic(Diagnostic.Severity.Error, "T016", s"Cannot infer argument type for congr: ${e.message}", span))
        }

        // Intermediate term has `aRight` at `diffIdx` and remaining `lArgs` elsewhere
        val midArgs = lArgs.updated(diffIdx, aRight)
        val midTerm = Term.apps(lHead, midArgs)

        val eqType2 = Term.shift(eqType, 2)
        val lhs2 = Term.shift(lhs, 2)
        val aType1 = Term.shift(aType, 1)
        val aLeft1 = Term.shift(aLeft, 1)
        val ctxAppWithY = Term.apps(
          Term.shift(lHead, 2),
          lArgs.zipWithIndex.map { case (arg, i) => if (i == diffIdx) Term.Var(1) else Term.shift(arg, 2) }
        )
        val congrMotive = Term.Lam(
          "_y",
          aType,
          Term.Lam(
            "_q",
            Term.apps(Term.Ind("Eq"), List(aType1, aLeft1, Term.Var(0))),
            Term.apps(Term.Ind("Eq"), List(eqType2, lhs2, ctxAppWithY))
          )
        )

        val argSubId = state.nextGoalId
        val argSubGoal = ProofGoal(argSubId, "congr:arg", goal.localCtx, Term.apps(Term.Ind("Eq"), List(aType, aLeft, aRight)))

        if (diffIndices.length == 1) {
          val nextState = state.replaceHead(
            List(argSubGoal),
            sols =>
              Term.Match(
                "Eq",
                List(aType, aLeft),
                congrMotive,
                sols(argSubId),
                List(MatchBranch("Refl", Nil, Term.apps(Term.Ctor("Eq", "Refl"), List(eqType, lhs))))
              ),
            argSubId + 1
          )
          Right((env, nextState))
        } else {
          // Chain remaining differing arguments via transitivity!
          val restSubId = argSubId + 1
          val restSubGoal = ProofGoal(restSubId, "congr:rest", goal.localCtx, Term.apps(Term.Ind("Eq"), List(eqType, midTerm, rhs)))
          val eqType1 = Term.shift(eqType, 1)
          val mid1 = Term.shift(midTerm, 1)
          val transMotive = Term.Lam(
            "_z",
            eqType,
            Term.Lam(
              "_p",
              Term.apps(Term.Ind("Eq"), List(eqType1, mid1, Term.Var(0))),
              Term.apps(Term.Ind("Eq"), List(eqType2, lhs2, Term.Var(1)))
            )
          )
          val nextState = state.replaceHead(
            List(argSubGoal, restSubGoal),
            sols => {
              val firstEq = Term.Match(
                "Eq",
                List(aType, aLeft),
                congrMotive,
                sols(argSubId),
                List(MatchBranch("Refl", Nil, Term.apps(Term.Ctor("Eq", "Refl"), List(eqType, lhs))))
              )
              Term.Match("Eq", List(eqType, midTerm), transMotive, sols(restSubId), List(MatchBranch("Refl", Nil, firstEq)))
            },
            restSubId + 1
          )
          Right((env, nextState))
        }

      case None =>
        Left(Diagnostic(Diagnostic.Severity.Error, "T016", "Goal is not an equality ('===') for 'congr'", span))
    }
  }

  // ===========================================================================
  // Induction & Case Analysis (Generates Kernel-Checked Fix + Match Terms!)
  // ===========================================================================

  private def tacticInduction(
    env: ElabEnv,
    state: ProofState,
    targetExpr: SurfaceExpr,
    explicitCases: List[TacticCaseBranch],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] =
    inductionOrCases(env, state, targetExpr, eqHypNameOpt = None, explicitCases, withInductionHypotheses = true, span)

  private def tacticCases(
    env: ElabEnv,
    state: ProofState,
    targetExpr: SurfaceExpr,
    eqHypNameOpt: Option[String],
    explicitCases: List[TacticCaseBranch],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] =
    inductionOrCases(env, state, targetExpr, eqHypNameOpt, explicitCases, withInductionHypotheses = false, span)

  private def inductionOrCases(
    env: ElabEnv,
    state: ProofState,
    targetExpr: SurfaceExpr,
    eqHypNameOpt: Option[String],
    explicitCases: List[TacticCaseBranch],
    withInductionHypotheses: Boolean,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val metaCtx = new MetaContext()
    val (targetTerm, targetTyRaw, env1) = Elaborator.inferExpr(env, metaCtx, goal.localCtx, targetExpr) match {
      case Left(err) => return Left(err)
      case Right(r)  => r
    }
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(env1.kernelEnv, goal.localCtx, fuel)
    val targetTyVal = NbE.evaluate(env1.kernelEnv, evalEnv, metaCtx.zonk(targetTyRaw, goal.localCtx.depth), fuel)

    val (indName, paramTerms, indexTerms) = targetTyVal match {
      case Value.VInd(name, allArgs) =>
        val ind = env1.kernelEnv.inductives(name)
        val (pVals, iVals) = allArgs.splitAt(ind.numParams)
        (
          name,
          pVals.map(NbE.quote(env1.kernelEnv, goal.localCtx.depth, _, fuel)),
          iVals.map(NbE.quote(env1.kernelEnv, goal.localCtx.depth, _, fuel))
        )
      case other =>
        val quoted = NbE.quote(env1.kernelEnv, goal.localCtx.depth, other, fuel)
        return Left(
          Diagnostic(
            Diagnostic.Severity.Error,
            "T020",
            s"Target of ${if (withInductionHypotheses) "induction" else "cases"} must have an inductive type, found '${Pretty.show(quoted, goal.localCtx.names)}'",
            targetExpr.span
          )
        )
    }

    val indEntry = env1.kernelEnv.inductives(indName)
    val caseMap = explicitCases.map(c => c.ctorName -> c).toMap

    if (withInductionHypotheses) {
      if (indEntry.numIndices > 0) {
        return Left(Diagnostic(Diagnostic.Severity.Error, "T021", s"Induction on indexed family '$indName' requires non-indexed target or use 'cases'", span))
      }
      val targetVarIdx = targetTerm match {
        case Term.Var(idx) => idx
        case _ =>
          return Left(Diagnostic(Diagnostic.Severity.Error, "T022", "Target of 'induction' must be a variable in scope", targetExpr.span))
      }

      // Abstract `Var(targetVarIdx)` out of `goal.targetType`
      val indType = Term.apps(Term.Ind(indName), paramTerms)
      val varName = goal.localCtx.entries(targetVarIdx).name
      val propBody = replaceVarInTerm(Term.shift(goal.targetType, 1), targetVarIdx + 1, Term.Var(0))
      val fixName = s"_ih_$varName"
      val fixType = Term.Pi(varName, indType, propBody)

      // Context inside Fix + Lam(x): depth + 2
      val indType1 = Term.shift(indType, 1)
      val motive = Term.Lam("_s", Term.shift(indType, 2), Term.shift(propBody, 2, 1))
      val shiftedParams = paramTerms.map(Term.shift(_, 2))

      val baseBranchCtx = goal.localCtx
        .push(fixName, fixType)
        .push(s"_ind_$varName", indType1)

      val subgoals = List.newBuilder[ProofGoal]
      val branchBuilders = List.newBuilder[(CtorEntry, List[String], List[(String, Term, Term)], Int)]
      var nextId = state.nextGoalId

      for (ctor <- indEntry.constructors) {
        val explicitCaseOpt = caseMap.get(ctor.name)
        val instFields = indEntry.instantiateFields(ctor, shiftedParams)
        val recFieldIndices = ctor.fields.zipWithIndex.collect {
          case (f, i) if isRecursiveIndField(f.ty, indName) => i
        }
        val numFields = ctor.arity
        val numIHs = recFieldIndices.length

        // Assign user-provided binder names if given (fields first, then IHs!)
        val userBinders = explicitCaseOpt.map(_.binders).getOrElse(Nil)
        val fieldNames = (0 until numFields).toList.map { i =>
          if (i < userBinders.length) userBinders(i) else ctor.fields(i).name
        }
        val ihNames = (0 until numIHs).toList.map { i =>
          val userPos = numFields + i
          if (userPos < userBinders.length) userBinders(userPos)
          else if (numIHs == 1) "ih"
          else s"ih${i + 1}"
        }

        // Build branchCtx: baseBranchCtx + fields + IHs
        var branchCtx = instFields.zip(fieldNames).foldLeft(baseBranchCtx) { case (ctx, (b, n)) =>
          ctx.push(n, b.ty)
        }

        val ihDefs = List.newBuilder[(String, Term, Term)] // (ihName, ihType, ihValue)
        for ((recFieldPos, ihOrder) <- recFieldIndices.zipWithIndex) {
          val ihName = ihNames(ihOrder)
          // Current depth relative to baseBranchCtx is `numFields + ihOrder`
          // `fixName` is at index `1 + numFields + ihOrder`
          // `recFieldPos` is at index `(numFields - 1 - recFieldPos) + ihOrder`
          val fixVar = Term.Var(1 + numFields + ihOrder)
          val fieldVar = Term.Var((numFields - 1 - recFieldPos) + ihOrder)

          // Support BOTH direct recursive fields (`next: IO[A]`) AND higher-order recursive fields
          // (`cont: Nat => IO[A]`), synthesizing `ih: forall (x: Nat) => P(cont(x))`!
          val fieldTypeInBranch = Term.shift(instFields(recFieldPos).ty, (numFields - recFieldPos) + ihOrder)
          val argBinders = peelHigherOrderPiBinders(fieldTypeInBranch, indName)
          val m = argBinders.length
          val (ihTy, ihVal) =
            if (m == 0) {
              val v = Term.App(fixVar, fieldVar)
              val t = Term.subst(Term.shift(propBody, 2 + numFields + ihOrder, 1), 0, fieldVar)
              (t, v)
            } else {
              val argVars = (0 until m).toList.map(k => Term.Var(m - 1 - k))
              val appliedField = Term.apps(Term.shift(fieldVar, m), argVars)
              val bodyVal = Term.App(Term.shift(fixVar, m), appliedField)
              val bodyTy = Term.subst(Term.shift(propBody, 2 + numFields + ihOrder + m, 1), 0, appliedField)
              (Term.pis(argBinders, bodyTy), Term.lams(argBinders, bodyVal))
            }
          ihDefs += ((ihName, ihTy, ihVal))
          branchCtx = branchCtx.push(ihName, ihTy, Some(ihVal))
        }

        val rawExpectedBranchTy = indEntry.branchBodyType(ctor, shiftedParams, motive)
        val expectedBranchTy = NbE.normalize(env1.kernelEnv, branchCtx, Term.shift(rawExpectedBranchTy, numIHs))
        val subId = nextId
        nextId += 1
        subgoals += ProofGoal(subId, s"case ${ctor.name}", branchCtx, expectedBranchTy)
        branchBuilders += ((ctor, fieldNames, ihDefs.result(), subId))
      }

      val buildersList = branchBuilders.result()
      val newSubgoalsList = subgoals.result()

      val nextState = state.replaceHead(
        newSubgoalsList,
        solutions => {
          val kernelBranches = buildersList.map { case (ctor, fieldNames, ihDefs, subId) =>
            val subProof = solutions(subId)
            // Wrap subProof in nested Let bindings for each IH!
            val wrappedBody = ihDefs.foldRight(subProof) { case ((ihName, ihTy, ihVal), acc) =>
              Term.Let(ihName, ihTy, ihVal, acc)
            }
            MatchBranch(ctor.name, fieldNames, wrappedBody)
          }
          val matchTerm = Term.Match(indName, shiftedParams, motive, Term.Var(0), kernelBranches)
          val fixTerm = Term.Fix(fixName, 0, fixType, Term.Lam(s"_ind_$varName", indType1, matchTerm))
          Term.App(fixTerm, Term.Var(targetVarIdx))
        },
        nextId
      )

      runExplicitCaseBranches(env1, nextState, indEntry.constructors.map(_.name), caseMap, span)
    } else {
      // `cases(target)` without induction hypotheses
      val instIndices = indEntry.instantiateIndices(paramTerms)
      val numIdx = indEntry.numIndices
      val idxVars = (0 until numIdx).toList.map(j => Term.Var(numIdx - 1 - j))
      val scrutBinderTy = Term.apps(Term.Ind(indName), paramTerms.map(Term.shift(_, numIdx)) ++ idxVars)

      val motiveBody = {
        targetTerm match {
          case Term.Var(scrutIdx) =>
            var b = Term.shift(goal.targetType, numIdx + 1)
            b = replaceVarInTerm(b, scrutIdx + numIdx + 1, Term.Var(0))
            for ((idxT, pos) <- indexTerms.zipWithIndex) {
              idxT match {
                case Term.Var(vIdx) => b = replaceVarInTerm(b, vIdx + numIdx + 1, Term.Var(numIdx - pos))
                case _              => ()
              }
            }
            b
          case nonVarTarget =>
            val normGoal = NbE.normalize(env1.kernelEnv, goal.localCtx, goal.targetType)
            val (abstracted, _) = abstractSubterm(
              env1.kernelEnv,
              goal.localCtx,
              normGoal,
              nonVarTarget,
              replacementVarIdx = 0,
              extraDepth = numIdx + 1
            )
            abstracted
        }
      }
      val baseMotive = Term.lams(instIndices, Term.Lam("_scrut", scrutBinderTy, motiveBody))

      eqHypNameOpt match {
        case None =>
          val subgoals = List.newBuilder[ProofGoal]
          val branchBuilders = List.newBuilder[(CtorEntry, List[String], Int)]
          var nextId = state.nextGoalId

          for (ctor <- indEntry.constructors) {
            val explicitCaseOpt = caseMap.get(ctor.name)
            val instFields = indEntry.instantiateFields(ctor, paramTerms)
            val userBinders = explicitCaseOpt.map(_.binders).getOrElse(Nil)
            val fieldNames = (0 until ctor.arity).toList.map { i =>
              if (i < userBinders.length) userBinders(i) else ctor.fields(i).name
            }
            val branchCtx = instFields.zip(fieldNames).foldLeft(goal.localCtx) { case (ctx, (b, n)) =>
              ctx.push(n, b.ty)
            }
            val expectedBranchTy = NbE.normalize(env1.kernelEnv, branchCtx, indEntry.branchBodyType(ctor, paramTerms, baseMotive))
            val subId = nextId
            nextId += 1
            subgoals += ProofGoal(subId, s"case ${ctor.name}", branchCtx, expectedBranchTy)
            branchBuilders += ((ctor, fieldNames, subId))
          }

          val buildersList = branchBuilders.result()
          val nextState = state.replaceHead(
            subgoals.result(),
            solutions => {
              val kernelBranches = buildersList.map { case (ctor, fieldNames, subId) =>
                MatchBranch(ctor.name, fieldNames, solutions(subId))
              }
              Term.Match(indName, paramTerms, baseMotive, targetTerm, kernelBranches)
            },
            nextId
          )

          runExplicitCaseBranches(env1, nextState, indEntry.constructors.map(_.name), caseMap, span)

        case Some(eqHypName) =>
          // Equation-preserving case split: `cases(expr, eqHypName)`
          // Motive: (s: Ind(params)) => (eqHypName: expr === s) => Goal(s), applied to Eq.Refl(Ind(params), expr)!
          if (numIdx > 0) {
            return Left(Diagnostic(Diagnostic.Severity.Error, "T024", s"'cases(expr, $eqHypName)' currently requires a non-indexed inductive type", span))
          }
          val indTy = scrutBinderTy
          val eqBinderTy = Term.apps(Term.Ind("Eq"), List(Term.shift(indTy, 1), Term.shift(targetTerm, 1), Term.Var(0)))
          val eqMotive = Term.Lam("_scrut", indTy, Term.Pi(eqHypName, eqBinderTy, Term.shift(motiveBody, 1, 0)))

          val subgoals = List.newBuilder[ProofGoal]
          val branchBuilders = List.newBuilder[(CtorEntry, List[String], Term, Int)]
          var nextId = state.nextGoalId

          for (ctor <- indEntry.constructors) {
            val explicitCaseOpt = caseMap.get(ctor.name)
            val instFields = indEntry.instantiateFields(ctor, paramTerms)
            val userBinders = explicitCaseOpt.map(_.binders).getOrElse(Nil)
            val fieldNames = (0 until ctor.arity).toList.map { i =>
              if (i < userBinders.length) userBinders(i) else ctor.fields(i).name
            }
            val fieldCtx = instFields.zip(fieldNames).foldLeft(goal.localCtx) { case (ctx, (b, n)) =>
              ctx.push(n, b.ty)
            }
            val r = ctor.arity
            val fieldVars = (0 until r).toList.map(k => Term.Var(r - 1 - k))
            val ctorApp = Term.apps(Term.Ctor(indName, ctor.name), paramTerms.map(Term.shift(_, r)) ++ fieldVars)
            val eqHypTy = Term.apps(Term.Ind("Eq"), List(Term.shift(indTy, r), Term.shift(targetTerm, r), ctorApp))
            val branchCtx = fieldCtx.push(eqHypName, eqHypTy)

            val rawBranchGoal = Term.shift(indEntry.branchBodyType(ctor, paramTerms, baseMotive), 1)
            val expectedBranchTy = NbE.normalize(env1.kernelEnv, branchCtx, rawBranchGoal)
            val subId = nextId
            nextId += 1
            subgoals += ProofGoal(subId, s"case ${ctor.name}", branchCtx, expectedBranchTy)
            branchBuilders += ((ctor, fieldNames, eqHypTy, subId))
          }

          val buildersList = branchBuilders.result()
          val reflArg = Term.apps(Term.Ctor("Eq", "Refl"), List(indTy, targetTerm))
          val nextState = state.replaceHead(
            subgoals.result(),
            solutions => {
              val kernelBranches = buildersList.map { case (ctor, fieldNames, eqHypTy, subId) =>
                MatchBranch(ctor.name, fieldNames, Term.Lam(eqHypName, eqHypTy, solutions(subId)))
              }
              Term.App(Term.Match(indName, paramTerms, eqMotive, targetTerm, kernelBranches), reflArg)
            },
            nextId
          )

          runExplicitCaseBranches(env1, nextState, indEntry.constructors.map(_.name), caseMap, span)
      }
    }
  }

  private def tacticRevert(
    env: ElabEnv,
    state: ProofState,
    names: List[String],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = boundary {
    var curState = state
    for (varName <- names) {
      val goal = curState.openGoals.head
      val varIdx = goal.localCtx.entries.indexWhere(_.name == varName)
      if (varIdx < 0) {
        break(Left(Diagnostic(Diagnostic.Severity.Error, "T025", s"Cannot revert unknown variable '$varName'", span)))
      }
      // Revert entries 0 .. varIdx (popping inner dependent hypotheses too so context stays well-typed!)
      val poppedInnerToOuter = goal.localCtx.entries.take(varIdx + 1)
      val remainingEntries = goal.localCtx.entries.drop(varIdx + 1)
      val revertedCtx = LocalCtx(remainingEntries)
      val newTarget = poppedInnerToOuter.foldLeft(goal.targetType) { (accGoal, entry) =>
        Term.Pi(entry.name, entry.ty, accGoal)
      }
      val subId = curState.nextGoalId
      val subGoal = ProofGoal(subId, goal.label, revertedCtx, newTarget)
      val applyVars = (varIdx to 0 by -1).toList.map(Term.Var(_))
      curState = curState.replaceHead(
        List(subGoal),
        sols => Term.apps(Term.shift(sols(subId), varIdx + 1), applyVars),
        subId + 1
      )
    }
    Right((env, curState))
  }

  private def tacticExfalso(env: ElabEnv, state: ProofState, span: Span): Either[Diagnostic, (ElabEnv, ProofState)] = {
    if (!env.kernelEnv.inductives.contains("False")) {
      return Left(Diagnostic(Diagnostic.Severity.Error, "T026", "'exfalso' requires 'False' to be in scope", span))
    }
    val goal = state.openGoals.head
    val subId = state.nextGoalId
    val subGoal = ProofGoal(subId, "exfalso", goal.localCtx, Term.Ind("False"))
    val nextState = state.replaceHead(
      List(subGoal),
      sols => eliminateFalse(sols(subId), goal.targetType),
      subId + 1
    )
    Right((env, nextState))
  }

  private def tacticSubst(
    env: ElabEnv,
    state: ProofState,
    hypExpr: SurfaceExpr,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    tacticRewrite(env, state, hypExpr, reverse = false, span)
      .orElse(tacticRewrite(env, state, hypExpr, reverse = true, span))
  }

  private def tacticSpecialize(
    env: ElabEnv,
    state: ProofState,
    hypName: String,
    args: List[SurfaceExpr],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val hypIdx = goal.localCtx.entries.indexWhere(_.name == hypName)
    if (hypIdx < 0) {
      return Left(Diagnostic(Diagnostic.Severity.Error, "T027", s"Cannot specialize unknown hypothesis '$hypName'", span))
    }
    val callExpr =
      if (args.isEmpty) SurfaceExpr.VarExpr(hypName, span)
      else SurfaceExpr.CallExpr(SurfaceExpr.VarExpr(hypName, span), args, span)
    val metaCtx = new MetaContext()
    Elaborator.inferExpr(env, metaCtx, goal.localCtx, callExpr).map { case (rawTerm, rawType, nextEnv) =>
      val specTerm = metaCtx.zonk(rawTerm, goal.localCtx.depth)
      val specType = NbE.normalize(nextEnv.kernelEnv, goal.localCtx, metaCtx.zonk(rawType, goal.localCtx.depth))
      val subId = state.nextGoalId
      val subCtx = goal.localCtx.push(hypName, specType, Some(specTerm))
      val subGoal = ProofGoal(subId, goal.label, subCtx, Term.shift(goal.targetType, 1))
      val nextState = state.replaceHead(
        List(subGoal),
        sols => Term.Let(hypName, specType, specTerm, sols(subId)),
        subId + 1
      )
      (nextEnv, nextState)
    }
  }

  private def runExplicitCaseBranches(
    env: ElabEnv,
    stateAfterSplit: ProofState,
    ctorNames: List[String],
    caseMap: Map[String, TacticCaseBranch],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    if (caseMap.isEmpty) return Right((env, stateAfterSplit))
    boundary {
      var curEnv = env
      var curState = stateAfterSplit
      val goalIdsForCases = stateAfterSplit.openGoals.take(ctorNames.length).map(_.goalId)
      for ((ctorName, goalId) <- ctorNames.zip(goalIdsForCases)) {
        caseMap.get(ctorName).foreach { branch =>
          curState.focusGoal(goalId) match {
            case Some(focused) =>
              val remainingBefore = focused.openGoals.tail.map(_.goalId).toSet
              runScript(curEnv, focused, branch.body) match {
                case Left(err) => break(Left(err))
                case Right((nextEnv, afterBranch)) =>
                  curEnv = nextEnv
                  curState = afterBranch
                  val stillOpen = afterBranch.openGoals.filterNot(g => remainingBefore.contains(g.goalId))
                  if (stillOpen.nonEmpty) {
                    val msg = stillOpen.map(_.formatHuman(curEnv.kernelEnv)).mkString("\n")
                    break(Left(Diagnostic(Diagnostic.Severity.Error, "T023", s"Case '$ctorName' left unsolved goal(s):\n$msg", branch.span)))
                  }
              }
            case None => ()
          }
        }
      }
      Right((curEnv, curState))
    }
  }

  private def isRecursiveIndField(fieldTy: Term, indName: String): Boolean = fieldTy match {
    case Term.Pi(_, _, codomain) => isRecursiveIndField(codomain, indName)
    case other =>
      val (head, _) = Term.splitApps(other)
      head == Term.Ind(indName)
  }

  private def peelHigherOrderPiBinders(fieldTy: Term, indName: String): List[Binder] = fieldTy match {
    case Term.Pi(name, domain, codomain) if isRecursiveIndField(codomain, indName) =>
      val cleanName = if (name == "_" || name.isEmpty) "x" else name
      Binder(cleanName, domain) :: peelHigherOrderPiBinders(codomain, indName)
    case _ => Nil
  }

  private def replaceVarInTerm(term: Term, targetIdx: Int, replacement: Term): Term = term match {
    case Term.Var(i) if i == targetIdx => replacement
    case Term.USort(_) | Term.Var(_) | Term.Const(_) | Term.Ind(_) | Term.Ctor(_, _) => term
    case Term.Pi(n, d, c) => Term.Pi(n, replaceVarInTerm(d, targetIdx, replacement), replaceVarInTerm(c, targetIdx + 1, Term.shift(replacement, 1)))
    case Term.Lam(n, d, b) => Term.Lam(n, replaceVarInTerm(d, targetIdx, replacement), replaceVarInTerm(b, targetIdx + 1, Term.shift(replacement, 1)))
    case Term.App(f, a) => Term.App(replaceVarInTerm(f, targetIdx, replacement), replaceVarInTerm(a, targetIdx, replacement))
    case Term.Let(n, ty, v, b) =>
      Term.Let(n, replaceVarInTerm(ty, targetIdx, replacement), replaceVarInTerm(v, targetIdx, replacement), replaceVarInTerm(b, targetIdx + 1, Term.shift(replacement, 1)))
    case Term.Match(ind, ps, m, s, brs) =>
      Term.Match(
        ind,
        ps.map(replaceVarInTerm(_, targetIdx, replacement)),
        replaceVarInTerm(m, targetIdx, replacement),
        replaceVarInTerm(s, targetIdx, replacement),
        brs.map(br => br.copy(body = replaceVarInTerm(br.body, targetIdx + br.arity, Term.shift(replacement, br.arity))))
      )
    case Term.Fix(n, r, ty, b) =>
      Term.Fix(n, r, replaceVarInTerm(ty, targetIdx, replacement), replaceVarInTerm(b, targetIdx + 1, Term.shift(replacement, 1)))
    case Term.MutualFix(defs, sel) =>
      val k = defs.length
      Term.MutualFix(
        defs.map(d =>
          d.copy(
            ty = replaceVarInTerm(d.ty, targetIdx, replacement),
            body = replaceVarInTerm(d.body, targetIdx + k, Term.shift(replacement, k))
          )
        ),
        sel
      )
  }

  // ===========================================================================
  // Logical Tactics: split, left, right, exists, contradiction, discriminate, injection, have
  // ===========================================================================

  private def tacticSplit(env: ElabEnv, state: ProofState, span: Span): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(env.kernelEnv, goal.localCtx, fuel)
    NbE.evaluate(env.kernelEnv, evalEnv, goal.targetType, fuel) match {
      case Value.VInd(indName, allArgs) =>
        val indEntry = env.kernelEnv.inductives(indName)
        if (indEntry.constructors.length != 1) {
          return Left(Diagnostic(Diagnostic.Severity.Error, "T030", s"'split' requires a single-constructor type, '$indName' has ${indEntry.constructors.length}", span))
        }
        val ctor = indEntry.constructors.head
        val paramTerms = allArgs.take(indEntry.numParams).map(NbE.quote(env.kernelEnv, goal.localCtx.depth, _, fuel))
        val instFields = indEntry.instantiateFields(ctor, paramTerms)
        // Check fields are non-dependent (otherwise use `exists`)
        if (instFields.zipWithIndex.exists { case (b, i) => (0 until i).exists(j => Term.freeVarOccurs(b.ty, j)) }) {
          return Left(Diagnostic(Diagnostic.Severity.Error, "T031", s"'$indName' is dependent; use 'exists(witness)' to provide the first field", span))
        }
        val subgoals = List.newBuilder[ProofGoal]
        var nextId = state.nextGoalId
        val subIds = List.newBuilder[Int]
        for ((field, idx) <- instFields.zipWithIndex) {
          val fieldTy = Term.shift(field.ty, -idx, idx)
          val id = nextId
          nextId += 1
          subIds += id
          subgoals += ProofGoal(id, s"split:${field.name}", goal.localCtx, fieldTy)
        }
        val ids = subIds.result()
        val nextState = state.replaceHead(
          subgoals.result(),
          sols => Term.apps(Term.Ctor(indName, ctor.name), paramTerms ++ ids.map(sols)),
          nextId
        )
        Right((env, nextState))

      case _ =>
        Left(Diagnostic(Diagnostic.Severity.Error, "T030", "Goal is not an inductive type for 'split'", span))
    }
  }

  private def tacticLeftOrRight(
    env: ElabEnv,
    state: ProofState,
    isLeft: Boolean,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(env.kernelEnv, goal.localCtx, fuel)
    NbE.evaluate(env.kernelEnv, evalEnv, goal.targetType, fuel) match {
      case Value.VInd(indName, allArgs) =>
        val indEntry = env.kernelEnv.inductives(indName)
        if (indEntry.constructors.length != 2) {
          return Left(Diagnostic(Diagnostic.Severity.Error, "T032", s"'${if (isLeft) "left" else "right"}' requires a 2-constructor type (like Or)", span))
        }
        val ctor = if (isLeft) indEntry.constructors(0) else indEntry.constructors(1)
        val paramTerms = allArgs.take(indEntry.numParams).map(NbE.quote(env.kernelEnv, goal.localCtx.depth, _, fuel))
        val instFields = indEntry.instantiateFields(ctor, paramTerms)
        val subgoals = List.newBuilder[ProofGoal]
        val subIds = List.newBuilder[Int]
        var nextId = state.nextGoalId
        for ((field, idx) <- instFields.zipWithIndex) {
          val fieldTy = Term.shift(field.ty, -idx, idx)
          val id = nextId
          nextId += 1
          subIds += id
          subgoals += ProofGoal(id, if (isLeft) "left" else "right", goal.localCtx, fieldTy)
        }
        val ids = subIds.result()
        val nextState = state.replaceHead(
          subgoals.result(),
          sols => Term.apps(Term.Ctor(indName, ctor.name), paramTerms ++ ids.map(sols)),
          nextId
        )
        Right((env, nextState))

      case _ =>
        Left(Diagnostic(Diagnostic.Severity.Error, "T032", "Goal is not a disjunction type", span))
    }
  }

  private def tacticExists(
    env: ElabEnv,
    state: ProofState,
    witnessExpr: SurfaceExpr,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(env.kernelEnv, goal.localCtx, fuel)
    NbE.evaluate(env.kernelEnv, evalEnv, goal.targetType, fuel) match {
      case Value.VInd(indName, allArgs) =>
        val indEntry = env.kernelEnv.inductives(indName)
        if (indEntry.constructors.length != 1 || indEntry.constructors.head.arity != 2) {
          return Left(Diagnostic(Diagnostic.Severity.Error, "T033", s"'exists' requires a 1-constructor, 2-field existential/sigma type, got '$indName'", span))
        }
        val ctor = indEntry.constructors.head
        val paramTerms = allArgs.take(indEntry.numParams).map(NbE.quote(env.kernelEnv, goal.localCtx.depth, _, fuel))
        val instFields = indEntry.instantiateFields(ctor, paramTerms)
        val witnessTy = instFields(0).ty
        val metaCtx = new MetaContext()
        Elaborator.checkExpr(env, metaCtx, goal.localCtx, witnessExpr, witnessTy).map { case (witnessRaw, nextEnv) =>
          val witness = metaCtx.zonk(witnessRaw, goal.localCtx.depth)
          val proofTy = NbE.normalize(nextEnv.kernelEnv, goal.localCtx, Term.subst(instFields(1).ty, 0, witness))
          val subId = state.nextGoalId
          val subGoal = ProofGoal(subId, "exists:proof", goal.localCtx, proofTy)
          val nextState = state.replaceHead(
            List(subGoal),
            sols => Term.apps(Term.Ctor(indName, ctor.name), paramTerms ++ List(witness, sols(subId))),
            subId + 1
          )
          (nextEnv, nextState)
        }
      case _ =>
        Left(Diagnostic(Diagnostic.Severity.Error, "T033", "Goal is not an existential type for 'exists'", span))
    }
  }

  private def eliminateFalse(falseProof: Term, targetType: Term): Term =
    Term.Match(
      "False",
      Nil,
      Term.Lam("_f", Term.Ind("False"), Term.shift(targetType, 1)),
      falseProof,
      Nil
    )

  private def tacticContradiction(
    env: ElabEnv,
    state: ProofState,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = boundary {
    val goal = state.openGoals.head
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(env.kernelEnv, goal.localCtx, fuel)

    // 1. Direct `h : False` in context
    for (idx <- goal.localCtx.entries.indices) {
      val hypTy = goal.localCtx.lookupType(idx).get
      NbE.evaluate(env.kernelEnv, evalEnv, hypTy, fuel) match {
        case Value.VInd("False", Nil) =>
          val proof = eliminateFalse(Term.Var(idx), goal.targetType)
          break(Right((env, state.replaceHead(Nil, _ => proof, state.nextGoalId))))
        case _ => ()
      }
    }

    // 2. Pair `h1 : P` and `h2 : P => False` (i.e. Not(P))
    for (i <- goal.localCtx.entries.indices) {
      val tyI = goal.localCtx.lookupType(i).get
      val valI = NbE.evaluate(env.kernelEnv, evalEnv, tyI, fuel)
      valI match {
        case Value.VPi(_, domVal, codClosure) =>
          val fresh = Value.VNeutral(NeutralHead.NVar(goal.localCtx.depth), Nil)
          NbE.applyClosure(env.kernelEnv, codClosure, fresh, fuel) match {
            case Value.VInd("False", Nil) =>
              for (j <- goal.localCtx.entries.indices) {
                val valJ = NbE.evaluate(env.kernelEnv, evalEnv, goal.localCtx.lookupType(j).get, fuel)
                if (NbE.isSubtype(env.kernelEnv, goal.localCtx.depth, valJ, domVal, fuel)) {
                  val falseProof = Term.App(Term.Var(i), Term.Var(j))
                  val proof = eliminateFalse(falseProof, goal.targetType)
                  break(Right((env, state.replaceHead(Nil, _ => proof, state.nextGoalId))))
                }
              }
            case _ => ()
          }
        case _ => ()
      }
    }

    // 3. Impossible constructor equality `h : C1(...) === C2(...)`
    tacticDiscriminate(env, state, None, span).left.map { _ =>
      Diagnostic(Diagnostic.Severity.Error, "T034", "Could not find a contradiction in the current context", span)
    }
  }

  private def tacticDiscriminate(
    env: ElabEnv,
    state: ProofState,
    hypOpt: Option[SurfaceExpr],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = boundary {
    val goal = state.openGoals.head
    val candidates: List[(Term, Term)] = hypOpt match {
      case Some(expr) =>
        val metaCtx = new MetaContext()
        Elaborator.inferExpr(env, metaCtx, goal.localCtx, expr) match {
          case Left(err)        => break(Left(err))
          case Right((t, ty, _)) => List((metaCtx.zonk(t, goal.localCtx.depth), metaCtx.zonk(ty, goal.localCtx.depth)))
        }
      case None =>
        goal.localCtx.entries.indices.toList.map(i => (Term.Var(i), goal.localCtx.lookupType(i).get))
    }

    for ((hypTerm, hypTy) <- candidates) {
      extractEqGoal(env.kernelEnv, goal.localCtx, hypTy).foreach { case (eqType, lhs, rhs) =>
        val (lHead, _) = Term.splitApps(lhs)
        val (rHead, _) = Term.splitApps(rhs)
        (lHead, rHead) match {
          case (Term.Ctor(indName, c1), Term.Ctor(indName2, c2)) if indName == indName2 && c1 != c2 =>
            val indEntry = env.kernelEnv.inductives(indName)
            val (_, eqTyArgs) = Term.splitApps(NbE.normalize(env.kernelEnv, goal.localCtx, eqType))
            val indParams = eqTyArgs.take(indEntry.numParams)

            // Build discriminator: (x: Ind) => x match { case c1(...) => True; case _ => False }
            val discMotive = Term.Lam("_d", Term.shift(eqType, 1), Term.USort(Sort.Prop))
            val discBranches = indEntry.constructors.map { ctor =>
              val body = if (ctor.name == c1) Term.Ind("True") else Term.Ind("False")
              MatchBranch(ctor.name, ctor.fields.map(_.name), body)
            }
            val eqType1 = Term.shift(eqType, 1)
            val lhs1 = Term.shift(lhs, 1)
            val discBody = Term.Match(
              indName,
              indParams.map(Term.shift(_, 2)),
              Term.shift(discMotive, 1),
              Term.Var(1), // _y
              discBranches
            )
            val eqMotive = Term.Lam(
              "_y",
              eqType,
              Term.Lam(
                "_q",
                Term.apps(Term.Ind("Eq"), List(eqType1, lhs1, Term.Var(0))),
                discBody
              )
            )
            val falseProof = Term.Match(
              "Eq",
              List(eqType, lhs),
              eqMotive,
              hypTerm,
              List(MatchBranch("Refl", Nil, Term.Ctor("True", "Intro")))
            )
            val finalProof = eliminateFalse(falseProof, goal.targetType)
            break(Right((env, state.replaceHead(Nil, _ => finalProof, state.nextGoalId))))
          case _ => ()
        }
      }
    }

    Left(Diagnostic(Diagnostic.Severity.Error, "T035", "No conflicting constructor equality found for 'discriminate'", span))
  }

  private def tacticInjection(
    env: ElabEnv,
    state: ProofState,
    hypExpr: SurfaceExpr,
    names: List[String],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val metaCtx = new MetaContext()
    val (hypTerm, hypTy, env1) = Elaborator.inferExpr(env, metaCtx, goal.localCtx, hypExpr) match {
      case Left(err) => return Left(err)
      case Right(r)  => r
    }
    extractEqGoal(env1.kernelEnv, goal.localCtx, metaCtx.zonk(hypTy, goal.localCtx.depth)) match {
      case Some((eqType, lhs, rhs)) =>
        val (lHead, lArgs) = Term.splitApps(lhs)
        val (rHead, rArgs) = Term.splitApps(rhs)
        (lHead, rHead) match {
          case (Term.Ctor(indName, c1), Term.Ctor(indName2, c2)) if indName == indName2 && c1 == c2 =>
            val indEntry = env1.kernelEnv.inductives(indName)
            val ctor = indEntry.ctor(c1).get
            val indParams = lArgs.take(indEntry.numParams)
            val lFields = lArgs.drop(indEntry.numParams)
            val rFields = rArgs.drop(indEntry.numParams)
            val instFields = indEntry.instantiateFields(ctor, indParams)

            var curCtx = goal.localCtx
            val letBindings = List.newBuilder[(String, Term, Term)]
            var shiftCount = 0

            for (fieldPos <- 0 until ctor.arity) {
              // Skip dependent fields that reference earlier fields
              val rawFieldTy = instFields(fieldPos).ty
              if (!(0 until fieldPos).exists(j => Term.freeVarOccurs(rawFieldTy, j))) {
                val fieldTy = Term.shift(rawFieldTy, -fieldPos, fieldPos)
                val aVal = lFields(fieldPos)
                val bVal = rFields(fieldPos)
                val injName = if (fieldPos < names.length) names(fieldPos) else s"inj_${fieldPos}"

                // Build projection proj(x) = x match { case c1(f...) => f_fieldPos; case _ => aVal }
                val projMotive = Term.Lam("_p", Term.shift(eqType, 1), Term.shift(fieldTy, 2))
                val projBranches = indEntry.constructors.map { ct =>
                  val body =
                    if (ct.name == c1) Term.Var(ct.arity - 1 - fieldPos)
                    else Term.shift(aVal, ct.arity)
                  MatchBranch(ct.name, ct.fields.map(_.name), body)
                }
                def projOf(x: Term, depthShift: Int): Term =
                  Term.Match(
                    indName,
                    indParams.map(Term.shift(_, depthShift)),
                    Term.Lam("_p", Term.shift(eqType, depthShift), Term.shift(fieldTy, depthShift + 1)),
                    x,
                    projBranches.map(br =>
                      if (br.ctorName == c1) br
                      else br.copy(body = Term.shift(aVal, depthShift + br.arity))
                    )
                  )
                val _ = projMotive

                val eqMotive = Term.Lam(
                  "_y",
                  eqType,
                  Term.Lam(
                    "_q",
                    Term.apps(Term.Ind("Eq"), List(Term.shift(eqType, 1), Term.shift(lhs, 1), Term.Var(0))),
                    Term.apps(Term.Ind("Eq"), List(Term.shift(fieldTy, 2), Term.shift(aVal, 2), projOf(Term.Var(1), 2)))
                  )
                )
                val fieldEqProof = Term.Match(
                  "Eq",
                  List(eqType, lhs),
                  eqMotive,
                  hypTerm,
                  List(MatchBranch("Refl", Nil, Term.apps(Term.Ctor("Eq", "Refl"), List(fieldTy, aVal))))
                )
                val fieldEqType = Term.apps(Term.Ind("Eq"), List(fieldTy, aVal, bVal))

                val shiftedTy = Term.shift(fieldEqType, shiftCount)
                val shiftedPf = Term.shift(fieldEqProof, shiftCount)
                letBindings += ((injName, shiftedTy, shiftedPf))
                curCtx = curCtx.push(injName, shiftedTy, Some(shiftedPf))
                shiftCount += 1
              }
            }

            val lets = letBindings.result()
            val subId = state.nextGoalId
            val subGoal = ProofGoal(subId, goal.label, curCtx, Term.shift(goal.targetType, shiftCount))
            val nextState = state.replaceHead(
              List(subGoal),
              sols => lets.foldRight(sols(subId)) { case ((n, ty, pf), acc) => Term.Let(n, ty, pf, acc) },
              subId + 1
            )
            Right((env1, nextState))

          case _ =>
            Left(Diagnostic(Diagnostic.Severity.Error, "T036", "'injection' requires equality between identical constructors", span))
        }
      case None =>
        Left(Diagnostic(Diagnostic.Severity.Error, "T036", "'injection' requires an equality hypothesis", span))
    }
  }

  private def tacticHave(
    env: ElabEnv,
    state: ProofState,
    hypName: String,
    propTypeExpr: SurfaceExpr,
    proofStmts: List[TacticStmt],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val metaCtx = new MetaContext()
    Elaborator.elaborateType(env, metaCtx, goal.localCtx, propTypeExpr).flatMap { rawPropTy =>
      val propTy = metaCtx.zonk(rawPropTy, goal.localCtx.depth)
      val haveState = ProofState.initial(goal.localCtx, propTy, label = s"have:$hypName")
      runScript(env, haveState, proofStmts).flatMap { case (nextEnv, doneHave) =>
        if (!doneHave.isSolved) {
          val msg = doneHave.openGoals.map(_.formatHuman(nextEnv.kernelEnv)).mkString("\n")
          Left(Diagnostic(Diagnostic.Severity.Error, "T037", s"'have($hypName)' proof incomplete:\n$msg", span))
        } else {
          doneHave.buildProofTerm match {
            case Left(err) => Left(Diagnostic(Diagnostic.Severity.Error, "T037", err, span))
            case Right(haveProof) =>
              val subId = state.nextGoalId
              val subCtx = goal.localCtx.push(hypName, propTy, Some(haveProof))
              val subGoal = ProofGoal(subId, goal.label, subCtx, Term.shift(goal.targetType, 1))
              val nextState = state.replaceHead(
                List(subGoal),
                sols => Term.Let(hypName, propTy, haveProof, sols(subId)),
                subId + 1
              )
              Right((nextEnv, nextState))
          }
        }
      }
    }
  }

  // ===========================================================================
  // Simplification & Decision Tactics: unfold, simp, trivial, decide, sorry, hole
  // ===========================================================================

  private def tacticUnfold(
    env: ElabEnv,
    state: ProofState,
    defName: String,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    if (!env.kernelEnv.defs.contains(defName)) {
      return Left(Diagnostic(Diagnostic.Severity.Error, "T040", s"Cannot unfold unknown definition '$defName'", span))
    }
    val goal = state.openGoals.head
    val normalized = NbE.normalize(env.kernelEnv, goal.localCtx, goal.targetType)
    val subId = state.nextGoalId
    val subGoal = ProofGoal(subId, goal.label, goal.localCtx, normalized)
    Right((env, state.replaceHead(List(subGoal), sols => sols(subId), subId + 1)))
  }

  private def tacticSimpTarget(
    env: ElabEnv,
    state: ProofState,
    extraLemmas: List[SurfaceExpr],
    includeLocalHyps: Boolean,
    target: Option[String],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = target match {
    case None =>
      tacticSimp(env, state, extraLemmas, includeLocalHyps, span)
    case Some("*") =>
      var curEnv = env
      var curState = state
      val hypNames = curState.openGoals.head.localCtx.entries.map(_.name).distinct
      for (hName <- hypNames if !curState.isSolved) {
        tacticSimpInHyp(curEnv, curState, extraLemmas, includeLocalHyps, hName, span) match {
          case Right((nextEnv, nextState)) =>
            curEnv = nextEnv; curState = nextState
          case Left(_) => ()
        }
      }
      if (curState.isSolved) Right((curEnv, curState))
      else tacticSimp(curEnv, curState, extraLemmas, includeLocalHyps, span)
    case Some(hypName) =>
      tacticSimpInHyp(env, state, extraLemmas, includeLocalHyps, hypName, span)
  }

  private def tacticSimpInHyp(
    env: ElabEnv,
    state: ProofState,
    extraLemmas: List[SurfaceExpr],
    includeLocalHyps: Boolean,
    hypName: String,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal0 = state.openGoals.head
    val (hypIdx0, rawTy0) = lookupHyp(goal0.localCtx, hypName) match {
      case Some(pair) => pair
      case None =>
        return Left(Diagnostic(Diagnostic.Severity.Error, "T040", s"Unknown hypothesis '$hypName' in 'simp in $hypName'", span))
    }

    var curEnv = env
    var curState = state

    // 1. Normalize hypothesis type via NbE if it simplifies
    val normTy0 = NbE.normalize(env.kernelEnv, goal0.localCtx, rawTy0)
    if (normTy0 != rawTy0) {
      val subId = curState.nextGoalId
      val subCtx = goal0.localCtx.push(hypName, normTy0, Some(Term.Var(hypIdx0)))
      val subGoal = ProofGoal(subId, goal0.label, subCtx, Term.shift(goal0.targetType, 1))
      curState = curState.replaceHead(
        List(subGoal),
        sols => Term.Let(hypName, normTy0, Term.Var(hypIdx0), sols(subId)),
        subId + 1
      )
    }

    // 2. Repeatedly rewrite hypothesis using extras, optional local Eq hypotheses, and @simp lemmas
    var progress = true
    var rounds = 0
    while (progress && rounds < 12 && !curState.isSolved) {
      progress = false
      rounds += 1

      for (extra <- extraLemmas if !curState.isSolved && !progress) {
        tacticRewriteInHyp(curEnv, curState, extra, reverse = false, hypName, span) match {
          case Right((nextEnv, nextState)) =>
            curEnv = nextEnv; curState = nextState; progress = true
          case Left(_) => ()
        }
      }

      if (includeLocalHyps && !curState.isSolved && !progress) {
        val g = curState.openGoals.head
        val curHypIdx = lookupHyp(g.localCtx, hypName).map(_._1).getOrElse(-1)
        for (idx <- g.localCtx.entries.indices if idx != curHypIdx && !curState.isSolved && !progress) {
          val eqHypTy = g.localCtx.lookupType(idx).get
          extractEqGoal(curEnv.kernelEnv, g.localCtx, eqHypTy).foreach { case (_, lhs, rhs) =>
            val lhsStr = Pretty.show(lhs, g.localCtx.names)
            val rhsStr = Pretty.show(rhs, g.localCtx.names)
            if (lhs != rhs && !rhsStr.contains(lhsStr)) {
              val metaCtx = new MetaContext()
              rewriteInHypWithCoreLemma(curEnv, curState, g, metaCtx, Term.Var(idx), eqHypTy, reverse = false, hypName, span) match {
                case Right((nextEnv, nextState)) =>
                  curEnv = nextEnv; curState = nextState; progress = true
                case Left(_) => ()
              }
            }
          }
        }
      }

      for (simpName <- curEnv.simpLemmas if !curState.isSolved && !progress) {
        curEnv.kernelEnv.lookupConstType(simpName).foreach { lemmaTy =>
          val metaCtx = new MetaContext()
          val g = curState.openGoals.head
          rewriteInHypWithCoreLemma(curEnv, curState, g, metaCtx, Term.Const(simpName), lemmaTy, reverse = false, hypName, span) match {
            case Right((nextEnv, nextState)) =>
              curEnv = nextEnv; curState = nextState; progress = true
            case Left(_) => ()
          }
        }
      }
    }

    Right((curEnv, curState))
  }

  private def tacticSimp(
    env: ElabEnv,
    state: ProofState,
    extraLemmas: List[SurfaceExpr],
    includeLocalHyps: Boolean,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head

    // 1. First normalize via NbE (beta, delta, iota, zeta)
    val normTarget = NbE.normalize(env.kernelEnv, goal.localCtx, goal.targetType)
    var curEnv = env
    var curState = {
      val subId = state.nextGoalId
      val subGoal = ProofGoal(subId, goal.label, goal.localCtx, normTarget)
      state.replaceHead(List(subGoal), sols => sols(subId), subId + 1)
    }

    // 2. Repeatedly rewrite with extra lemmas, optional local Eq hypotheses (`simp(*)`), and @simp lemmas
    var progress = true
    var rounds = 0
    while (progress && rounds < 12 && !curState.isSolved) {
      progress = false
      rounds += 1

      // Try explicit extra lemmas first
      for (extra <- extraLemmas if !curState.isSolved && !progress) {
        tacticRewrite(curEnv, curState, extra, reverse = false, span) match {
          case Right((nextEnv, nextState)) =>
            curEnv = nextEnv; curState = nextState; progress = true
          case Left(_) => ()
        }
      }

      // Optionally rewrite using local equality hypotheses (`simp(*)`)
      if (includeLocalHyps && !curState.isSolved && !progress) {
        val g = curState.openGoals.head
        for (idx <- g.localCtx.entries.indices if !curState.isSolved && !progress) {
          val hypTy = g.localCtx.lookupType(idx).get
          extractEqGoal(curEnv.kernelEnv, g.localCtx, hypTy).foreach { case (_, lhs, rhs) =>
            // Guard against trivial or cyclic rewrites (e.g. x === f(x))
            val lhsStr = Pretty.show(lhs, g.localCtx.names)
            val rhsStr = Pretty.show(rhs, g.localCtx.names)
            if (lhs != rhs && !rhsStr.contains(lhsStr)) {
              val metaCtx = new MetaContext()
              rewriteWithCoreLemma(curEnv, curState, g, metaCtx, Term.Var(idx), hypTy, reverse = false, span) match {
                case Right((nextEnv, nextState)) =>
                  curEnv = nextEnv; curState = nextState; progress = true
                case Left(_) => ()
              }
            }
          }
        }
      }

      // Try registered @simp lemmas
      for (simpName <- curEnv.simpLemmas if !curState.isSolved && !progress) {
        curEnv.kernelEnv.lookupConstType(simpName).foreach { lemmaTy =>
          val metaCtx = new MetaContext()
          val g = curState.openGoals.head
          rewriteWithCoreLemma(curEnv, curState, g, metaCtx, Term.Const(simpName), lemmaTy, reverse = false, span) match {
            case Right((nextEnv, nextState)) =>
              curEnv = nextEnv; curState = nextState; progress = true
            case Left(_) => ()
          }
        }
      }
    }

    // 3. Auto-close if goal is now trivially `x === x` or `True`!
    if (!curState.isSolved) {
      val g = curState.openGoals.head
      tacticRefl(curEnv, curState, span) match {
        case Right(done) => return Right(done)
        case Left(_) =>
          val norm = NbE.normalize(curEnv.kernelEnv, g.localCtx, g.targetType)
          if (norm == Term.Ind("True") && curEnv.kernelEnv.inductives.contains("True")) {
            return Right((curEnv, curState.replaceHead(Nil, _ => Term.Ctor("True", "Intro"), curState.nextGoalId)))
          }
      }
    }

    Right((curEnv, curState))
  }

  def tacticTrivial(env: ElabEnv, state: ProofState, span: Span): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val norm = NbE.normalize(env.kernelEnv, goal.localCtx, goal.targetType)
    if (norm == Term.Ind("True") && env.kernelEnv.inductives.contains("True")) {
      return Right((env, state.replaceHead(Nil, _ => Term.Ctor("True", "Intro"), state.nextGoalId)))
    }
    tacticRefl(env, state, span)
      .orElse(tacticAssumption(env, state, span))
      .orElse(tacticContradiction(env, state, span))
      .left
      .map(_ => Diagnostic(Diagnostic.Severity.Error, "T041", "Goal could not be solved by 'trivial'", span))
  }

  private def tacticDecide(env: ElabEnv, state: ProofState, span: Span): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    decideTerm(env.kernelEnv, goal.localCtx, goal.targetType) match {
      case Some(proof) => Right((env, state.replaceHead(Nil, _ => proof, state.nextGoalId)))
      case None =>
        tacticTrivial(env, state, span).left.map { _ =>
          Diagnostic(
            Diagnostic.Severity.Error,
            "T042",
            s"'decide' could not computationally decide '${Pretty.show(NbE.normalize(env.kernelEnv, goal.localCtx, goal.targetType), goal.localCtx.names)}'",
            span
          )
        }
    }
  }

  private def decideTerm(kernelEnv: KernelEnv, localCtx: LocalCtx, targetType: Term): Option[Term] = {
    val norm = NbE.normalize(kernelEnv, localCtx, targetType)
    val (head, args) = Term.splitApps(norm)
    head match {
      case Term.Ind("True") =>
        Some(Term.Ctor("True", "Intro"))

      case Term.Ind("Eq") if args.length == 3 =>
        val fuel = new NbE.Fuel()
        val evalEnv = NbE.buildEvalEnv(kernelEnv, localCtx, fuel)
        val v1 = NbE.evaluate(kernelEnv, evalEnv, args(1), fuel)
        val v2 = NbE.evaluate(kernelEnv, evalEnv, args(2), fuel)
        if (NbE.areConvertible(kernelEnv, localCtx.depth, v1, v2, fuel)) {
          Some(Term.apps(Term.Ctor("Eq", "Refl"), List(args(0), args(1))))
        } else None

      case Term.Ind("And") if args.length == 2 =>
        for {
          p1 <- decideTerm(kernelEnv, localCtx, args(0))
          p2 <- decideTerm(kernelEnv, localCtx, args(1))
        } yield Term.apps(Term.Ctor("And", "Intro"), List(args(0), args(1), p1, p2))

      case Term.Ind("Or") if args.length == 2 =>
        decideTerm(kernelEnv, localCtx, args(0))
          .map(p => Term.apps(Term.Ctor("Or", "Inl"), List(args(0), args(1), p)))
          .orElse(
            decideTerm(kernelEnv, localCtx, args(1))
              .map(p => Term.apps(Term.Ctor("Or", "Inr"), List(args(0), args(1), p)))
          )

      case Term.Ind("Le") if args.length == 2 =>
        (extractNatLit(args(0)), extractNatLit(args(1))) match {
          case (Some(m), Some(n)) if m <= n =>
            def buildLe(curN: Int): Term =
              if (curN == m) Term.App(Term.Ctor("Le", "Refl"), buildNatTerm(m))
              else Term.apps(Term.Ctor("Le", "Step"), List(buildNatTerm(m), buildNatTerm(curN - 1), buildLe(curN - 1)))
            Some(buildLe(n))
          case _ => None
        }

      case Term.Ind("Iff") if args.length == 2 =>
        for {
          p1 <- decideTerm(kernelEnv, localCtx, Term.Pi("_", args(0), Term.shift(args(1), 1)))
          p2 <- decideTerm(kernelEnv, localCtx, Term.Pi("_", args(1), Term.shift(args(0), 1)))
        } yield Term.apps(Term.Ctor("Iff", "Intro"), List(args(0), args(1), p1, p2))

      case _ =>
        // Check `Not(P)` (`P => False`): try discriminate first, then OmegaTactic for concrete false inequalities like `~Le(5, 2)`!
        norm match {
          case Term.Pi(n, dom, Term.Ind("False")) =>
            val subState = ProofState.initial(localCtx.push(n, dom), Term.Ind("False"))
            tacticDiscriminate(ElabEnv(kernelEnv = kernelEnv), subState, None, Span.synthetic) match {
              case Right((_, done)) if done.isSolved =>
                done.buildProofTerm.toOption.map(body => Term.Lam(n, dom, body))
              case _ =>
                OmegaTactic.solveGoal(kernelEnv, localCtx, norm)
            }
          case _ => None
        }
    }
  }

  // ===========================================================================
  // Practical Combinators & Ergonomic Tactics:
  // obtain, rename, tauto, try, repeat, all, first, <;>
  // ===========================================================================

  private def tacticObtain(
    env: ElabEnv,
    state: ProofState,
    binders: List[String],
    source: SurfaceExpr,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val metaCtx = new MetaContext()
    Elaborator.inferExpr(env, metaCtx, goal.localCtx, source).flatMap { case (rawTerm, rawType, nextEnv) =>
      val term = metaCtx.zonk(rawTerm, goal.localCtx.depth)
      val ty = NbE.normalize(nextEnv.kernelEnv, goal.localCtx, metaCtx.zonk(rawType, goal.localCtx.depth))
      val (head, args) = Term.splitApps(ty)
      head match {
        case Term.Ind(indName) =>
          nextEnv.kernelEnv.inductives.get(indName) match {
            case Some(ind) if ind.constructors.length == 1 && ind.numIndices == 0 =>
              val ctor = ind.constructors.head
              if (binders.length < ctor.arity) {
                Left(
                  Diagnostic(
                    Diagnostic.Severity.Error,
                    "T072",
                    s"'obtain' on '$indName' requires at least ${ctor.arity} binder(s), got ${binders.length}",
                    span
                  )
                )
              } else {
                val params = args.take(ind.numParams)
                val fieldBinders = ind.instantiateFields(ctor, params)

                // If user supplied extra binders (e.g. `obtain(a, b, c) = h` on `A /\ (B /\ C)`),
                // bind the last field temporarily and recursively destruct it!
                val (directNames, tailBinders) =
                  if (binders.length == ctor.arity) (binders, Nil)
                  else {
                    val tempName = s"_obt_${state.nextGoalId}"
                    (binders.take(ctor.arity - 1) :+ tempName, binders.drop(ctor.arity - 1))
                  }

                val arity = ctor.arity
                val subCtx = fieldBinders.zip(directNames).foldLeft(goal.localCtx) { case (c, (b, n)) =>
                  c.push(n, b.ty)
                }
                val subId = state.nextGoalId
                val subGoal = ProofGoal(subId, goal.label, subCtx, Term.shift(goal.targetType, arity))
                val motive = Term.Lam("_obt", ty, Term.shift(goal.targetType, 1))
                val nextState = state.replaceHead(
                  List(subGoal),
                  sols => Term.Match(indName, params, motive, term, List(MatchBranch(ctor.name, directNames, sols(subId)))),
                  subId + 1
                )
                if (tailBinders.isEmpty) {
                  Right((nextEnv, nextState))
                } else {
                  val tempName = directNames.last
                  tacticObtain(nextEnv, nextState, tailBinders, SurfaceExpr.VarExpr(tempName, span), span)
                }
              }

            case Some(_) =>
              Left(Diagnostic(Diagnostic.Severity.Error, "T072", s"'obtain' requires a single-constructor type (And, Exists, Iff, Pair, Subset), found '$indName'", span))
            case None =>
              Left(Diagnostic(Diagnostic.Severity.Error, "T072", s"Unknown inductive type '$indName' in 'obtain'", span))
          }
        case _ =>
          Left(Diagnostic(Diagnostic.Severity.Error, "T072", s"'obtain' expected an inductive type, found '${Pretty.show(ty, goal.localCtx.names)}'", span))
      }
    }
  }

  private def tacticRename(
    env: ElabEnv,
    state: ProofState,
    oldName: String,
    newName: String,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val idx = goal.localCtx.entries.indexWhere(_.name == oldName)
    if (idx < 0) {
      return Left(Diagnostic(Diagnostic.Severity.Error, "T073", s"Cannot rename unknown hypothesis '$oldName'", span))
    }
    val updatedEntries = goal.localCtx.entries.updated(idx, goal.localCtx.entries(idx).copy(name = newName))
    val subId = state.nextGoalId
    val subGoal = ProofGoal(subId, goal.label, LocalCtx(updatedEntries), goal.targetType)
    Right((env, state.replaceHead(List(subGoal), sols => sols(subId), subId + 1)))
  }

  private def runOnSelectedGoals(
    env: ElabEnv,
    state: ProofState,
    targetGoalIds: List[Int],
    body: List[TacticStmt]
  ): Either[Diagnostic, (ElabEnv, ProofState)] = boundary {
    var curEnv = env
    var curState = state
    for (gid <- targetGoalIds) {
      curState.focusGoal(gid) match {
        case None => ()
        case Some(focused) =>
          val g = focused.openGoals.head
          val singleInit = ProofState.initial(g.localCtx, g.targetType, g.label)
          runScript(curEnv, singleInit, body) match {
            case Left(err) => break(Left(err))
            case Right((nextEnv, singleAfter)) =>
              val idOffset = curState.nextGoalId
              val rebasedSubgoals = singleAfter.openGoals.map(sg => sg.copy(goalId = sg.goalId + idOffset))
              val nextNextId = idOffset + singleAfter.nextGoalId
              val nextState = focused.replaceHead(
                rebasedSubgoals,
                sols => {
                  val localSols = singleAfter.openGoals.map(sg => sg.goalId -> sols(sg.goalId + idOffset)).toMap
                  singleAfter.reconstruct(localSols)
                },
                nextNextId,
                markSorry = singleAfter.usedSorry
              )
              curEnv = nextEnv
              curState = nextState
          }
      }
    }
    Right((curEnv, curState))
  }

  private def tacticSeqAll(
    env: ElabEnv,
    state: ProofState,
    first: TacticStmt,
    after: TacticStmt,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val _ = span
    val tailGoalIds = state.openGoals.tail.map(_.goalId).toSet
    step(env, state, first).flatMap { case (env1, state1) =>
      val newSubgoalIds = state1.openGoals.map(_.goalId).filterNot(tailGoalIds.contains)
      if (newSubgoalIds.isEmpty) Right((env1, state1))
      else runOnSelectedGoals(env1, state1, newSubgoalIds, List(after))
    }
  }

  private def tacticAllGoals(
    env: ElabEnv,
    state: ProofState,
    body: List[TacticStmt],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val _ = span
    runOnSelectedGoals(env, state, state.openGoals.map(_.goalId), body)
  }

  private def tacticTry(
    env: ElabEnv,
    state: ProofState,
    body: List[TacticStmt],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val _ = span
    val headId = state.openGoals.head.goalId
    runOnSelectedGoals(env, state, List(headId), body) match {
      case Right(res) => Right(res)
      case Left(_)    => Right((env, state))
    }
  }

  private def tacticRepeat(
    env: ElabEnv,
    state: ProofState,
    body: List[TacticStmt],
    maxSteps: Int,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val _ = span
    var curEnv = env
    var curState = state
    var steps = 0
    var continuing = true
    while (continuing && steps < maxSteps && !curState.isSolved) {
      val prevGoal = curState.openGoals.head
      val prevCount = curState.openGoals.length
      runOnSelectedGoals(curEnv, curState, List(prevGoal.goalId), body) match {
        case Right((nextEnv, nextState)) =>
          val unchanged =
            nextState.openGoals.length == prevCount &&
              nextState.openGoals.headOption.exists(g => g.targetType == prevGoal.targetType && g.localCtx == prevGoal.localCtx)
          if (unchanged) {
            continuing = false
          } else {
            curEnv = nextEnv
            curState = nextState
            steps += 1
          }
        case Left(_) =>
          continuing = false
      }
    }
    Right((curEnv, curState))
  }

  private def tacticFirst(
    env: ElabEnv,
    state: ProofState,
    branches: List[List[TacticStmt]],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = boundary {
    val headId = state.openGoals.head.goalId
    for (br <- branches) {
      runOnSelectedGoals(env, state, List(headId), br) match {
        case Right(res) => break(Right(res))
        case Left(_)    => ()
      }
    }
    Left(Diagnostic(Diagnostic.Severity.Error, "T074", "All branches of 'first { ... }' failed", span))
  }

  /**
   * Complete intuitionistic propositional logic solver (`tauto`) with 0 axioms.
   * Handles `True`, `False`, `And`, `Or`, `Iff`, `Not`, `=>`, hypothesis splitting,
   * forward Modus Ponens saturation, and backtracking disjunction/implication search.
   */
  def tacticTauto(env: ElabEnv, state: ProofState, span: Span): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val single = ProofState.initial(goal.localCtx, goal.targetType, goal.label)
    tautoSearch(env, single, depth = 10, destructedLevels = Set.empty, span) match {
      case Some((nextEnv, solved)) if solved.isSolved =>
        solved.buildProofTerm match {
          case Right(pt) => Right((nextEnv, state.replaceHead(Nil, _ => pt, state.nextGoalId)))
          case Left(err) => Left(Diagnostic(Diagnostic.Severity.Error, "T076", s"'tauto' proof reconstruction failed: $err", span))
        }
      case _ =>
        Left(Diagnostic(Diagnostic.Severity.Error, "T076", s"'tauto' could not prove propositional goal:\n${goal.formatHuman(env.kernelEnv)}", span))
    }
  }

  private def tautoSearch(
    env: ElabEnv,
    state: ProofState,
    depth: Int,
    destructedLevels: Set[Int],
    span: Span
  ): Option[(ElabEnv, ProofState)] = boundary {
    if (state.isSolved) break(Some((env, state)))
    if (depth <= 0) break(None)

    // Solve multiple independent subgoals separately so each gets a full depth budget!
    if (state.openGoals.length > 1) {
      var curEnv = env
      val solvedTerms = scala.collection.mutable.Map.empty[Int, Term]
      for (g <- state.openGoals) {
        val subInit = ProofState.initial(g.localCtx, g.targetType, g.label)
        tautoSearch(curEnv, subInit, depth, destructedLevels, span) match {
          case Some((eNext, done)) if done.isSolved =>
            done.buildProofTerm match {
              case Right(pt) =>
                curEnv = eNext
                solvedTerms(g.goalId) = pt
              case Left(_) => break(None)
            }
          case _ => break(None)
        }
      }
      val fullTerm = state.reconstruct(solvedTerms.toMap)
      break(Some((curEnv, ProofState(Nil, state.nextGoalId, _ => fullTerm, state.usedSorry))))
    }

    // 1. Immediate closers (`True`, `refl`, `assumption`, `contradiction`, `discriminate`)
    tacticTrivial(env, state, span) match {
      case Right((e1, s1)) =>
        tautoSearch(e1, s1, depth, destructedLevels, span).foreach(res => break(Some(res)))
      case Left(_) => ()
    }

    val goal = state.openGoals.head
    val normTarget = NbE.normalize(env.kernelEnv, goal.localCtx, goal.targetType)

    // 2. Reversible right introductions: `Pi` / implication (`P => Q`, `~P`)
    normTarget match {
      case Term.Pi(_, _, _) =>
        step(env, state, TacticStmt.Intro(Nil, span)) match {
          case Right((e1, s1)) => break(tautoSearch(e1, s1, depth, destructedLevels, span))
          case Left(_)         => ()
        }
      case _ => ()
    }

    // 3. Reversible left eliminations: `False`, `And`, `Iff`, `Or`, `Exists` (track De Bruijn level so never repeated!)
    for (idx <- goal.localCtx.entries.indices) {
      val hypLevel = goal.localCtx.depth - 1 - idx
      val hypName = goal.localCtx.entries(idx).name
      if (!destructedLevels.contains(hypLevel) && goal.localCtx.entries.indexWhere(_.name == hypName) == idx) {
        val hypTy = NbE.normalize(env.kernelEnv, goal.localCtx, goal.localCtx.lookupType(idx).get)
        val (hypHead, _) = Term.splitApps(hypTy)
        hypHead match {
          case Term.Ind("False") | Term.Ind("And") | Term.Ind("Iff") | Term.Ind("Or") | Term.Ind("Exists") =>
            step(env, state, TacticStmt.Cases(SurfaceExpr.VarExpr(hypName, span), None, Nil, span)) match {
              case Right((e1, s1)) =>
                break(tautoSearch(e1, s1, depth - 1, destructedLevels + hypLevel, span))
              case Left(_) => ()
            }
          case _ => ()
        }
      }
    }

    // 4. Reversible right conjunction/iff split
    val (targetHead, _) = Term.splitApps(normTarget)
    targetHead match {
      case Term.Ind("And") | Term.Ind("Iff") =>
        step(env, state, TacticStmt.Split(span)) match {
          case Right((e1, s1)) => break(tautoSearch(e1, s1, depth - 1, destructedLevels, span))
          case Left(_)         => ()
        }
      case _ => ()
    }

    // 5. Forward Modus Ponens saturation: if `h : A => B` and `a : A` are both in context (and `B` not yet in context), derive `B`!
    val existingTypes = goal.localCtx.entries.indices.map(i => NbE.normalize(env.kernelEnv, goal.localCtx, goal.localCtx.lookupType(i).get)).toSet
    for (idx <- goal.localCtx.entries.indices) {
      val hypTy = NbE.normalize(env.kernelEnv, goal.localCtx, goal.localCtx.lookupType(idx).get)
      hypTy match {
        case Term.Pi(_, dom, cod) if !Term.freeVarOccurs(cod, 0) =>
          val codUnshifted = Term.shift(cod, -1)
          val normDom = NbE.normalize(env.kernelEnv, goal.localCtx, dom)
          val normCod = NbE.normalize(env.kernelEnv, goal.localCtx, codUnshifted)
          if (!existingTypes.contains(normCod)) {
            val argIdxOpt = goal.localCtx.entries.indices.find { j =>
              NbE.normalize(env.kernelEnv, goal.localCtx, goal.localCtx.lookupType(j).get) == normDom
            }
            argIdxOpt.foreach { argIdx =>
              val mpProof = Term.App(Term.Var(idx), Term.Var(argIdx))
              val mpName = s"_mp_${state.nextGoalId}"
              val subId = state.nextGoalId
              val subCtx = goal.localCtx.push(mpName, normCod, Some(mpProof))
              val subGoal = ProofGoal(subId, goal.label, subCtx, Term.shift(goal.targetType, 1))
              val nextState = state.replaceHead(
                List(subGoal),
                sols => Term.Let(mpName, normCod, mpProof, sols(subId)),
                subId + 1
              )
              tautoSearch(env, nextState, depth - 1, destructedLevels, span).foreach(res => break(Some(res)))
            }
          }
        case _ => ()
      }
    }

    // 6. Backtracking disjunction right rules (`left` / `right`)
    if (targetHead == Term.Ind("Or")) {
      step(env, state, TacticStmt.LeftBranch(span)) match {
        case Right((e1, s1)) => tautoSearch(e1, s1, depth - 1, destructedLevels, span).foreach(res => break(Some(res)))
        case Left(_)         => ()
      }
      step(env, state, TacticStmt.RightBranch(span)) match {
        case Right((e1, s1)) => tautoSearch(e1, s1, depth - 1, destructedLevels, span).foreach(res => break(Some(res)))
        case Left(_)         => ()
      }
    }

    // 7. Backward chaining on local implications `h : A => B` matching goal (or `h : A => False` via exfalso)
    for (idx <- goal.localCtx.entries.indices) {
      val hypTy = NbE.normalize(env.kernelEnv, goal.localCtx, goal.localCtx.lookupType(idx).get)
      hypTy match {
        case Term.Pi(_, _, _) =>
          val metaCtx = new MetaContext()
          applyCoreTerm(env, state, goal, metaCtx, Term.Var(idx), hypTy, span) match {
            case Right((e1, s1)) =>
              tautoSearch(e1, s1, depth - 1, destructedLevels, span).foreach(res => break(Some(res)))
            case Left(_) => ()
          }
        case _ => ()
      }
    }

    // 8. Try `exfalso` if any negation `P => False` is in context and goal isn't already `False`
    if (targetHead != Term.Ind("False")) {
      val hasNeg = goal.localCtx.entries.indices.exists { idx =>
        NbE.normalize(env.kernelEnv, goal.localCtx, goal.localCtx.lookupType(idx).get) match {
          case Term.Pi(_, _, Term.Ind("False")) => true
          case _                                => false
        }
      }
      if (hasNeg) {
        step(env, state, TacticStmt.Exfalso(span)) match {
          case Right((e1, s1)) =>
            tautoSearch(e1, s1, depth - 1, destructedLevels, span).foreach(res => break(Some(res)))
          case Left(_) => ()
        }
      }
    }

    None
  }

  private def extractNatLit(term: Term): Option[Int] = term match {
    case Term.Ctor("Nat", "Zero") => Some(0)
    case Term.App(Term.Ctor("Nat", "Succ"), inner) => extractNatLit(inner).map(_ + 1)
    case _ => None
  }

  private def buildNatTerm(n: Int): Term =
    if (n <= 0) Term.Ctor("Nat", "Zero")
    else Term.App(Term.Ctor("Nat", "Succ"), buildNatTerm(n - 1))

  private def tacticSorry(env: ElabEnv, state: ProofState, span: Span): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val (envWithSorry, _) = env.ensureSorryAxiom
    val isProp = TypeChecker.inferSort(envWithSorry.kernelEnv, goal.localCtx, goal.targetType).contains(Sort.Prop)
    val sorryConst = if (isProp) "$sorryProp" else "$sorry"
    val proof = Term.App(Term.Const(sorryConst), goal.targetType)
    Right((envWithSorry, state.replaceHead(Nil, _ => proof, state.nextGoalId, markSorry = true)))
  }

  private def tacticHole(
    env: ElabEnv,
    state: ProofState,
    nameOpt: Option[String],
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val holeInfo = HoleInfo(nameOpt, span, goal.localCtx, goal.targetType)
    val nextEnv = env.copy(holes = env.holes :+ holeInfo)
    if (env.holeCollectionMode) {
      // Record the hole and continue inspecting the rest of the file!
      val (envWithSorry, _) = nextEnv.ensureSorryAxiom
      val isProp = TypeChecker.inferSort(envWithSorry.kernelEnv, goal.localCtx, goal.targetType).contains(Sort.Prop)
      val sorryConst = if (isProp) "$sorryProp" else "$sorry"
      val placeholder = Term.App(Term.Const(sorryConst), goal.targetType)
      Right((envWithSorry, state.replaceHead(Nil, _ => placeholder, state.nextGoalId, markSorry = true)))
    } else {
      Left(
        Diagnostic(
          Diagnostic.Severity.Info,
          "H001",
          s"Proof hole ${nameOpt.map("?" + _).getOrElse("?")}:\n${goal.formatHuman(env.kernelEnv)}",
          span
        )
      )
    }
  }
}
