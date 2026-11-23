package samurai.tactic

import scala.util.boundary
import scala.util.boundary.break
import samurai.elab.{ElabEnv, MetaContext}
import samurai.kernel.*
import samurai.syntax.*
import samurai.util.{Diagnostic, Span}

/**
 * Automated proof search (`auto` / `samurai`) and AI/Human tactic suggestion engine.
 *
 * Uses bounded backtracking search over intuitionistic logic, equality, simplification,
 * local hypotheses, and `@hint` lemmas. Every synthesized proof is a concrete core `Term`
 * independently checked by the Trusted Kernel.
 */
object ProofSearch {

  def tacticAuto(
    env: ElabEnv,
    state: ProofState,
    maxDepth: Int,
    span: Span
  ): Either[Diagnostic, (ElabEnv, ProofState)] = {
    val goal = state.openGoals.head
    val singleGoalState = ProofState.initial(goal.localCtx, goal.targetType, goal.label)
    search(env, singleGoalState, maxDepth, span) match {
      case Some((nextEnv, solved)) if solved.isSolved =>
        solved.buildProofTerm match {
          case Right(proofTerm) =>
            Right((nextEnv, state.replaceHead(Nil, _ => proofTerm, state.nextGoalId)))
          case Left(err) =>
            Left(Diagnostic(Diagnostic.Severity.Error, "T050", s"'auto' proof reconstruction failed: $err", span))
        }
      case _ =>
        Left(
          Diagnostic(
            Diagnostic.Severity.Error,
            "T050",
            s"'auto($maxDepth)' could not prove goal:\n${goal.formatHuman(env.kernelEnv)}",
            span,
            hint = Some("Try 'induction(...)', 'rewrite(...)', or inspect suggestions via AI protocol")
          )
        )
    }
  }

  private def search(
    env: ElabEnv,
    state: ProofState,
    depth: Int,
    span: Span
  ): Option[(ElabEnv, ProofState)] = boundary {
    if (state.isSolved) break(Some((env, state)))
    if (depth <= 0) break(None)

    val goal = state.openGoals.head

    // 1. Immediate closers: trivial (True, refl, assumption, contradiction, discriminate) and decide
    Tactics.tacticTrivial(env, state, span) match {
      case Right((e1, s1)) =>
        search(e1, s1, depth, span) match {
          case some @ Some(_) => break(some)
          case None           => ()
        }
      case Left(_) => ()
    }

    Tactics.step(env, state, TacticStmt.Decide(span)) match {
      case Right((e1, s1)) =>
        search(e1, s1, depth, span) match {
          case some @ Some(_) => break(some)
          case None           => ()
        }
      case Left(_) => ()
    }

    // 2. Reversible introductions: Pi / implication
    val normTarget = NbE.normalize(env.kernelEnv, goal.localCtx, goal.targetType)
    normTarget match {
      case Term.Pi(_, _, _) =>
        Tactics.step(env, state, TacticStmt.Intro(Nil, span)) match {
          case Right((e1, s1)) =>
            break(search(e1, s1, depth, span))
          case Left(_) => ()
        }
      case _ => ()
    }

    // 3. Destruct any And / Or / False / Exists hypotheses in context!
    for (idx <- goal.localCtx.entries.indices) {
      val hypName = goal.localCtx.entries(idx).name
      val hypTy = NbE.normalize(env.kernelEnv, goal.localCtx, goal.localCtx.lookupType(idx).get)
      val (hypHead, _) = Term.splitApps(hypTy)
      hypHead match {
        case Term.Ind("And") | Term.Ind("Or") | Term.Ind("False") | Term.Ind("Exists") =>
          // Avoid re-destructing already destructed names by only destructing if not shadowed
          if (goal.localCtx.entries.indexWhere(_.name == hypName) == idx) {
            Tactics.step(env, state, TacticStmt.Cases(SurfaceExpr.VarExpr(hypName, span), None, Nil, span)) match {
              case Right((e1, s1)) =>
                search(e1, s1, depth - 1, span) match {
                  case some @ Some(_) => break(some)
                  case None           => ()
                }
              case Left(_) => ()
            }
          }
        case _ => ()
      }
    }

    // 4. Split conjunctions (And / Iff / Pair)
    val (targetHead, _) = Term.splitApps(normTarget)
    targetHead match {
      case Term.Ind("And") | Term.Ind("Iff") =>
        Tactics.step(env, state, TacticStmt.Split(span)) match {
          case Right((e1, s1)) =>
            search(e1, s1, depth - 1, span) match {
              case some @ Some(_) => break(some)
              case None           => ()
            }
          case Left(_) => ()
        }

      case Term.Ind("Or") =>
        // Backtracking disjunction search
        Tactics.step(env, state, TacticStmt.LeftBranch(span)) match {
          case Right((e1, s1)) =>
            search(e1, s1, depth - 1, span) match {
              case some @ Some(_) => break(some)
              case None           => ()
            }
          case Left(_) => ()
        }
        Tactics.step(env, state, TacticStmt.RightBranch(span)) match {
          case Right((e1, s1)) =>
            search(e1, s1, depth - 1, span) match {
              case some @ Some(_) => break(some)
              case None           => ()
            }
          case Left(_) => ()
        }

      case Term.Ind("Eq") =>
        // Try simp once on equality goals
        Tactics.step(env, state, TacticStmt.Simp(Nil, span)) match {
          case Right((e1, s1)) if s1.isSolved =>
            break(Some((e1, s1)))
          case Right((e1, s1)) =>
            val afterNorm = NbE.normalize(e1.kernelEnv, s1.openGoals.head.localCtx, s1.openGoals.head.targetType)
            if (afterNorm != normTarget) {
              search(e1, s1, depth - 1, span) match {
                case some @ Some(_) => break(some)
                case None           => ()
              }
            }
          case Left(_) => ()
        }
        // Try congr if heads match
        Tactics.step(env, state, TacticStmt.Congr(span)) match {
          case Right((e1, s1)) =>
            search(e1, s1, depth - 1, span) match {
              case some @ Some(_) => break(some)
              case None           => ()
            }
          case Left(_) => ()
        }

      case _ => ()
    }

    // 5. Try backward chaining (`apply`) with local hypotheses
    for (idx <- goal.localCtx.entries.indices) {
      val hypTy = goal.localCtx.lookupType(idx).get
      val metaCtx = new MetaContext()
      Tactics.applyCoreTerm(env, state, goal, metaCtx, Term.Var(idx), hypTy, span) match {
        case Right((e1, s1)) =>
          search(e1, s1, depth - 1, span) match {
            case some @ Some(_) => break(some)
            case None           => ()
          }
        case Left(_) => ()
      }
    }

    // 6. Try backward chaining (`apply`) with `@hint` lemmas
    for (hintName <- env.hintLemmas) {
      env.kernelEnv.lookupConstType(hintName).foreach { lemmaTy =>
        val metaCtx = new MetaContext()
        Tactics.applyCoreTerm(env, state, goal, metaCtx, Term.Const(hintName), lemmaTy, span) match {
          case Right((e1, s1)) =>
            search(e1, s1, depth - 1, span) match {
              case some @ Some(_) => break(some)
              case None           => ()
            }
          case Left(_) => ()
        }
      }
    }

    None
  }

  /**
   * Generate ranked tactic suggestions for a given proof goal — designed for both
   * human interactive assistance and AI agent action spaces!
   */
  def suggest(env: ElabEnv, goal: ProofGoal): List[TacticSuggestion] = {
    val suggestions = List.newBuilder[TacticSuggestion]
    val state = ProofState.initial(goal.localCtx, goal.targetType, goal.label)
    val normTarget = NbE.normalize(env.kernelEnv, goal.localCtx, goal.targetType)
    val (head, _) = Term.splitApps(normTarget)

    // 1. Check immediate closers
    if (Tactics.tacticTrivial(env, state, Span.synthetic).isRight) {
      suggestions += TacticSuggestion("trivial", 0.99, "Closes the goal immediately via refl, True, assumption, or contradiction")
    }
    if (Tactics.step(env, state, TacticStmt.Decide(Span.synthetic)).isRight) {
      suggestions += TacticSuggestion("decide", 0.95, "Closes the goal via computational reflection")
    }

    // 2. Structural rules on goal head
    normTarget match {
      case Term.Pi(name, _, _) =>
        val paramName = if (name == "_" || name.isEmpty) "h" else name
        suggestions += TacticSuggestion(s"intro($paramName)", 0.92, "Introduce universally quantified variable or implication hypothesis")
      case _ => ()
    }

    head match {
      case Term.Ind("Eq") =>
        suggestions += TacticSuggestion("simp", 0.85, "Normalize and rewrite using @simp lemmas")
        if (Tactics.step(env, state, TacticStmt.Congr(Span.synthetic)).isRight) {
          suggestions += TacticSuggestion("congr", 0.82, "Reduce equality of applications to equality of arguments")
        }
        suggestions += TacticSuggestion("symmetry", 0.45, "Swap left-hand and right-hand sides of equality")
      case Term.Ind("And") | Term.Ind("Iff") =>
        suggestions += TacticSuggestion("split", 0.90, "Split conjunction into two subgoals")
      case Term.Ind("Or") =>
        suggestions += TacticSuggestion("left", 0.65, "Prove the left branch of disjunction")
        suggestions += TacticSuggestion("right", 0.65, "Prove the right branch of disjunction")
      case _ => ()
    }

    // 3. Induction / cases / rewrite suggestions from local hypotheses
    for (idx <- goal.localCtx.entries.indices) {
      val name = goal.localCtx.entries(idx).name
      val hypTy = NbE.normalize(env.kernelEnv, goal.localCtx, goal.localCtx.lookupType(idx).get)
      val (hypHead, _) = Term.splitApps(hypTy)
      hypHead match {
        case Term.Ind("Eq") =>
          suggestions += TacticSuggestion(s"rewrite($name)", 0.80, s"Rewrite goal using equality hypothesis '$name'")
        case Term.Ind("Nat") | Term.Ind("List") =>
          suggestions += TacticSuggestion(s"induction($name)", 0.78, s"Perform structural induction on '$name'")
        case Term.Ind("Bool") | Term.Ind("And") | Term.Ind("Or") | Term.Ind("False") =>
          suggestions += TacticSuggestion(s"cases($name)", 0.84, s"Case split on hypothesis '$name'")
        case _ => ()
      }
    }

    // 4. Matching lemmas from the environment (type-directed lemma search!)
    val matchingLemmas = searchMatchingLemmas(env, goal, limit = 5)
    for ((lemmaName, lemmaTypeStr) <- matchingLemmas) {
      suggestions += TacticSuggestion(s"apply($lemmaName)", 0.75, s"Matches goal with lemma: $lemmaName : $lemmaTypeStr")
    }

    suggestions += TacticSuggestion("auto", 0.60, "Run bounded automated proof search")
    suggestions.result().distinctBy(_.tactic).sortBy(-_.confidence)
  }

  /** Find checked theorems/definitions whose conclusion unifies with `goal.targetType`. */
  def searchMatchingLemmas(env: ElabEnv, goal: ProofGoal, limit: Int = 10): List[(String, String)] = {
    val state = ProofState.initial(goal.localCtx, goal.targetType, goal.label)
    val matches = List.newBuilder[(String, String)]
    var count = 0
    for ((name, defEntry) <- env.kernelEnv.defs if count < limit) {
      val metaCtx = new MetaContext()
      if (Tactics.applyCoreTerm(env, state, goal, metaCtx, Term.Const(name), defEntry.ty, Span.synthetic).isRight) {
        matches += ((name, Pretty.show(defEntry.ty)))
        count += 1
      }
    }
    matches.result()
  }
}
