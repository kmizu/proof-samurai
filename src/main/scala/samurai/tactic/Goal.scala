package samurai.tactic

import samurai.kernel.*
import samurai.util.Json

/**
 * A single open proof obligation (goal) inside a tactic proof or interactive AI proof session.
 */
final case class ProofGoal(
  goalId: Int,
  label: String,
  localCtx: LocalCtx,
  targetType: Term
) {
  private def isInternalSynthetic(name: String): Boolean =
    name.startsWith("_ih_") || name.startsWith("_ind_")

  def goalShape(kernelEnv: KernelEnv): String = {
    val normTarget = NbE.normalize(kernelEnv, localCtx, targetType)
    normTarget match {
      case Term.Pi(_, _, cod) =>
        if (Term.freeVarOccurs(cod, 0)) "forall" else "implication"
      case other =>
        val (head, _) = Term.splitApps(other)
        head match {
          case Term.Ind("Eq")     => "equality"
          case Term.Ind("And")    => "conjunction"
          case Term.Ind("Or")     => "disjunction"
          case Term.Ind("Iff")    => "iff"
          case Term.Ind("Exists") => "existential"
          case Term.Ind("False")  => "contradiction"
          case Term.Ind("True")   => "trivial"
          case Term.Ind(_)        => "inductive"
          case _                  => "proposition"
        }
    }
  }

  def formatHuman(kernelEnv: KernelEnv): String = {
    val sb = new StringBuilder
    sb.append(s"Goal #$goalId ($label):\n")
    val entriesOuterToInner = localCtx.entries.reverse
    var prefixNames: List[String] = Nil
    val visibleEntries = List.newBuilder[(String, String)]
    for (entry <- entriesOuterToInner) {
      if (!isInternalSynthetic(entry.name)) {
        val prettyTy = Pretty.show(entry.ty, prefixNames)
        visibleEntries += (entry.name -> prettyTy)
      }
      prefixNames = entry.name :: prefixNames
    }
    val visible = visibleEntries.result()
    val maxNameLen = visible.map(_._1.length).maxOption.getOrElse(0)
    for ((name, prettyTy) <- visible) {
      val pad = " " * (maxNameLen - name.length)
      sb.append(s"  $name$pad : $prettyTy\n")
    }
    sb.append("  ----------------------------------------\n")
    val normTarget = NbE.normalize(kernelEnv, localCtx, targetType)
    sb.append(s"  ⊢ ${Pretty.show(normTarget, localCtx.names)}\n")
    sb.toString
  }

  def toJson(kernelEnv: KernelEnv): Json = {
    val hypotheses = List.newBuilder[Json]
    val entriesOuterToInner = localCtx.entries.reverse
    var prefixNames: List[String] = Nil
    for (entry <- entriesOuterToInner) {
      if (!isInternalSynthetic(entry.name)) {
        hypotheses += Json.obj(
          "name" -> Json.Str(entry.name),
          "type" -> Json.Str(Pretty.show(entry.ty, prefixNames))
        )
      }
      prefixNames = entry.name :: prefixNames
    }
    val normTarget = NbE.normalize(kernelEnv, localCtx, targetType)
    Json.obj(
      "goalId" -> Json.Num(goalId),
      "label" -> Json.Str(label),
      "goalShape" -> Json.Str(goalShape(kernelEnv)),
      "hypotheses" -> Json.Arr(hypotheses.result()),
      "target" -> Json.Str(Pretty.show(targetType, localCtx.names)),
      "normalizedTarget" -> Json.Str(Pretty.show(normTarget, localCtx.names))
    )
  }
}

/**
 * Immutable LCF-style proof state.
 *
 * Because `ProofState` is purely immutable, both human interactive tactics and AI tree-search
 * agents can branch, backtrack, and explore multiple proof paths cleanly.
 * When `openGoals` is empty, `reconstruct(Map.empty)` yields a concrete core `Term`
 * which MUST be verified from scratch by `samurai.kernel.TypeChecker`.
 */
final case class ProofState(
  openGoals: List[ProofGoal],
  nextGoalId: Int,
  reconstruct: Map[Int, Term] => Term,
  usedSorry: Boolean = false
) {
  def isSolved: Boolean = openGoals.isEmpty

  def currentGoal: Option[ProofGoal] = openGoals.headOption

  def buildProofTerm: Either[String, Term] =
    if (openGoals.nonEmpty) {
      Left(s"Proof incomplete: ${openGoals.length} remaining goal(s)")
    } else {
      Right(reconstruct(Map.empty))
    }

  /**
   * Replace the focused (head) goal with zero or more new subgoals and a combiner function.
   */
  def replaceHead(
    newSubgoals: List[ProofGoal],
    combineHead: Map[Int, Term] => Term,
    newNextGoalId: Int,
    markSorry: Boolean = false
  ): ProofState = {
    val headGoal = openGoals.head
    val remainingGoals = openGoals.tail
    val nextReconstruct: Map[Int, Term] => Term = { solutions =>
      val headTerm = combineHead(solutions)
      reconstruct(solutions + (headGoal.goalId -> headTerm))
    }
    ProofState(
      openGoals = newSubgoals ++ remainingGoals,
      nextGoalId = newNextGoalId,
      reconstruct = nextReconstruct,
      usedSorry = usedSorry || markSorry
    )
  }

  /** Focus a specific goal by index (for multi-goal tactics or AI selection). */
  def focusGoal(goalId: Int): Option[ProofState] = {
    val idx = openGoals.indexWhere(_.goalId == goalId)
    if (idx < 0) None
    else {
      val chosen = openGoals(idx)
      val rest = openGoals.patch(idx, Nil, 1)
      Some(copy(openGoals = chosen :: rest))
    }
  }
}

object ProofState {
  def initial(localCtx: LocalCtx, targetType: Term, label: String = "main"): ProofState = {
    val rootGoal = ProofGoal(0, label, localCtx, targetType)
    ProofState(
      openGoals = List(rootGoal),
      nextGoalId = 1,
      reconstruct = solutions => solutions(0)
    )
  }
}

final case class TacticSuggestion(
  tactic: String,
  confidence: Double,
  rationale: String
) {
  def toJson: Json = Json.obj(
    "tactic" -> Json.Str(tactic),
    "confidence" -> Json.Num(confidence),
    "rationale" -> Json.Str(rationale)
  )
}
