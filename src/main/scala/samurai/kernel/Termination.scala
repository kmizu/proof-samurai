package samurai.kernel

import scala.util.boundary
import scala.util.boundary.break

/**
 * Structural termination (guardedness) checker for recursive `Fix` and `MutualFix` definitions.
 *
 * Ensures every recursive call passes a structurally strictly smaller subterm of the
 * designated decreasing inductive parameter `recursiveArgIndex`, guaranteeing strong
 * normalization and logical soundness (no `def loop: False = loop` or mutual loops).
 */
object Termination {

  private final case class GuardState(
    mutualFixTargets: Map[Int, (String, Int)], // fixLevel -> (fixName, recursiveArgIndex)
    decreasingInductiveName: String,
    currentDepth: Int,
    equalLevels: Set[Int],
    smallerLevels: Set[Int]
  ) {
    def pushPlain: GuardState = copy(currentDepth = currentDepth + 1)
    def pushEqual: GuardState = copy(currentDepth = currentDepth + 1, equalLevels = equalLevels + currentDepth)
    def pushSmaller: GuardState = copy(currentDepth = currentDepth + 1, smallerLevels = smallerLevels + currentDepth)
    def pushPlains(count: Int): GuardState = copy(currentDepth = currentDepth + count)
    def levelOf(deBruijnIndex: Int): Int = currentDepth - deBruijnIndex - 1
  }

  def checkFix(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    fixName: String,
    recursiveArgIndex: Int,
    fixType: Term,
    body: Term
  ): Either[String, Unit] =
    checkMutualFix(kernelEnv, localCtx, List(MutualFixDef(fixName, recursiveArgIndex, fixType, body)))

  def checkMutualFix(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    defs: List[MutualFixDef]
  ): Either[String, Unit] = boundary {
    if (defs.isEmpty) {
      break(Left("Mutual recursive block cannot be empty"))
    }

    // 1. Verify every mutual definition decreases on the same inductive type.
    val decreasingIndNames = List.newBuilder[String]
    for (fixDef <- defs) {
      if (fixDef.recArgIdx < 0) {
        break(Left(s"Recursive argument index must be non-negative in '${fixDef.name}'"))
      }
      findInductiveAtArgIndex(kernelEnv, localCtx, fixDef.ty, fixDef.recArgIdx) match {
        case Left(err)   => break(Left(s"Termination error in '${fixDef.name}': $err"))
        case Right(name) => decreasingIndNames += name
      }
    }
    val indNames = decreasingIndNames.result()
    val sharedInductiveName = indNames.head
    if (indNames.exists(_ != sharedInductiveName)) {
      break(
        Left(
          s"Mutual recursive definitions must decrease on the same inductive type (found: ${indNames.distinct.mkString(", ")})"
        )
      )
    }

    // 2. Build level -> (name, recArgIdx) table for all mutual functions in scope.
    val baseDepth = localCtx.depth
    val numMutual = defs.length
    val mutualTargets: Map[Int, (String, Int)] = defs.zipWithIndex.map { case (d, idx) =>
      (baseDepth + idx) -> (d.name, d.recArgIdx)
    }.toMap

    // 3. Check guardedness of every body in the mutual block.
    for (fixDef <- defs) {
      var curTerm = fixDef.body
      var curDepth = baseDepth + numMutual
      var paramLevel = -1

      for (argPos <- 0 to fixDef.recArgIdx) {
        curTerm match {
          case Term.Lam(_, _, innerBody) =>
            if (argPos == fixDef.recArgIdx) {
              paramLevel = curDepth
            }
            curDepth += 1
            curTerm = innerBody
          case _ =>
            break(
              Left(
                s"Termination error in '${fixDef.name}': body must bind at least ${fixDef.recArgIdx + 1} " +
                  s"lambda parameter(s) to reach decreasing argument #${fixDef.recArgIdx}"
              )
            )
        }
      }

      val initialState = GuardState(
        mutualFixTargets = mutualTargets,
        decreasingInductiveName = sharedInductiveName,
        currentDepth = curDepth,
        equalLevels = Set(paramLevel),
        smallerLevels = Set.empty
      )

      checkGuarded(kernelEnv, fixDef.name, curTerm, initialState) match {
        case Left(err) => break(Left(err))
        case Right(()) => ()
      }
    }

    Right(())
  }

  private def findInductiveAtArgIndex(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    fixType: Term,
    targetIndex: Int
  ): Either[String, String] = boundary {
    val fuel = new NbE.Fuel()
    var evalEnv = NbE.buildEvalEnv(kernelEnv, localCtx, fuel)
    var curValue = NbE.evaluate(kernelEnv, evalEnv, fixType, fuel)
    var curDepth = localCtx.depth
    var pos = 0

    while (pos <= targetIndex) {
      curValue match {
        case Value.VPi(_, domain, codomain) =>
          if (pos == targetIndex) {
            domain match {
              case Value.VInd(indName, _) => break(Right(indName))
              case other =>
                val domainTerm = NbE.quote(kernelEnv, curDepth, other, fuel)
                break(
                  Left(
                    s"decreasing parameter #$targetIndex must have an inductive type, found '${Pretty.show(domainTerm)}'"
                  )
                )
            }
          } else {
            val freshVar = Value.VNeutral(NeutralHead.NVar(curDepth), Nil)
            curValue = NbE.applyClosure(kernelEnv, codomain, freshVar, fuel)
            evalEnv = freshVar :: evalEnv
            curDepth += 1
            pos += 1
          }
        case _ =>
          break(Left(s"function type has fewer than ${targetIndex + 1} parameter(s)"))
      }
    }
    Left(s"could not locate parameter #$targetIndex")
  }

  private def checkGuarded(
    kernelEnv: KernelEnv,
    fixName: String,
    term: Term,
    state: GuardState
  ): Either[String, Unit] = term match {
    case Term.USort(_) | Term.Const(_) | Term.Ind(_) | Term.Ctor(_, _) =>
      Right(())

    case Term.Var(index) =>
      val lvl = state.levelOf(index)
      state.mutualFixTargets.get(lvl) match {
        case Some((calleeName, calleeRecIdx)) =>
          Left(
            s"Termination error in '$fixName': recursive reference '$calleeName' cannot be used unapplied " +
              s"(must be applied to a structurally smaller argument at position #$calleeRecIdx)"
          )
        case None =>
          Right(())
      }

    case Term.Pi(_, domain, codomain) =>
      for {
        _ <- checkGuarded(kernelEnv, fixName, domain, state)
        _ <- checkGuarded(kernelEnv, fixName, codomain, state.pushPlain)
      } yield ()

    case Term.Lam(_, domain, body) =>
      for {
        _ <- checkGuarded(kernelEnv, fixName, domain, state)
        _ <- checkGuarded(kernelEnv, fixName, body, state.pushPlain)
      } yield ()

    case Term.Let(_, ty, value, body) =>
      for {
        _ <- checkGuarded(kernelEnv, fixName, ty, state)
        _ <- checkGuarded(kernelEnv, fixName, value, state)
        nextState = value match {
          case Term.Var(index) if state.smallerLevels.contains(state.levelOf(index)) => state.pushSmaller
          case Term.Var(index) if state.equalLevels.contains(state.levelOf(index))   => state.pushEqual
          case _                                                                     => state.pushPlain
        }
        _ <- checkGuarded(kernelEnv, fixName, body, nextState)
      } yield ()

    case app @ Term.App(_, _) =>
      val (head, args) = Term.splitApps(app)
      checkList(kernelEnv, fixName, args, state).flatMap { _ =>
        head match {
          case Term.Var(index) if state.mutualFixTargets.contains(state.levelOf(index)) =>
            val (calleeName, calleeRecIdx) = state.mutualFixTargets(state.levelOf(index))
            if (args.length <= calleeRecIdx) {
              Left(
                s"Termination error in '$fixName': recursive call to '$calleeName' is under-applied " +
                  s"(expected at least ${calleeRecIdx + 1} argument(s), got ${args.length})"
              )
            } else {
              val recArg = args(calleeRecIdx)
              if (isStrictlySmallerTerm(recArg, state)) Right(())
              else
                Left(
                  s"Termination error in '$fixName': recursive call to '$calleeName' argument #$calleeRecIdx " +
                    s"is not structurally strictly smaller than the decreasing parameter"
                )
            }
          case _ =>
            checkGuarded(kernelEnv, fixName, head, state)
        }
      }

    case Term.Match(indName, params, motive, scrutinee, branches) =>
      for {
        _ <- checkList(kernelEnv, fixName, params, state)
        _ <- checkGuarded(kernelEnv, fixName, motive, state)
        _ <- checkGuarded(kernelEnv, fixName, scrutinee, state)
        _ <- checkBranches(kernelEnv, fixName, indName, scrutinee, branches, state)
      } yield ()

    case Term.Fix(_, _, ty, innerBody) =>
      for {
        _ <- checkGuarded(kernelEnv, fixName, ty, state)
        _ <- checkGuarded(kernelEnv, fixName, innerBody, state.pushPlain)
      } yield ()

    case Term.MutualFix(innerDefs, _) =>
      boundary {
        for (d <- innerDefs) {
          checkGuarded(kernelEnv, fixName, d.ty, state) match {
            case Left(err) => break(Left(err))
            case Right(()) => ()
          }
          checkGuarded(kernelEnv, fixName, d.body, state.pushPlains(innerDefs.length)) match {
            case Left(err) => break(Left(err))
            case Right(()) => ()
          }
        }
        Right(())
      }
  }

  private def checkBranches(
    kernelEnv: KernelEnv,
    fixName: String,
    indName: String,
    scrutinee: Term,
    branches: List[MatchBranch],
    state: GuardState
  ): Either[String, Unit] = boundary {
    val scrutineeIsTracked = indName == state.decreasingInductiveName && (scrutinee match {
      case Term.Var(index) =>
        val lvl = state.levelOf(index)
        state.equalLevels.contains(lvl) || state.smallerLevels.contains(lvl)
      case _ => false
    })

    val indEntryOpt = kernelEnv.inductives.get(indName)

    for (branch <- branches) {
      val ctorOpt = indEntryOpt.flatMap(_.ctor(branch.ctorName))
      val branchState = branch.fieldNames.indices.foldLeft(state) { (curState, fieldIdx) =>
        val fieldIsRecursiveSubterm = scrutineeIsTracked && ctorOpt.exists { ctor =>
          fieldIdx < ctor.fields.length && isRecursiveFieldType(ctor.fields(fieldIdx).ty, state.decreasingInductiveName)
        }
        if (fieldIsRecursiveSubterm) curState.pushSmaller else curState.pushPlain
      }
      checkGuarded(kernelEnv, fixName, branch.body, branchState) match {
        case Left(err) => break(Left(err))
        case Right(()) => ()
      }
    }
    Right(())
  }

  /**
   * True if `fieldType` is `Ind(indName)(...)` or `Pi(..., Ind(indName)(...))`
   * (supporting both direct recursive fields like `Succ(pred: Nat)` and higher-order fields like `Lim(f: Nat => Ord)` or `Acc.Intro`).
   */
  private def isRecursiveFieldType(fieldType: Term, indName: String): Boolean = fieldType match {
    case Term.Pi(_, _, codomain) => isRecursiveFieldType(codomain, indName)
    case other =>
      val (head, _) = Term.splitApps(other)
      head == Term.Ind(indName)
  }

  /**
   * True if `term` is a variable in `smallerLevels`, OR a higher-order subterm variable in
   * `smallerLevels` applied to arguments (e.g., `inv(y, ltProof)` from `Acc.Intro`).
   */
  private def isStrictlySmallerTerm(term: Term, state: GuardState): Boolean = term match {
    case Term.Var(index) =>
      state.smallerLevels.contains(state.levelOf(index))
    case app @ Term.App(_, _) =>
      val (head, _) = Term.splitApps(app)
      head match {
        case Term.Var(index) => state.smallerLevels.contains(state.levelOf(index))
        case _               => false
      }
    case _ => false
  }

  private def checkList(
    kernelEnv: KernelEnv,
    fixName: String,
    terms: List[Term],
    state: GuardState
  ): Either[String, Unit] = boundary {
    for (t <- terms) {
      checkGuarded(kernelEnv, fixName, t, state) match {
        case Left(err) => break(Left(err))
        case Right(()) => ()
      }
    }
    Right(())
  }
}
