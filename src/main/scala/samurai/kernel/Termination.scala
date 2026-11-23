package samurai.kernel

import scala.util.boundary
import scala.util.boundary.break

/**
 * Structural termination (guardedness) checker for recursive `Fix` definitions.
 *
 * Ensures every recursive call to `fix` passes a structurally strictly smaller
 * subterm of the designated decreasing inductive parameter `recursiveArgIndex`,
 * guaranteeing strong normalization and logical soundness (no `def loop: False = loop`).
 */
object Termination {

  private final case class GuardState(
    fixLevel: Int,
    decreasingInductiveName: String,
    recursiveArgIndex: Int,
    currentDepth: Int,
    equalLevels: Set[Int],
    smallerLevels: Set[Int]
  ) {
    def pushPlain: GuardState = copy(currentDepth = currentDepth + 1)
    def pushEqual: GuardState = copy(currentDepth = currentDepth + 1, equalLevels = equalLevels + currentDepth)
    def pushSmaller: GuardState = copy(currentDepth = currentDepth + 1, smallerLevels = smallerLevels + currentDepth)
    def levelOf(deBruijnIndex: Int): Int = currentDepth - deBruijnIndex - 1
  }

  def checkFix(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    fixName: String,
    recursiveArgIndex: Int,
    fixType: Term,
    body: Term
  ): Either[String, Unit] = boundary {
    if (recursiveArgIndex < 0) {
      break(Left(s"Recursive argument index must be non-negative in '$fixName'"))
    }

    // 1. Inspect `fixType` to find the inductive type at `recursiveArgIndex`.
    val decreasingIndName = findInductiveAtArgIndex(kernelEnv, localCtx, fixType, recursiveArgIndex) match {
      case Left(err)   => break(Left(s"Termination error in '$fixName': $err"))
      case Right(name) => name
    }

    // 2. Peel off at least `recursiveArgIndex + 1` lambdas from `body`.
    val baseDepth = localCtx.depth
    val fixLevel = baseDepth // `body` binds `fixName` at level `baseDepth`
    var curTerm = body
    var curDepth = baseDepth + 1
    var paramLevel = -1

    for (argPos <- 0 to recursiveArgIndex) {
      curTerm match {
        case Term.Lam(_, _, innerBody) =>
          if (argPos == recursiveArgIndex) {
            paramLevel = curDepth
          }
          curDepth += 1
          curTerm = innerBody
        case _ =>
          break(
            Left(
              s"Termination error in '$fixName': body must bind at least ${recursiveArgIndex + 1} " +
                s"lambda parameter(s) to reach decreasing argument #$recursiveArgIndex"
            )
          )
      }
    }

    val initialState = GuardState(
      fixLevel = fixLevel,
      decreasingInductiveName = decreasingIndName,
      recursiveArgIndex = recursiveArgIndex,
      currentDepth = curDepth,
      equalLevels = Set(paramLevel),
      smallerLevels = Set.empty
    )

    checkGuarded(kernelEnv, fixName, curTerm, initialState)
  }

  private def findInductiveAtArgIndex(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    fixType: Term,
    targetIndex: Int
  ): Either[String, String] = {
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
              case Value.VInd(indName, _) => return Right(indName)
              case other =>
                val domainTerm = NbE.quote(kernelEnv, curDepth, other, fuel)
                return Left(
                  s"decreasing parameter #$targetIndex must have an inductive type, found '${Pretty.show(domainTerm)}'"
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
          return Left(s"function type has fewer than ${targetIndex + 1} parameter(s)")
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
      if (state.levelOf(index) == state.fixLevel) {
        Left(
          s"Termination error in '$fixName': recursive reference '$fixName' cannot be used unapplied " +
            s"(must be applied to a structurally smaller argument at position #${state.recursiveArgIndex})"
        )
      } else {
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
      // First verify all argument subterms are guarded
      checkList(kernelEnv, fixName, args, state).flatMap { _ =>
        head match {
          case Term.Var(index) if state.levelOf(index) == state.fixLevel =>
            if (args.length <= state.recursiveArgIndex) {
              Left(
                s"Termination error in '$fixName': recursive call to '$fixName' is under-applied " +
                  s"(expected at least ${state.recursiveArgIndex + 1} argument(s), got ${args.length})"
              )
            } else {
              val recArg = args(state.recursiveArgIndex)
              if (isStrictlySmallerTerm(recArg, state)) Right(())
              else Left(
                s"Termination error in '$fixName': recursive call argument #${state.recursiveArgIndex} " +
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
   * (supporting both direct recursive fields like `Succ(pred: Nat)` and higher-order fields like `Lim(f: Nat => Ord)`).
   */
  private def isRecursiveFieldType(fieldType: Term, indName: String): Boolean = fieldType match {
    case Term.Pi(_, _, codomain) => isRecursiveFieldType(codomain, indName)
    case other =>
      val (head, _) = Term.splitApps(other)
      head == Term.Ind(indName)
  }

  /**
   * True if `term` is a variable in `smallerLevels`, OR a higher-order subterm variable in
   * `smallerLevels` applied to arguments (e.g., `f(n)` where `f: Nat => Ord` came from `Lim(f)`).
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
