package samurai.kernel

final case class Closure(capturedEnv: List[Value], bodyTerm: Term)

final case class BranchClosure(
  constructorName: String,
  fieldNames: List[String],
  capturedEnv: List[Value],
  bodyTerm: Term
)

enum NeutralHead {
  case NVar(level: Int)
  case NConst(constName: String)
  case NFix(fixName: String, recursiveArgIndex: Int, fixType: Value, bodyClosure: Closure)
}

enum Eliminator {
  case EApp(argument: Value)
  case EMatch(
    inductiveName: String,
    params: List[Value],
    motive: Value,
    branches: List[BranchClosure]
  )
}

enum Value {
  case VSort(sort: Sort)
  case VPi(binderName: String, domain: Value, codomain: Closure)
  case VLam(binderName: String, domain: Value, body: Closure)
  case VInd(inductiveName: String, arguments: List[Value])
  case VCtor(inductiveName: String, constructorName: String, arguments: List[Value])
  case VNeutral(head: NeutralHead, spine: List[Eliminator])
}

final case class FuelExceededException(message: String) extends RuntimeException(message)

/**
 * Normalization by Evaluation (NbE) for the Proof Samurai Trusted Kernel.
 *
 * Implements beta, delta (transparent defs), iota (match & guarded fix), zeta (let),
 * eta-conversion for functions, cumulative Type(i) <= Type(j) subtyping,
 * and definitional proof irrelevance for Prop arguments.
 */
object NbE {
  private val DefaultMaxSteps: Int = 2_000_000

  final class Fuel(var remaining: Int = DefaultMaxSteps) {
    def consume(): Unit = {
      remaining -= 1
      if (remaining <= 0) {
        throw FuelExceededException("Normalization step limit exceeded")
      }
    }
  }

  def buildEvalEnv(kernelEnv: KernelEnv, localCtx: LocalCtx, fuel: Fuel = new Fuel()): List[Value] = {
    // Entries are stored innermost-first; fold from outermost to innermost so let-values see outer bindings.
    val outermostFirst = localCtx.entries.reverse
    var evalEnv: List[Value] = Nil
    var level = 0
    for (entry <- outermostFirst) {
      val boundValue = entry.value match {
        case Some(letValue) => evaluate(kernelEnv, evalEnv, letValue, fuel)
        case None           => Value.VNeutral(NeutralHead.NVar(level), Nil)
      }
      evalEnv = boundValue :: evalEnv
      level += 1
    }
    evalEnv
  }

  def normalize(kernelEnv: KernelEnv, localCtx: LocalCtx, term: Term): Term = {
    val fuel = new Fuel()
    val evalEnv = buildEvalEnv(kernelEnv, localCtx, fuel)
    val value = evaluate(kernelEnv, evalEnv, term, fuel)
    quote(kernelEnv, localCtx.depth, value, fuel)
  }

  def evaluate(kernelEnv: KernelEnv, evalEnv: List[Value], term: Term, fuel: Fuel = new Fuel()): Value = {
    fuel.consume()
    term match {
      case Term.USort(sort) =>
        Value.VSort(sort)

      case Term.Var(index) =>
        if (index >= 0 && index < evalEnv.length) evalEnv(index)
        else Value.VNeutral(NeutralHead.NVar(-(index + 1)), Nil)

      case Term.Const(constName) =>
        kernelEnv.defs.get(constName) match {
          case Some(defEntry) if defEntry.transparent =>
            evaluate(kernelEnv, Nil, defEntry.body, fuel)
          case _ =>
            Value.VNeutral(NeutralHead.NConst(constName), Nil)
        }

      case Term.Ind(inductiveName) =>
        Value.VInd(inductiveName, Nil)

      case Term.Ctor(inductiveName, constructorName) =>
        Value.VCtor(inductiveName, constructorName, Nil)

      case Term.Pi(binderName, domain, codomain) =>
        Value.VPi(binderName, evaluate(kernelEnv, evalEnv, domain, fuel), Closure(evalEnv, codomain))

      case Term.Lam(binderName, domain, body) =>
        Value.VLam(binderName, evaluate(kernelEnv, evalEnv, domain, fuel), Closure(evalEnv, body))

      case Term.App(functionTerm, argumentTerm) =>
        val fnValue = evaluate(kernelEnv, evalEnv, functionTerm, fuel)
        val argValue = evaluate(kernelEnv, evalEnv, argumentTerm, fuel)
        applyValue(kernelEnv, fnValue, argValue, fuel)

      case Term.Let(_, _, boundValueTerm, bodyTerm) =>
        val boundValue = evaluate(kernelEnv, evalEnv, boundValueTerm, fuel)
        evaluate(kernelEnv, boundValue :: evalEnv, bodyTerm, fuel)

      case Term.Match(inductiveName, params, motive, scrutinee, branches) =>
        val paramValues = params.map(evaluate(kernelEnv, evalEnv, _, fuel))
        val motiveValue = evaluate(kernelEnv, evalEnv, motive, fuel)
        val scrutineeValue = evaluate(kernelEnv, evalEnv, scrutinee, fuel)
        val branchClosures = branches.map(branch =>
          BranchClosure(branch.ctorName, branch.fieldNames, evalEnv, branch.body)
        )
        applyMatch(kernelEnv, inductiveName, paramValues, motiveValue, scrutineeValue, branchClosures, fuel)

      case Term.Fix(fixName, recursiveArgIndex, fixType, body) =>
        val fixTypeValue = evaluate(kernelEnv, evalEnv, fixType, fuel)
        Value.VNeutral(NeutralHead.NFix(fixName, recursiveArgIndex, fixTypeValue, Closure(evalEnv, body)), Nil)
    }
  }

  def applyClosure(kernelEnv: KernelEnv, closure: Closure, argument: Value, fuel: Fuel): Value =
    evaluate(kernelEnv, argument :: closure.capturedEnv, closure.bodyTerm, fuel)

  def applyValue(kernelEnv: KernelEnv, functionValue: Value, argumentValue: Value, fuel: Fuel): Value = {
    fuel.consume()
    functionValue match {
      case Value.VLam(_, _, bodyClosure) =>
        applyClosure(kernelEnv, bodyClosure, argumentValue, fuel)

      case Value.VInd(inductiveName, existingArgs) =>
        Value.VInd(inductiveName, existingArgs :+ argumentValue)

      case Value.VCtor(inductiveName, constructorName, existingArgs) =>
        Value.VCtor(inductiveName, constructorName, existingArgs :+ argumentValue)

      case Value.VNeutral(fixHead @ NeutralHead.NFix(_, recursiveArgIndex, _, bodyClosure), spine) =>
        val extendedSpine = spine :+ Eliminator.EApp(argumentValue)
        val pureApps = extendedSpine.forall {
          case Eliminator.EApp(_) => true
          case _                  => false
        }
        if (pureApps && extendedSpine.length > recursiveArgIndex) {
          extendedSpine(recursiveArgIndex) match {
            case Eliminator.EApp(Value.VCtor(_, _, _)) =>
              // Guarded unfolding: recursive argument is a constructor value!
              val selfValue = Value.VNeutral(fixHead, Nil)
              val unfoldedBody = applyClosure(kernelEnv, bodyClosure, selfValue, fuel)
              applySpine(kernelEnv, unfoldedBody, extendedSpine, fuel)
            case _ =>
              Value.VNeutral(fixHead, extendedSpine)
          }
        } else {
          Value.VNeutral(fixHead, extendedSpine)
        }

      case Value.VNeutral(head, spine) =>
        Value.VNeutral(head, spine :+ Eliminator.EApp(argumentValue))

      case other =>
        throw new IllegalStateException(s"Cannot apply non-function value: $other")
    }
  }

  def applySpine(kernelEnv: KernelEnv, headValue: Value, spine: List[Eliminator], fuel: Fuel): Value =
    spine.foldLeft(headValue) { (current, eliminator) =>
      eliminator match {
        case Eliminator.EApp(arg) =>
          applyValue(kernelEnv, current, arg, fuel)
        case Eliminator.EMatch(inductiveName, params, motive, branches) =>
          applyMatch(kernelEnv, inductiveName, params, motive, current, branches, fuel)
      }
    }

  def applyMatch(
    kernelEnv: KernelEnv,
    inductiveName: String,
    params: List[Value],
    motive: Value,
    scrutinee: Value,
    branches: List[BranchClosure],
    fuel: Fuel
  ): Value = {
    fuel.consume()
    scrutinee match {
      case Value.VCtor(ctorIndName, constructorName, ctorArgs) if ctorIndName == inductiveName =>
        val numParams = kernelEnv.inductives.get(inductiveName).map(_.numParams).getOrElse(params.length)
        val fieldArgs = ctorArgs.drop(numParams)
        branches.find(_.constructorName == constructorName) match {
          case Some(branch) =>
            // Push fields left-to-right so last field is at index 0
            val extendedEnv = fieldArgs.foldLeft(branch.capturedEnv)((env, fieldVal) => fieldVal :: env)
            evaluate(kernelEnv, extendedEnv, branch.bodyTerm, fuel)
          case None =>
            throw new IllegalStateException(s"Missing match branch for $inductiveName.$constructorName")
        }

      case Value.VNeutral(head, spine) =>
        Value.VNeutral(head, spine :+ Eliminator.EMatch(inductiveName, params, motive, branches))

      case other =>
        throw new IllegalStateException(s"Cannot match on non-inductive value: $other")
    }
  }

  def quote(kernelEnv: KernelEnv, depth: Int, value: Value, fuel: Fuel = new Fuel()): Term = {
    fuel.consume()
    value match {
      case Value.VSort(sort) =>
        Term.USort(sort)

      case Value.VPi(binderName, domain, codomain) =>
        val quotedDomain = quote(kernelEnv, depth, domain, fuel)
        val freshVar = Value.VNeutral(NeutralHead.NVar(depth), Nil)
        val quotedCodomain = quote(kernelEnv, depth + 1, applyClosure(kernelEnv, codomain, freshVar, fuel), fuel)
        Term.Pi(binderName, quotedDomain, quotedCodomain)

      case Value.VLam(binderName, domain, body) =>
        val quotedDomain = quote(kernelEnv, depth, domain, fuel)
        val freshVar = Value.VNeutral(NeutralHead.NVar(depth), Nil)
        val quotedBody = quote(kernelEnv, depth + 1, applyClosure(kernelEnv, body, freshVar, fuel), fuel)
        Term.Lam(binderName, quotedDomain, quotedBody)

      case Value.VInd(inductiveName, arguments) =>
        Term.apps(Term.Ind(inductiveName), arguments.map(quote(kernelEnv, depth, _, fuel)))

      case Value.VCtor(inductiveName, constructorName, arguments) =>
        Term.apps(Term.Ctor(inductiveName, constructorName), arguments.map(quote(kernelEnv, depth, _, fuel)))

      case Value.VNeutral(head, spine) =>
        val quotedHead = head match {
          case NeutralHead.NVar(level) =>
            Term.Var(depth - level - 1)
          case NeutralHead.NConst(constName) =>
            Term.Const(constName)
          case NeutralHead.NFix(fixName, recursiveArgIndex, fixType, bodyClosure) =>
            val quotedFixType = quote(kernelEnv, depth, fixType, fuel)
            val freshSelf = Value.VNeutral(NeutralHead.NVar(depth), Nil)
            val quotedBody = quote(kernelEnv, depth + 1, applyClosure(kernelEnv, bodyClosure, freshSelf, fuel), fuel)
            Term.Fix(fixName, recursiveArgIndex, quotedFixType, quotedBody)
        }
        spine.foldLeft(quotedHead) { (acc, eliminator) =>
          eliminator match {
            case Eliminator.EApp(arg) =>
              Term.App(acc, quote(kernelEnv, depth, arg, fuel))
            case Eliminator.EMatch(inductiveName, params, motive, branches) =>
              val quotedParams = params.map(quote(kernelEnv, depth, _, fuel))
              val quotedMotive = quote(kernelEnv, depth, motive, fuel)
              val quotedBranches = branches.map { branch =>
                val arity = branch.fieldNames.length
                val extendedEnv = (0 until arity).foldLeft(branch.capturedEnv) { (env, offset) =>
                  Value.VNeutral(NeutralHead.NVar(depth + offset), Nil) :: env
                }
                val bodyVal = evaluate(kernelEnv, extendedEnv, branch.bodyTerm, fuel)
                val quotedBody = quote(kernelEnv, depth + arity, bodyVal, fuel)
                MatchBranch(branch.constructorName, branch.fieldNames, quotedBody)
              }
              Term.Match(inductiveName, quotedParams, quotedMotive, acc, quotedBranches)
          }
        }
    }
  }

  /**
   * Check whether `subType` is a cumulative subtype of `superType` (Type(i) <= Type(j) for i <= j,
   * covariant in Pi codomains, definitional equality everywhere else).
   */
  def isSubtype(
    kernelEnv: KernelEnv,
    depth: Int,
    subType: Value,
    superType: Value,
    fuel: Fuel = new Fuel()
  ): Boolean = {
    fuel.consume()
    (subType, superType) match {
      case (Value.VSort(subSort), Value.VSort(superSort)) =>
        subSort.leq(superSort)
      case (Value.VPi(_, domLeft, codLeft), Value.VPi(_, domRight, codRight)) =>
        areConvertible(kernelEnv, depth, domLeft, domRight, fuel) && {
          val freshVar = Value.VNeutral(NeutralHead.NVar(depth), Nil)
          isSubtype(
            kernelEnv,
            depth + 1,
            applyClosure(kernelEnv, codLeft, freshVar, fuel),
            applyClosure(kernelEnv, codRight, freshVar, fuel),
            fuel
          )
        }
      case _ =>
        areConvertible(kernelEnv, depth, subType, superType, fuel)
    }
  }

  /** Check definitional equality of two values, including eta for functions and Prop proof irrelevance. */
  def areConvertible(
    kernelEnv: KernelEnv,
    depth: Int,
    left: Value,
    right: Value,
    fuel: Fuel = new Fuel()
  ): Boolean = {
    fuel.consume()
    (left, right) match {
      case (Value.VSort(s1), Value.VSort(s2)) =>
        s1 == s2

      case (Value.VPi(_, dom1, cod1), Value.VPi(_, dom2, cod2)) =>
        areConvertible(kernelEnv, depth, dom1, dom2, fuel) && {
          val freshVar = Value.VNeutral(NeutralHead.NVar(depth), Nil)
          areConvertible(
            kernelEnv,
            depth + 1,
            applyClosure(kernelEnv, cod1, freshVar, fuel),
            applyClosure(kernelEnv, cod2, freshVar, fuel),
            fuel
          )
        }

      case (Value.VLam(_, _, body1), Value.VLam(_, _, body2)) =>
        val freshVar = Value.VNeutral(NeutralHead.NVar(depth), Nil)
        areConvertible(
          kernelEnv,
          depth + 1,
          applyClosure(kernelEnv, body1, freshVar, fuel),
          applyClosure(kernelEnv, body2, freshVar, fuel),
          fuel
        )

      // Eta-equality for functions
      case (Value.VLam(_, _, body1), other) =>
        val freshVar = Value.VNeutral(NeutralHead.NVar(depth), Nil)
        areConvertible(
          kernelEnv,
          depth + 1,
          applyClosure(kernelEnv, body1, freshVar, fuel),
          applyValue(kernelEnv, other, freshVar, fuel),
          fuel
        )

      case (other, Value.VLam(_, _, body2)) =>
        val freshVar = Value.VNeutral(NeutralHead.NVar(depth), Nil)
        areConvertible(
          kernelEnv,
          depth + 1,
          applyValue(kernelEnv, other, freshVar, fuel),
          applyClosure(kernelEnv, body2, freshVar, fuel),
          fuel
        )

      case (Value.VInd(name1, args1), Value.VInd(name2, args2)) =>
        name1 == name2 && args1.length == args2.length &&
          args1.zip(args2).forall { case (a1, a2) => areConvertible(kernelEnv, depth, a1, a2, fuel) }

      case (Value.VCtor(ind1, ctor1, args1), Value.VCtor(ind2, ctor2, args2)) =>
        if (ind1 != ind2 || ctor1 != ctor2 || args1.length != args2.length) false
        else {
          // If inductive lives in Prop, all inhabitants are definitionally equal (proof irrelevance).
          kernelEnv.inductives.get(ind1) match {
            case Some(indEntry) if indEntry.sort == Sort.Prop => true
            case Some(indEntry) =>
              val paramCount = indEntry.numParams
              val ctorOpt = indEntry.ctor(ctor1)
              args1.zip(args2).zipWithIndex.forall { case ((a1, a2), argPosition) =>
                val isPropField = ctorOpt.exists { ctorEntry =>
                  val fieldIndex = argPosition - paramCount
                  if (fieldIndex >= 0 && fieldIndex < ctorEntry.fieldIsProp.length) {
                    ctorEntry.fieldIsProp(fieldIndex)
                  } else if (fieldIndex >= 0 && fieldIndex < ctorEntry.fields.length) {
                    isKnownPropType(kernelEnv, ctorEntry.fields(fieldIndex).ty)
                  } else false
                }
                isPropField || areConvertible(kernelEnv, depth, a1, a2, fuel)
              }
            case None =>
              args1.zip(args2).forall { case (a1, a2) => areConvertible(kernelEnv, depth, a1, a2, fuel) }
          }
        }

      case (Value.VNeutral(head1, spine1), Value.VNeutral(head2, spine2)) =>
        headsEqual(kernelEnv, depth, head1, head2, fuel) &&
          spine1.length == spine2.length &&
          spine1.zip(spine2).forall { case (e1, e2) => eliminatorsEqual(kernelEnv, depth, e1, e2, fuel) }

      case _ => false
    }
  }

  private def isKnownPropType(kernelEnv: KernelEnv, fieldType: Term): Boolean = {
    val (head, _) = Term.splitApps(fieldType)
    head match {
      case Term.Ind(indName) => kernelEnv.inductives.get(indName).exists(_.sort == Sort.Prop)
      case _                 => false
    }
  }

  private def headsEqual(
    kernelEnv: KernelEnv,
    depth: Int,
    head1: NeutralHead,
    head2: NeutralHead,
    fuel: Fuel
  ): Boolean = (head1, head2) match {
    case (NeutralHead.NVar(l1), NeutralHead.NVar(l2))     => l1 == l2
    case (NeutralHead.NConst(c1), NeutralHead.NConst(c2)) => c1 == c2
    case (NeutralHead.NFix(_, idx1, ty1, body1), NeutralHead.NFix(_, idx2, ty2, body2)) =>
      idx1 == idx2 &&
        areConvertible(kernelEnv, depth, ty1, ty2, fuel) && {
          val freshSelf = Value.VNeutral(NeutralHead.NVar(depth), Nil)
          areConvertible(
            kernelEnv,
            depth + 1,
            applyClosure(kernelEnv, body1, freshSelf, fuel),
            applyClosure(kernelEnv, body2, freshSelf, fuel),
            fuel
          )
        }
    case _ => false
  }

  private def eliminatorsEqual(
    kernelEnv: KernelEnv,
    depth: Int,
    elim1: Eliminator,
    elim2: Eliminator,
    fuel: Fuel
  ): Boolean = (elim1, elim2) match {
    case (Eliminator.EApp(a1), Eliminator.EApp(a2)) =>
      areConvertible(kernelEnv, depth, a1, a2, fuel)

    case (
          Eliminator.EMatch(ind1, params1, motive1, branches1),
          Eliminator.EMatch(ind2, params2, motive2, branches2)
        ) =>
      ind1 == ind2 &&
        params1.length == params2.length &&
        params1.zip(params2).forall { case (p1, p2) => areConvertible(kernelEnv, depth, p1, p2, fuel) } &&
        areConvertible(kernelEnv, depth, motive1, motive2, fuel) &&
        branches1.length == branches2.length &&
        branches1.zip(branches2).forall { case (b1, b2) =>
          b1.constructorName == b2.constructorName &&
            b1.fieldNames.length == b2.fieldNames.length && {
              val arity = b1.fieldNames.length
              val env1 = (0 until arity).foldLeft(b1.capturedEnv)((env, offset) =>
                Value.VNeutral(NeutralHead.NVar(depth + offset), Nil) :: env
              )
              val env2 = (0 until arity).foldLeft(b2.capturedEnv)((env, offset) =>
                Value.VNeutral(NeutralHead.NVar(depth + offset), Nil) :: env
              )
              val v1 = evaluate(kernelEnv, env1, b1.bodyTerm, fuel)
              val v2 = evaluate(kernelEnv, env2, b2.bodyTerm, fuel)
              areConvertible(kernelEnv, depth + arity, v1, v2, fuel)
            }
        }

    case _ => false
  }
}
