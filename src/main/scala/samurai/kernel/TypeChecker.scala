package samurai.kernel

import scala.util.boundary
import scala.util.boundary.break

final case class KernelError(code: String, message: String)

/**
 * Small, auditable Trusted Kernel Type Checker for Proof Samurai.
 *
 * All surface programs, elaborated terms, tactic proofs, and AI-synthesized proof terms
 * MUST pass through this independent kernel before entering `KernelEnv`.
 */
object TypeChecker {

  /** Check and register a new inductive type declaration in `kernelEnv`. */
  def checkInductive(kernelEnv: KernelEnv, inductive: IndEntry): Either[KernelError, KernelEnv] = boundary {
    if (kernelEnv.contains(inductive.name)) {
      break(Left(KernelError("K001", s"Duplicate declaration name '${inductive.name}'")))
    }
    inductive.sort match {
      case Sort.Type(level) if level < 0 =>
        break(Left(KernelError("K002", s"Invalid negative universe level $level in '${inductive.name}'")))
      case _ => ()
    }

    // 1. Check parameter telescope
    var paramCtx = LocalCtx.empty
    for (param <- inductive.params) {
      inferSort(kernelEnv, paramCtx, param.ty) match {
        case Left(err) => break(Left(err))
        case Right(_)  => paramCtx = paramCtx.push(param.name, param.ty)
      }
    }

    // 2. Check index telescope under params
    var indexCtx = paramCtx
    for (indexBinder <- inductive.indices) {
      inferSort(kernelEnv, indexCtx, indexBinder.ty) match {
        case Left(err) => break(Left(err))
        case Right(_)  => indexCtx = indexCtx.push(indexBinder.name, indexBinder.ty)
      }
    }

    // 3. Register inductive tentatively (for checking recursive constructor occurrences)
    val tentativeInd = inductive.copy(isSubsingleton = false)
    val envWithInd = kernelEnv.addInductive(tentativeInd)

    // 4. Check duplicate constructor names
    val ctorNames = inductive.constructors.map(_.name)
    if (ctorNames.distinct.length != ctorNames.length) {
      break(Left(KernelError("K003", s"Duplicate constructor names in inductive '${inductive.name}'")))
    }

    // 5. Check every constructor's fields, universe levels, and result indices
    var allFieldsInProp = true
    val checkedCtors = List.newBuilder[CtorEntry]
    for (constructor <- inductive.constructors) {
      if (constructor.resultIndices.length != inductive.numIndices) {
        break(
          Left(
            KernelError(
              "K004",
              s"Constructor '${inductive.name}.${constructor.name}' supplies ${constructor.resultIndices.length} " +
                s"result indices, expected ${inductive.numIndices}"
            )
          )
        )
      }

      var fieldCtx = paramCtx
      val fieldPropFlags = List.newBuilder[Boolean]
      for (field <- constructor.fields) {
        inferSort(envWithInd, fieldCtx, field.ty) match {
          case Left(err) => break(Left(err))
          case Right(fieldSort) =>
            val isProp = fieldSort == Sort.Prop
            fieldPropFlags += isProp
            if (!isProp) {
              allFieldsInProp = false
            }
            // Predicativity check for Type(k) inductives:
            // All constructor fields must live in Prop or Type(j) with j <= k!
            (inductive.sort, fieldSort) match {
              case (Sort.Type(indLevel), Sort.Type(fieldLevel)) if fieldLevel > indLevel =>
                break(
                  Left(
                    KernelError(
                      "K005",
                      s"Universe level error in '${inductive.name}.${constructor.name}': " +
                        s"field '${field.name}' lives in ${fieldSort}, which exceeds inductive universe ${inductive.sort}"
                    )
                  )
                )
              case _ => ()
            }
            fieldCtx = fieldCtx.push(field.name, field.ty)
        }
      }

      // Check constructor result indices against `inductive.indices` (with params shifted over fields!)
      val numParams = inductive.numParams
      val numFields = constructor.arity
      val shiftedParamVars = (0 until numParams).toList.map(j => Term.Var(numFields + numParams - 1 - j))
      val checkedIndices = List.newBuilder[Term]
      for ((resultIdxTerm, idxPos) <- constructor.resultIndices.zipWithIndex) {
        val rawIndexTy = inductive.indices(idxPos).ty
        val prevChecked = checkedIndices.result()
        // Substitute params and previous result indices into `rawIndexTy`
        val expectedIndexTy = Term.substMany(rawIndexTy, shiftedParamVars ++ prevChecked)
        check(envWithInd, fieldCtx, resultIdxTerm, expectedIndexTy) match {
          case Left(err) => break(Left(err))
          case Right(()) => checkedIndices += resultIdxTerm
        }
      }

      checkedCtors += constructor.copy(fieldIsProp = fieldPropFlags.result())
    }

    // 6. Strict positivity check (using NbE normalization in envWithInd!)
    Positivity.checkInductive(envWithInd, inductive) match {
      case Left(errMsg) => break(Left(KernelError("K006", errMsg)))
      case Right(())    => ()
    }

    // 7. Compute subsingleton status for Prop -> Type elimination soundness:
    // A Prop inductive is a subsingleton iff it has 0 constructors OR 1 constructor whose fields all live in Prop.
    val isSubsingleton =
      inductive.sort == Sort.Prop &&
        (inductive.constructors.isEmpty || (inductive.constructors.length == 1 && allFieldsInProp))

    val verifiedInd = inductive.copy(constructors = checkedCtors.result(), isSubsingleton = isSubsingleton)
    Right(kernelEnv.addInductive(verifiedInd))
  }

  /** Check and register a definition or theorem in `kernelEnv`. */
  def checkDef(
    kernelEnv: KernelEnv,
    name: String,
    declaredType: Term,
    body: Term,
    transparent: Boolean = true,
    isTheorem: Boolean = false
  ): Either[KernelError, KernelEnv] = {
    if (kernelEnv.contains(name)) {
      return Left(KernelError("K001", s"Duplicate declaration name '$name'"))
    }
    for {
      _ <- inferSort(kernelEnv, LocalCtx.empty, declaredType)
      _ <- check(kernelEnv, LocalCtx.empty, body, declaredType)
    } yield {
      val axiomsUsed = kernelEnv.collectAxioms(declaredType) ++ kernelEnv.collectAxioms(body)
      kernelEnv.addDef(
        DefEntry(
          name = name,
          ty = declaredType,
          body = body,
          transparent = transparent,
          isTheorem = isTheorem,
          axiomsUsed = axiomsUsed
        )
      )
    }
  }

  /** Check and register an explicit axiom (or sorry) in `kernelEnv`. */
  def checkAxiom(kernelEnv: KernelEnv, name: String, declaredType: Term): Either[KernelError, KernelEnv] = {
    if (kernelEnv.contains(name)) {
      return Left(KernelError("K001", s"Duplicate declaration name '$name'"))
    }
    inferSort(kernelEnv, LocalCtx.empty, declaredType).map { _ =>
      kernelEnv.addAxiom(AxiomEntry(name, declaredType))
    }
  }

  /** Infer the Sort of a type expression (must normalize to `VSort`). */
  def inferSort(kernelEnv: KernelEnv, localCtx: LocalCtx, typeTerm: Term): Either[KernelError, Sort] = {
    infer(kernelEnv, localCtx, typeTerm).flatMap { inferredType =>
      val fuel = new NbE.Fuel()
      val evalEnv = NbE.buildEvalEnv(kernelEnv, localCtx, fuel)
      NbE.evaluate(kernelEnv, evalEnv, inferredType, fuel) match {
        case Value.VSort(sort) => Right(sort)
        case other =>
          val quoted = NbE.quote(kernelEnv, localCtx.depth, other, fuel)
          Left(
            KernelError(
              "K010",
              s"Expected a type (Sort), but '${Pretty.show(typeTerm, localCtx.names)}' has type '${Pretty.show(quoted, localCtx.names)}'"
            )
          )
      }
    }
  }

  /** Bidirectional checking: verify that `term` has type `expectedType` in `(kernelEnv, localCtx)`. */
  def check(kernelEnv: KernelEnv, localCtx: LocalCtx, term: Term, expectedType: Term): Either[KernelError, Unit] = {
    infer(kernelEnv, localCtx, term).flatMap { inferredType =>
      val fuel = new NbE.Fuel()
      val evalEnv = NbE.buildEvalEnv(kernelEnv, localCtx, fuel)
      val inferredVal = NbE.evaluate(kernelEnv, evalEnv, inferredType, fuel)
      val expectedVal = NbE.evaluate(kernelEnv, evalEnv, expectedType, fuel)
      if (NbE.isSubtype(kernelEnv, localCtx.depth, inferredVal, expectedVal, fuel)) {
        Right(())
      } else {
        val normInferred = NbE.quote(kernelEnv, localCtx.depth, inferredVal, fuel)
        val normExpected = NbE.quote(kernelEnv, localCtx.depth, expectedVal, fuel)
        Left(
          KernelError(
            "K011",
            s"Type mismatch for '${Pretty.show(term, localCtx.names)}':\n" +
              s"  expected: ${Pretty.show(normExpected, localCtx.names)}\n" +
              s"  found:    ${Pretty.show(normInferred, localCtx.names)}"
          )
        )
      }
    }
  }

  /** Infer the core type of `term` in `(kernelEnv, localCtx)`. */
  def infer(kernelEnv: KernelEnv, localCtx: LocalCtx, term: Term): Either[KernelError, Term] = {
    try {
      inferImpl(kernelEnv, localCtx, term)
    } catch {
      case ex: FuelExceededException =>
        Left(KernelError("K099", ex.message))
    }
  }

  private def inferImpl(kernelEnv: KernelEnv, localCtx: LocalCtx, term: Term): Either[KernelError, Term] = term match {
    case Term.USort(sort) =>
      sort match {
        case Sort.Type(level) if level < 0 =>
          Left(KernelError("K002", s"Invalid negative universe level $level"))
        case _ =>
          Right(Term.USort(sort.succ))
      }

    case Term.Var(index) =>
      localCtx.lookupType(index) match {
        case Some(varType) => Right(varType)
        case None => Left(KernelError("K012", s"Unbound De Bruijn variable #$index (context depth ${localCtx.depth})"))
      }

    case Term.Const(constName) =>
      kernelEnv.lookupConstType(constName) match {
        case Some(constType) => Right(constType)
        case None => Left(KernelError("K013", s"Unknown constant '$constName'"))
      }

    case Term.Ind(indName) =>
      kernelEnv.inductives.get(indName) match {
        case Some(indEntry) => Right(indEntry.fullType)
        case None => Left(KernelError("K014", s"Unknown inductive type '$indName'"))
      }

    case Term.Ctor(indName, ctorName) =>
      kernelEnv.inductives.get(indName) match {
        case Some(indEntry) =>
          indEntry.ctor(ctorName) match {
            case Some(ctorEntry) => Right(indEntry.ctorType(ctorEntry))
            case None => Left(KernelError("K015", s"Unknown constructor '$indName.$ctorName'"))
          }
        case None => Left(KernelError("K014", s"Unknown inductive type '$indName'"))
      }

    case Term.Pi(binderName, domain, codomain) =>
      for {
        domainSort <- inferSort(kernelEnv, localCtx, domain)
        codomainSort <- inferSort(kernelEnv, localCtx.push(binderName, domain), codomain)
      } yield Term.USort(domainSort.piSort(codomainSort))

    case Term.Lam(binderName, domain, body) =>
      for {
        _ <- inferSort(kernelEnv, localCtx, domain)
        bodyType <- infer(kernelEnv, localCtx.push(binderName, domain), body)
      } yield Term.Pi(binderName, domain, bodyType)

    case Term.App(functionTerm, argumentTerm) =>
      for {
        functionType <- infer(kernelEnv, localCtx, functionTerm)
        fuel = new NbE.Fuel()
        evalEnv = NbE.buildEvalEnv(kernelEnv, localCtx, fuel)
        fnTypeVal = NbE.evaluate(kernelEnv, evalEnv, functionType, fuel)
        resultType <- fnTypeVal match {
          case Value.VPi(_, domainVal, codomainClosure) =>
            val domainTerm = NbE.quote(kernelEnv, localCtx.depth, domainVal, fuel)
            check(kernelEnv, localCtx, argumentTerm, domainTerm).map { _ =>
              val argVal = NbE.evaluate(kernelEnv, evalEnv, argumentTerm, fuel)
              val resVal = NbE.applyClosure(kernelEnv, codomainClosure, argVal, fuel)
              NbE.quote(kernelEnv, localCtx.depth, resVal, fuel)
            }
          case other =>
            val quoted = NbE.quote(kernelEnv, localCtx.depth, other, fuel)
            Left(
              KernelError(
                "K016",
                s"Cannot apply '${Pretty.show(functionTerm, localCtx.names)}' of non-function type '${Pretty.show(quoted, localCtx.names)}'"
              )
            )
        }
      } yield resultType

    case Term.Let(binderName, declaredType, valueTerm, bodyTerm) =>
      for {
        _ <- inferSort(kernelEnv, localCtx, declaredType)
        _ <- check(kernelEnv, localCtx, valueTerm, declaredType)
        bodyType <- infer(kernelEnv, localCtx.push(binderName, declaredType, Some(valueTerm)), bodyTerm)
      } yield Term.subst(bodyType, 0, valueTerm)

    case Term.Match(indName, params, motive, scrutinee, branches) =>
      inferMatch(kernelEnv, localCtx, indName, params, motive, scrutinee, branches)

    case Term.Fix(fixName, recursiveArgIndex, fixType, body) =>
      for {
        _ <- inferSort(kernelEnv, localCtx, fixType)
        _ <- check(kernelEnv, localCtx.push(fixName, fixType), body, Term.shift(fixType, 1))
        _ <- Termination
          .checkFix(kernelEnv, localCtx, fixName, recursiveArgIndex, fixType, body)
          .left
          .map(msg => KernelError("K020", msg))
      } yield fixType
  }

  private def inferMatch(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    indName: String,
    params: List[Term],
    motive: Term,
    scrutinee: Term,
    branches: List[MatchBranch]
  ): Either[KernelError, Term] = boundary {
    val indEntry = kernelEnv.inductives.get(indName) match {
      case Some(entry) => entry
      case None        => break(Left(KernelError("K014", s"Unknown inductive type '$indName' in match")))
    }

    if (params.length != indEntry.numParams) {
      break(
        Left(
          KernelError(
            "K021",
            s"Match on '$indName' expected ${indEntry.numParams} type parameter(s), got ${params.length}"
          )
        )
      )
    }

    // 1. Check params against indEntry.params
    val checkedParams = List.newBuilder[Term]
    for ((paramTerm, idx) <- params.zipWithIndex) {
      val expectedParamTy = Term.substMany(indEntry.params(idx).ty, checkedParams.result())
      check(kernelEnv, localCtx, paramTerm, expectedParamTy) match {
        case Left(err) => break(Left(err))
        case Right(()) => checkedParams += paramTerm
      }
    }

    // 2. Check scrutinee type reduces to VInd(indName, actualParams ++ actualIndices)
    val scrutineeType = infer(kernelEnv, localCtx, scrutinee) match {
      case Left(err) => break(Left(err))
      case Right(t)  => t
    }
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(kernelEnv, localCtx, fuel)
    val scrutTypeVal = NbE.evaluate(kernelEnv, evalEnv, scrutineeType, fuel)
    val (actualParams, actualIndices) = scrutTypeVal match {
      case Value.VInd(actualIndName, allArgs) if actualIndName == indName =>
        val expectedTotal = indEntry.numParams + indEntry.numIndices
        if (allArgs.length != expectedTotal) {
          break(Left(KernelError("K022", s"Scrutinee type '$indName' is not fully applied")))
        }
        val (pVals, iVals) = allArgs.splitAt(indEntry.numParams)
        // Verify params match scrutinee's params
        for (((givenP, actualP), idx) <- params.zip(pVals).zipWithIndex) {
          val givenPVal = NbE.evaluate(kernelEnv, evalEnv, givenP, fuel)
          if (!NbE.areConvertible(kernelEnv, localCtx.depth, givenPVal, actualP, fuel)) {
            break(Left(KernelError("K023", s"Match parameter #$idx does not match scrutinee type")))
          }
        }
        (pVals, iVals.map(NbE.quote(kernelEnv, localCtx.depth, _, fuel)))
      case other =>
        val quoted = NbE.quote(kernelEnv, localCtx.depth, other, fuel)
        break(
          Left(
            KernelError(
              "K024",
              s"Match scrutinee must have type '$indName', found '${Pretty.show(quoted, localCtx.names)}'"
            )
          )
        )
    }
    val _ = actualParams

    // 3. Check motive type: Pi(indices[params], Pi(s: Ind(params, idxVars), targetSort))
    val motiveType = infer(kernelEnv, localCtx, motive) match {
      case Left(err) => break(Left(err))
      case Right(t)  => t
    }
    val targetSort = extractMotiveTargetSort(kernelEnv, localCtx, indEntry, params, motiveType) match {
      case Left(err) => break(Left(err))
      case Right(s)  => s
    }

    // 4. Soundness guard: Subsingleton Prop -> Type elimination check!
    if (indEntry.sort == Sort.Prop && targetSort != Sort.Prop && !indEntry.isSubsingleton) {
      break(
        Left(
          KernelError(
            "K025",
            s"Illegal elimination of Prop inductive '$indName' into $targetSort: " +
              s"'$indName' is not a subsingleton (eliminating it into computational Type would break soundness and proof erasure)"
          )
        )
      )
    }

    // 5. Exhaustiveness check: branches must cover EVERY constructor of indEntry in order
    if (branches.length != indEntry.constructors.length) {
      val covered = branches.map(_.ctorName).toSet
      val missing = indEntry.constructors.map(_.name).filterNot(covered.contains)
      break(
        Left(
          KernelError(
            "K026",
            s"Non-exhaustive match on '$indName': missing constructor(s): ${missing.mkString(", ")}"
          )
        )
      )
    }

    for ((branch, expectedCtor) <- branches.zip(indEntry.constructors)) {
      if (branch.ctorName != expectedCtor.name) {
        break(
          Left(
            KernelError(
              "K027",
              s"Match branch mismatch on '$indName': expected constructor '${expectedCtor.name}', found '${branch.ctorName}'"
            )
          )
        )
      }
      if (branch.arity != expectedCtor.arity) {
        break(
          Left(
            KernelError(
              "K028",
              s"Constructor '${indName}.${expectedCtor.name}' expects ${expectedCtor.arity} field(s), " +
                s"but branch binds ${branch.arity}"
            )
          )
        )
      }
      val instFields = indEntry.instantiateFields(expectedCtor, params)
      val branchCtx = instFields.zip(branch.fieldNames).foldLeft(localCtx) { case (ctx, (binder, fieldName)) =>
        ctx.push(fieldName, binder.ty)
      }
      val expectedBranchType = indEntry.branchBodyType(expectedCtor, params, motive)
      check(kernelEnv, branchCtx, branch.body, expectedBranchType) match {
        case Left(err) => break(Left(err))
        case Right(()) => ()
      }
    }

    // 6. Result type is `motive(actualIndices..., scrutinee)`
    Right(Term.apps(motive, actualIndices :+ scrutinee))
  }

  private def extractMotiveTargetSort(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    indEntry: IndEntry,
    params: List[Term],
    motiveType: Term
  ): Either[KernelError, Sort] = boundary {
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(kernelEnv, localCtx, fuel)
    var curVal = NbE.evaluate(kernelEnv, evalEnv, motiveType, fuel)
    var curDepth = localCtx.depth
    val expectedIdxBinders = indEntry.instantiateIndices(params)

    // Verify each index binder
    var idxEvalEnv = evalEnv
    for ((expectedBinder, pos) <- expectedIdxBinders.zipWithIndex) {
      curVal match {
        case Value.VPi(_, actualDom, codomain) =>
          val expectedDomVal = NbE.evaluate(kernelEnv, idxEvalEnv, expectedBinder.ty, fuel)
          if (!NbE.areConvertible(kernelEnv, curDepth, actualDom, expectedDomVal, fuel)) {
            break(Left(KernelError("K029", s"Match motive index #$pos type mismatch")))
          }
          val freshVar = Value.VNeutral(NeutralHead.NVar(curDepth), Nil)
          curVal = NbE.applyClosure(kernelEnv, codomain, freshVar, fuel)
          idxEvalEnv = freshVar :: idxEvalEnv
          curDepth += 1
        case _ =>
          break(Left(KernelError("K029", s"Match motive has too few index binders for '${indEntry.name}'")))
      }
    }

    // Verify scrutinee binder: (s: Ind(params, idxVars)) => Sort(targetSort)
    val m = indEntry.numIndices
    val idxVars = (0 until m).toList.map(j => Term.Var(m - 1 - j))
    val expectedScrutTy = Term.apps(Term.Ind(indEntry.name), params.map(Term.shift(_, m)) ++ idxVars)
    val expectedScrutVal = NbE.evaluate(kernelEnv, idxEvalEnv, expectedScrutTy, fuel)

    curVal match {
      case Value.VPi(_, actualScrutDom, codomain) =>
        if (!NbE.areConvertible(kernelEnv, curDepth, actualScrutDom, expectedScrutVal, fuel)) {
          break(Left(KernelError("K029", s"Match motive scrutinee binder type mismatch for '${indEntry.name}'")))
        }
        val freshScrut = Value.VNeutral(NeutralHead.NVar(curDepth), Nil)
        val resultVal = NbE.applyClosure(kernelEnv, codomain, freshScrut, fuel)
        resultVal match {
          case Value.VSort(targetSort) => Right(targetSort)
          case _ =>
            Left(KernelError("K029", s"Match motive must return a Sort (Prop or Type), got '$resultVal'"))
        }
      case _ =>
        Left(KernelError("K029", s"Match motive must abstract over scrutinee of type '${indEntry.name}'"))
    }
  }
}
