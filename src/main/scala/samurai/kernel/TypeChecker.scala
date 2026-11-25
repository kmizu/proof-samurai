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

    // 0. Reject any reference to `partial def` inside inductive types, fields, or result indices (K031)!
    val leakedIndPartials =
      inductive.params.flatMap(b => kernelEnv.collectPartials(b.ty)).toSet ++
        inductive.indices.flatMap(b => kernelEnv.collectPartials(b.ty)).toSet ++
        inductive.constructors.flatMap { c =>
          c.fields.flatMap(f => kernelEnv.collectPartials(f.ty)) ++
            c.resultIndices.flatMap(kernelEnv.collectPartials)
        }.toSet
    if (leakedIndPartials.nonEmpty) {
      break(
        Left(
          KernelError(
            "K031",
            s"Inductive type '${inductive.name}' cannot reference partial function(s): ${leakedIndPartials.toList.sorted.mkString(", ")}"
          )
        )
      )
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

    // 7. Compute subsingleton status for Prop -> Type elimination soundness (standard CIC singleton elimination):
    // A Prop inductive is a subsingleton iff:
    // - it has 0 constructors (e.g. False), OR
    // - it has 1 constructor whose every field either lives in Prop OR is forced directly by a result index
    //   (e.g. Eq.Refl, True.Intro, And.Intro, and Acc.Intro(current, inv): Acc(current)).
    val checkedCtorList = checkedCtors.result()
    val isSubsingleton =
      inductive.sort == Sort.Prop && (
        checkedCtorList.isEmpty ||
          (checkedCtorList.length == 1 && {
            val soleCtor = checkedCtorList.head
            val numFields = soleCtor.arity
            soleCtor.fieldIsProp.zipWithIndex.forall { case (isPropField, fieldIdx) =>
              val fieldVarInResultIndices = Term.Var(numFields - 1 - fieldIdx)
              isPropField || soleCtor.resultIndices.contains(fieldVarInResultIndices)
            }
          })
      )

    val verifiedInd = inductive.copy(constructors = checkedCtorList, isSubsingleton = isSubsingleton)
    Right(kernelEnv.addInductive(verifiedInd))
  }

  /** Check and register a definition or theorem in `kernelEnv`. */
  def checkDef(
    kernelEnv: KernelEnv,
    name: String,
    declaredType: Term,
    body: Term,
    transparent: Boolean = true,
    isTheorem: Boolean = false,
    isPartial: Boolean = false
  ): Either[KernelError, KernelEnv] = {
    if (kernelEnv.contains(name)) {
      return Left(KernelError("K001", s"Duplicate declaration name '$name'"))
    }
    if (isPartial) {
      if (isTheorem) {
        return Left(KernelError("K030", s"Theorem '$name' cannot be declared partial"))
      }
      for {
        _ <- inferSort(kernelEnv, LocalCtx.empty, declaredType)
        _ <- checkPartialReturnType(kernelEnv, name, declaredType)
        // Register opaque self-reference so partial body may make unrestricted recursive calls via Term.Const(name),
        // while keeping Term.Fix strictly guarded and keeping NbE non-unfolding during type checking!
        tentativeSelf = DefEntry(
          name = name,
          ty = declaredType,
          body = Term.Const(name),
          transparent = false,
          isTheorem = false,
          axiomsUsed = Set.empty,
          isPartial = true
        )
        envWithSelf = kernelEnv.addDef(tentativeSelf)
        _ <- check(envWithSelf, LocalCtx.empty, body, declaredType)
      } yield {
        val axiomsUsed = kernelEnv.collectAxioms(declaredType) ++ kernelEnv.collectAxioms(body)
        kernelEnv.addDef(
          DefEntry(
            name = name,
            ty = declaredType,
            body = body,
            transparent = false,
            isTheorem = false,
            axiomsUsed = axiomsUsed,
            isPartial = true
          )
        )
      }
    } else {
      val leakedPartials = kernelEnv.collectPartials(declaredType) ++ kernelEnv.collectPartials(body)
      if (leakedPartials.nonEmpty) {
        return Left(
          KernelError(
            "K031",
            s"Total ${if (isTheorem) "theorem" else "definition"} '$name' cannot reference partial function(s): " +
              s"${leakedPartials.toList.sorted.mkString(", ")}"
          )
        )
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
            axiomsUsed = axiomsUsed,
            isPartial = false
          )
        )
      }
    }
  }

  /** Check and register a mutually recursive group of `partial def`s (all isolated from total code and Prop). */
  def checkMutualPartialDefs(
    kernelEnv: KernelEnv,
    entries: List[(String, Term, Term)]
  ): Either[KernelError, KernelEnv] = boundary {
    if (entries.isEmpty) {
      break(Left(KernelError("K030", "Mutual partial block cannot be empty")))
    }
    val names = entries.map(_._1)
    if (names.distinct.length != names.length) {
      break(Left(KernelError("K001", "Duplicate declaration names in mutual block")))
    }
    var tentativeEnv = kernelEnv
    for ((name, declaredType, _) <- entries) {
      if (kernelEnv.contains(name)) {
        break(Left(KernelError("K001", s"Duplicate declaration name '$name'")))
      }
      inferSort(kernelEnv, LocalCtx.empty, declaredType) match {
        case Left(err) => break(Left(err))
        case Right(_)  => ()
      }
      checkPartialReturnType(kernelEnv, name, declaredType) match {
        case Left(err) => break(Left(err))
        case Right(()) => ()
      }
      tentativeEnv = tentativeEnv.addDef(
        DefEntry(name, declaredType, Term.Const(name), transparent = false, isTheorem = false, axiomsUsed = Set.empty, isPartial = true)
      )
    }
    var finalEnv = kernelEnv
    for ((name, declaredType, body) <- entries) {
      check(tentativeEnv, LocalCtx.empty, body, declaredType) match {
        case Left(err) => break(Left(err))
        case Right(()) => ()
      }
      val axiomsUsed = kernelEnv.collectAxioms(declaredType) ++ kernelEnv.collectAxioms(body)
      finalEnv = finalEnv.addDef(
        DefEntry(
          name = name,
          ty = declaredType,
          body = body,
          transparent = false,
          isTheorem = false,
          axiomsUsed = axiomsUsed,
          isPartial = true
        )
      )
    }
    Right(finalEnv)
  }

  private def checkPartialReturnType(kernelEnv: KernelEnv, name: String, typeTerm: Term): Either[KernelError, Unit] = {
    var ctx = LocalCtx.empty
    var cur = NbE.normalize(kernelEnv, ctx, typeTerm)
    while (cur.isInstanceOf[Term.Pi]) {
      val Term.Pi(bName, domain, codomain) = cur: @unchecked
      ctx = ctx.push(bName, domain)
      cur = NbE.normalize(kernelEnv, ctx, codomain)
    }
    cur match {
      case Term.USort(_) =>
        Left(
          KernelError(
            "K030",
            s"Partial function '$name' cannot return a universe sort (Prop/Type); partial functions must return computational data"
          )
        )
      case _ =>
        inferSort(kernelEnv, ctx, cur).flatMap {
          case Sort.Prop =>
            Left(
              KernelError(
                "K030",
                s"Partial function '$name' cannot return a Prop type (would compromise logical soundness)"
              )
            )
          case _ => Right(())
        }
    }
  }

  /** Check and register an explicit axiom (or sorry) in `kernelEnv`. */
  def checkAxiom(kernelEnv: KernelEnv, name: String, declaredType: Term): Either[KernelError, KernelEnv] = {
    if (kernelEnv.contains(name)) {
      return Left(KernelError("K001", s"Duplicate declaration name '$name'"))
    }
    val leakedPartials = kernelEnv.collectPartials(declaredType)
    if (leakedPartials.nonEmpty) {
      return Left(
        KernelError(
          "K031",
          s"Axiom '$name' cannot reference partial function(s): ${leakedPartials.toList.sorted.mkString(", ")}"
        )
      )
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

    case Term.MutualFix(defs, selectedIndex) =>
      boundary {
        if (defs.isEmpty || selectedIndex < 0 || selectedIndex >= defs.length) {
          break(Left(KernelError("K020", s"Invalid MutualFix selection #$selectedIndex (size ${defs.length})")))
        }
        // 1. Check all declared types in `localCtx`
        for (d <- defs) {
          inferSort(kernelEnv, localCtx, d.ty) match {
            case Left(err) => break(Left(err))
            case Right(_)  => ()
          }
        }
        // 2. Push all `k` mutual binders into `mutualCtx` (d_j's type shifted by +j)
        val k = defs.length
        val mutualCtx = defs.zipWithIndex.foldLeft(localCtx) { case (ctxAcc, (d, j)) =>
          ctxAcc.push(d.name, Term.shift(d.ty, j))
        }
        // 3. Check each body against `shift(d.ty, k)`
        for (d <- defs) {
          check(kernelEnv, mutualCtx, d.body, Term.shift(d.ty, k)) match {
            case Left(err) => break(Left(err))
            case Right(()) => ()
          }
        }
        // 4. Verify mutual structural termination guard
        Termination.checkMutualFix(kernelEnv, localCtx, defs) match {
          case Left(msg) => break(Left(KernelError("K020", msg)))
          case Right(()) => ()
        }
        Right(defs(selectedIndex).ty)
      }
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
