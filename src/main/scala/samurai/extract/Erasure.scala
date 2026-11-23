package samurai.extract

import samurai.elab.ElabEnv
import samurai.kernel.*
import samurai.util.Json

enum ExtractedType {
  case TUnit
  case TVar(name: String)
  case TInd(name: String, typeArgs: List[ExtractedType])
  case TFun(domain: ExtractedType, codomain: ExtractedType)
  case TAny
}

final case class ExtractedCtor(
  name: String,
  fields: List[(String, ExtractedType)]
)

final case class ExtractedDataDecl(
  name: String,
  typeParams: List[String],
  isRecord: Boolean,
  constructors: List[ExtractedCtor]
)

enum ExtractedExpr {
  case EUnit
  case EUnreachable(reason: String)
  case EVar(name: String)
  case EConst(name: String, typeArgs: List[ExtractedType])
  case ECtor(indName: String, ctorName: String, typeArgs: List[ExtractedType], args: List[ExtractedExpr])
  case ELam(paramName: String, paramType: ExtractedType, body: ExtractedExpr)
  case EApp(callee: ExtractedExpr, arg: ExtractedExpr)
  case ELet(name: String, value: ExtractedExpr, body: ExtractedExpr)
  case EMatch(
    indName: String,
    scrutinee: ExtractedExpr,
    branches: List[(String, List[String], ExtractedExpr)]
  )
}

final case class ExtractedDefDecl(
  name: String,
  typeParams: List[String],
  valueParams: List[(String, ExtractedType)],
  returnType: ExtractedType,
  body: ExtractedExpr
)

final case class ExtractionManifest(
  extractedTypes: List[String],
  extractedFunctions: List[String],
  erasedPropositions: List[String],
  verifiedTheorems: List[String],
  axiomsUsed: Set[String]
) {
  def isAxiomFree: Boolean = axiomsUsed.isEmpty

  def toJson: Json = Json.obj(
    "extractedTypes" -> Json.Arr(extractedTypes.map(Json.Str(_))),
    "extractedFunctions" -> Json.Arr(extractedFunctions.map(Json.Str(_))),
    "erasedPropositions" -> Json.Arr(erasedPropositions.map(Json.Str(_))),
    "verifiedTheorems" -> Json.Arr(verifiedTheorems.map(Json.Str(_))),
    "axiomsUsed" -> Json.Arr(axiomsUsed.toList.sorted.map(Json.Str(_))),
    "isAxiomFree" -> Json.Bool(isAxiomFree)
  )
}

final case class ExtractedModule(
  moduleName: String,
  dataDecls: List[ExtractedDataDecl],
  defDecls: List[ExtractedDefDecl],
  manifest: ExtractionManifest
)

/**
 * Sound proof- and type-erasure pass from Trusted Kernel declarations to target-independent `ExtractedModule` IR.
 *
 * Guarantees:
 * - All `Prop` types, `theorem`s, and `Prop`-valued arguments/fields are completely erased.
 * - Subsingleton eliminations (`False`, `Eq`) erase soundly (`False` -> unreachable, `Eq` -> Refl branch).
 * - Computational semantics of all `Type`-valued functions and algebraic data types are preserved.
 */
object Erasure {

  final case class ExtractionOptions(
    moduleName: String = "ExtractedSamurai",
    requireAxiomFree: Boolean = false
  )

  def extract(
    elabEnv: ElabEnv,
    options: ExtractionOptions = ExtractionOptions()
  ): Either[String, ExtractedModule] = {
    val kernelEnv = elabEnv.kernelEnv

    if (options.requireAxiomFree && kernelEnv.allAxiomsUsed.nonEmpty) {
      return Left(
        s"Strict extraction rejected: environment uses axiom(s): ${kernelEnv.allAxiomsUsed.toList.sorted.mkString(", ")}"
      )
    }

    val dataDecls = List.newBuilder[ExtractedDataDecl]
    val defDecls = List.newBuilder[ExtractedDefDecl]
    val erasedProps = List.newBuilder[String]
    val verifiedTheorems = List.newBuilder[String]
    val allAxioms = Set.newBuilder[String]

    // Precompute parameter erasure masks for every inductive and def
    val indParamKeepMask: Map[String, List[Boolean]] = kernelEnv.inductives.map { case (name, ind) =>
      val mask = ind.params.map(b => isTypeParam(b.ty))
      name -> mask
    }

    val ctorFieldKeepMask: Map[(String, String), List[Boolean]] =
      kernelEnv.inductives.flatMap { case (indName, ind) =>
        ind.constructors.map { ctor =>
          val ctx0 = LocalCtx.empty.pushBinders(ind.params)
          var curCtx = ctx0
          val mask = ctor.fields.map { f =>
            val keep = isComputationalValueType(kernelEnv, curCtx, f.ty)
            curCtx = curCtx.push(f.name, f.ty)
            keep
          }
          (indName, ctor.name) -> mask
        }
      }

    // Track for each computational def: which leading binders are type params, which are kept value params
    val defRoles = scala.collection.mutable.Map.empty[String, List[Role]]

    for (declName <- kernelEnv.declOrder if !elabEnv.noExtractNames.contains(declName)) {
      kernelEnv.inductives.get(declName) match {
        case Some(ind) =>
          if (ind.sort == Sort.Prop) {
            erasedProps += ind.name
          } else {
            val typeParamNames = ind.params.collect {
              case b if isTypeParam(b.ty) => b.name
            }
            val paramCtx = LocalCtx.empty.pushBinders(ind.params)
            val extractedCtors = ind.constructors.map { ctor =>
              val keepMask = ctorFieldKeepMask((ind.name, ctor.name))
              var fieldCtx = paramCtx
              val keptFields = List.newBuilder[(String, ExtractedType)]
              for ((field, keep) <- ctor.fields.zip(keepMask)) {
                if (keep) {
                  val eTy = eraseType(kernelEnv, fieldCtx, field.ty, indParamKeepMask)
                  keptFields += (field.name -> eTy)
                }
                fieldCtx = fieldCtx.push(field.name, field.ty)
              }
              ExtractedCtor(ctor.name, keptFields.result())
            }
            dataDecls += ExtractedDataDecl(
              name = ind.name,
              typeParams = typeParamNames,
              isRecord = elabEnv.recordFields.contains(ind.name),
              constructors = extractedCtors
            )
          }

        case None =>
          kernelEnv.defs.get(declName).foreach { defEntry =>
            allAxioms ++= defEntry.axiomsUsed
            if (defEntry.isTheorem || isPropType(kernelEnv, LocalCtx.empty, defEntry.ty) || isTypeLevelDef(kernelEnv, defEntry.ty)) {
              verifiedTheorems += defEntry.name
            } else {
              // Split leading Pi binders of defEntry.ty
              val (roles, returnTypeCore, innerCtx) = analyzeDefSignature(kernelEnv, defEntry.ty, indParamKeepMask)
              defRoles(defEntry.name) = roles

              val typeParams = roles.collect { case Role.TParam(n) => n }
              val valueParams = roles.collect { case Role.VParam(n, t) => (n, t) }
              val retType = eraseType(kernelEnv, innerCtx, returnTypeCore, indParamKeepMask)

              // Peel Fix / Lam matching the signature binders
              val (bodyCore, ctxForBody, selfNameOpt) = peelDefBody(defEntry.name, defEntry.body, roles.length, innerCtx)
              val eraseEnv = buildEraseNameEnv(roles, selfNameOpt)
              val extractedBody = eraseTerm(
                kernelEnv,
                ctxForBody,
                bodyCore,
                eraseEnv,
                indParamKeepMask,
                ctorFieldKeepMask,
                defRoles.toMap
              )

              defDecls += ExtractedDefDecl(
                name = defEntry.name,
                typeParams = typeParams,
                valueParams = valueParams,
                returnType = retType,
                body = extractedBody
              )
            }
          }
      }
    }

    val finalData = dataDecls.result()
    val finalDefs = defDecls.result()
    val manifest = ExtractionManifest(
      extractedTypes = finalData.map(_.name),
      extractedFunctions = finalDefs.map(_.name),
      erasedPropositions = erasedProps.result(),
      verifiedTheorems = verifiedTheorems.result(),
      axiomsUsed = allAxioms.result() ++ kernelEnv.allAxiomsUsed
    )

    Right(ExtractedModule(options.moduleName, finalData, finalDefs, manifest))
  }

  private def isTypeParam(binderTy: Term): Boolean = binderTy match {
    case Term.USort(Sort.Type(_)) => true
    case _                        => false
  }

  private def isPropType(kernelEnv: KernelEnv, localCtx: LocalCtx, termType: Term): Boolean =
    TypeChecker.inferSort(kernelEnv, localCtx, termType).contains(Sort.Prop)

  private def isTypeLevelDef(kernelEnv: KernelEnv, defType: Term): Boolean = {
    def codomainIsSort(t: Term): Boolean = t match {
      case Term.USort(_)    => true
      case Term.Pi(_, _, c) => codomainIsSort(c)
      case _                => false
    }
    codomainIsSort(NbE.normalize(kernelEnv, LocalCtx.empty, defType))
  }

  private def isComputationalValueType(kernelEnv: KernelEnv, localCtx: LocalCtx, fieldTy: Term): Boolean = {
    val norm = NbE.normalize(kernelEnv, localCtx, fieldTy)
    norm match {
      case Term.USort(_) => false
      case _ =>
        !isPropType(kernelEnv, localCtx, norm)
    }
  }

  private sealed trait Role
  private object Role {
    final case class TParam(name: String) extends Role
    final case class VParam(name: String, extractedTy: ExtractedType) extends Role
    case object Erased extends Role
  }

  private def analyzeDefSignature(
    kernelEnv: KernelEnv,
    defType: Term,
    indParamKeepMask: Map[String, List[Boolean]]
  ): (List[Role], Term, LocalCtx) = {
    var cur = defType
    var ctx = LocalCtx.empty
    val roles = List.newBuilder[Role]
    var stillTypePrefix = true

    while (cur.isInstanceOf[Term.Pi]) {
      val Term.Pi(name, domain, codomain) = cur: @unchecked
      val cleanName = if (name == "_" || name.isEmpty) s"_p${ctx.depth}" else name
      val role =
        if (stillTypePrefix && isTypeParam(domain)) {
          Role.TParam(cleanName)
        } else {
          stillTypePrefix = false
          if (isComputationalValueType(kernelEnv, ctx, domain)) {
            Role.VParam(cleanName, eraseType(kernelEnv, ctx, domain, indParamKeepMask))
          } else {
            Role.Erased
          }
        }
      roles += role
      ctx = ctx.push(cleanName, domain)
      cur = codomain
    }

    (roles.result(), cur, ctx)
  }

  private def peelDefBody(
    defName: String,
    body: Term,
    numBinders: Int,
    sigCtx: LocalCtx
  ): (Term, LocalCtx, Option[String]) = {
    val (unwrapped, selfOpt, baseCtx) = body match {
      case Term.Fix(fixName, _, fixTy, inner) =>
        (inner, Some(defName), LocalCtx.empty.push(fixName, fixTy))
      case other =>
        (other, None, LocalCtx.empty)
    }

    var cur = unwrapped
    var remaining = numBinders
    var ctx = baseCtx
    val sigEntriesOuterToInner = sigCtx.entries.reverse
    var entryIdx = 0

    while (remaining > 0) {
      cur match {
        case Term.Lam(name, dom, inner) =>
          val binderName = if (entryIdx < sigEntriesOuterToInner.length) sigEntriesOuterToInner(entryIdx).name else name
          ctx = ctx.push(binderName, dom)
          cur = inner
          remaining -= 1
          entryIdx += 1
        case _ =>
          remaining = 0
      }
    }
    (cur, ctx, selfOpt)
  }

  private def buildEraseNameEnv(roles: List[Role], selfNameOpt: Option[String]): List[Option[String]] = {
    val base: List[Option[String]] = selfNameOpt.map(Some(_)).toList
    roles.foldLeft(base) { (env, role) =>
      role match {
        case Role.VParam(n, _) => Some(n) :: env
        case _                 => None :: env
      }
    }
  }

  private def eraseType(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    typeTerm: Term,
    indParamKeepMask: Map[String, List[Boolean]]
  ): ExtractedType = {
    val norm = NbE.normalize(kernelEnv, localCtx, typeTerm)
    if (isPropType(kernelEnv, localCtx, norm)) return ExtractedType.TUnit

    norm match {
      case Term.USort(_) => ExtractedType.TUnit
      case Term.Var(idx) =>
        if (idx >= 0 && idx < localCtx.entries.length) ExtractedType.TVar(localCtx.entries(idx).name)
        else ExtractedType.TAny
      case Term.Pi(name, domain, codomain) =>
        val nextCtx = localCtx.push(name, domain)
        if (!isComputationalValueType(kernelEnv, localCtx, domain)) {
          // Proof/type parameter is erased from runtime function type!
          eraseType(kernelEnv, nextCtx, codomain, indParamKeepMask)
        } else {
          ExtractedType.TFun(
            eraseType(kernelEnv, localCtx, domain, indParamKeepMask),
            eraseType(kernelEnv, nextCtx, codomain, indParamKeepMask)
          )
        }
      case other =>
        val (head, args) = Term.splitApps(other)
        head match {
          case Term.Ind(indName) =>
            kernelEnv.inductives.get(indName) match {
              case Some(ind) if ind.sort == Sort.Prop => ExtractedType.TUnit
              case Some(ind) =>
                val mask = indParamKeepMask.getOrElse(indName, Nil)
                val paramArgs = args.take(ind.numParams)
                val keptTypeArgs = paramArgs.zip(mask).collect {
                  case (arg, true) => eraseType(kernelEnv, localCtx, arg, indParamKeepMask)
                }
                ExtractedType.TInd(indName, keptTypeArgs)
              case None => ExtractedType.TAny
            }
          case _ => ExtractedType.TAny
        }
    }
  }

  private def eraseTerm(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    term: Term,
    nameEnv: List[Option[String]],
    indParamKeepMask: Map[String, List[Boolean]],
    ctorFieldKeepMask: Map[(String, String), List[Boolean]],
    defRoles: Map[String, List[Role]]
  ): ExtractedExpr = {
    term match {
      case Term.USort(_) => ExtractedExpr.EUnit

      case Term.Var(idx) =>
        if (idx >= 0 && idx < nameEnv.length) {
          nameEnv(idx) match {
            case Some(name) => ExtractedExpr.EVar(name)
            case None       => ExtractedExpr.EUnit
          }
        } else ExtractedExpr.EUnit

      case Term.Const(constName) =>
        ExtractedExpr.EConst(constName, Nil)

      case Term.Ind(_) =>
        ExtractedExpr.EUnit

      case Term.Ctor(indName, ctorName) =>
        if (kernelEnv.inductives.get(indName).exists(_.sort == Sort.Prop)) ExtractedExpr.EUnit
        else ExtractedExpr.ECtor(indName, ctorName, Nil, Nil)

      case Term.Lam(name, domain, body) =>
        val cleanName = if (name == "_" || name.isEmpty) s"_x${localCtx.depth}" else name
        val nextCtx = localCtx.push(cleanName, domain)
        if (!isComputationalValueType(kernelEnv, localCtx, domain)) {
          eraseTerm(kernelEnv, nextCtx, body, None :: nameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)
        } else {
          val eDom = eraseType(kernelEnv, localCtx, domain, indParamKeepMask)
          val eBody = eraseTerm(kernelEnv, nextCtx, body, Some(cleanName) :: nameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)
          ExtractedExpr.ELam(cleanName, eDom, eBody)
        }

      case Term.Let(name, ty, value, body) =>
        val cleanName = if (name == "_" || name.isEmpty) s"_v${localCtx.depth}" else name
        val nextCtx = localCtx.push(cleanName, ty, Some(value))
        if (!isComputationalValueType(kernelEnv, localCtx, ty)) {
          eraseTerm(kernelEnv, nextCtx, body, None :: nameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)
        } else {
          val eVal = eraseTerm(kernelEnv, localCtx, value, nameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)
          val eBody = eraseTerm(kernelEnv, nextCtx, body, Some(cleanName) :: nameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)
          ExtractedExpr.ELet(cleanName, eVal, eBody)
        }

      case app @ Term.App(_, _) =>
        val (head, args) = Term.splitApps(app)
        head match {
          case Term.Ctor(indName, ctorName) =>
            kernelEnv.inductives.get(indName) match {
              case Some(ind) if ind.sort == Sort.Prop => ExtractedExpr.EUnit
              case Some(ind) =>
                val paramMask = indParamKeepMask.getOrElse(indName, Nil)
                val (paramArgs, fieldArgs) = args.splitAt(ind.numParams)
                val keptTypeArgs = paramArgs.zip(paramMask).collect {
                  case (a, true) => eraseType(kernelEnv, localCtx, a, indParamKeepMask)
                }
                val fieldMask = ctorFieldKeepMask.getOrElse((indName, ctorName), fieldArgs.map(_ => true))
                val keptFieldArgs = fieldArgs.zip(fieldMask).collect {
                  case (a, true) =>
                    eraseTerm(kernelEnv, localCtx, a, nameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)
                }
                ExtractedExpr.ECtor(indName, ctorName, keptTypeArgs, keptFieldArgs)
              case None => ExtractedExpr.EUnit
            }

          case Term.Const(constName) if defRoles.contains(constName) =>
            applyWithRoles(kernelEnv, localCtx, ExtractedExpr.EConst(constName, Nil), Some(constName), args, defRoles(constName), nameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)

          case Term.Var(idx) if idx >= 0 && idx < nameEnv.length && nameEnv(idx).exists(defRoles.contains) =>
            val selfName = nameEnv(idx).get
            applyWithRoles(kernelEnv, localCtx, ExtractedExpr.EVar(selfName), Some(selfName), args, defRoles(selfName), nameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)

          case _ =>
            val eHead = eraseTerm(kernelEnv, localCtx, head, nameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)
            args.foldLeft(eHead) { (acc, arg) =>
              val argIsComp = TypeChecker.infer(kernelEnv, localCtx, arg).toOption.forall(t =>
                isComputationalValueType(kernelEnv, localCtx, t)
              )
              if (!argIsComp) acc
              else ExtractedExpr.EApp(acc, eraseTerm(kernelEnv, localCtx, arg, nameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles))
            }
        }

      case matchTerm @ Term.Match(indName, params, _, scrutinee, branches) =>
        kernelEnv.inductives.get(indName) match {
          case Some(ind) if ind.sort == Sort.Prop =>
            // Sound subsingleton Prop elimination erasure!
            branches match {
              case Nil =>
                ExtractedExpr.EUnreachable(s"eliminated empty Prop '$indName'")
              case List(singleBranch) =>
                // Eq.Refl / True.Intro / And.Intro -> erase scrutinee and evaluate branch directly!
                val ctor = ind.constructors.head
                val instFields = ind.instantiateFields(ctor, params)
                val branchCtx = instFields.zip(singleBranch.fieldNames).foldLeft(localCtx) { case (c, (b, n)) =>
                  c.push(n, b.ty)
                }
                val branchNameEnv = List.fill(singleBranch.arity)(None) ++ nameEnv
                eraseTerm(kernelEnv, branchCtx, singleBranch.body, branchNameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)
              case _ =>
                ExtractedExpr.EUnreachable(s"unexpected multi-branch Prop match on '$indName'")
            }

          case Some(ind) =>
            val eScrut = eraseTerm(kernelEnv, localCtx, scrutinee, nameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)
            val overallErasedTypeOpt =
              if (ind.numIndices > 0)
                TypeChecker.infer(kernelEnv, localCtx, matchTerm).toOption.map(eraseType(kernelEnv, localCtx, _, indParamKeepMask))
              else None

            val eBranches = branches.zip(ind.constructors).map { case (br, ctor) =>
              val instFields = ind.instantiateFields(ctor, params)
              val keepMask = ctorFieldKeepMask.getOrElse((indName, ctor.name), List.fill(ctor.arity)(true))
              val branchCtx = instFields.zip(br.fieldNames).foldLeft(localCtx) { case (c, (b, n)) =>
                c.push(n, b.ty)
              }
              val keptFieldNames = List.newBuilder[String]
              val branchNameEnv = br.fieldNames.zip(keepMask).foldLeft(nameEnv) { case (envAcc, (fName, keep)) =>
                if (keep) {
                  val safeName = if (fName == "_" || fName.isEmpty) "_" else fName
                  keptFieldNames += safeName
                  Some(safeName) :: envAcc
                } else {
                  None :: envAcc
                }
              }
              // For indexed families (e.g. Vec[A](Succ(n))), detect provably unreachable dummy branches
              // whose erased type differs from the overall match type (e.g. Unit vs Element) and emit EUnreachable!
              val isUnreachableIndexedBranch = overallErasedTypeOpt.exists { expectedErasedTy =>
                TypeChecker.infer(kernelEnv, branchCtx, br.body).toOption.exists { branchTy =>
                  val erasedBranchTy = eraseType(kernelEnv, branchCtx, branchTy, indParamKeepMask)
                  erasedBranchTy != expectedErasedTy
                }
              }
              val eBody =
                if (isUnreachableIndexedBranch) {
                  ExtractedExpr.EUnreachable(s"impossible indexed branch $indName.${ctor.name}")
                } else {
                  eraseTerm(kernelEnv, branchCtx, br.body, branchNameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)
                }
              (ctor.name, keptFieldNames.result(), eBody)
            }
            ExtractedExpr.EMatch(indName, eScrut, eBranches)

          case None => ExtractedExpr.EUnit
        }

      case Term.Fix(_, _, _, body) =>
        eraseTerm(kernelEnv, localCtx, body, None :: nameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)

      case Term.Pi(_, _, _) => ExtractedExpr.EUnit
    }
  }

  private def applyWithRoles(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    baseExpr: ExtractedExpr,
    constNameOpt: Option[String],
    args: List[Term],
    roles: List[Role],
    nameEnv: List[Option[String]],
    indParamKeepMask: Map[String, List[Boolean]],
    ctorFieldKeepMask: Map[(String, String), List[Boolean]],
    defRoles: Map[String, List[Role]]
  ): ExtractedExpr = {
    val typeArgs = List.newBuilder[ExtractedType]
    val valueArgs = List.newBuilder[ExtractedExpr]

    for ((arg, idx) <- args.zipWithIndex) {
      if (idx < roles.length) {
        roles(idx) match {
          case Role.TParam(_) =>
            typeArgs += eraseType(kernelEnv, localCtx, arg, indParamKeepMask)
          case Role.VParam(_, _) =>
            valueArgs += eraseTerm(kernelEnv, localCtx, arg, nameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)
          case Role.Erased => ()
        }
      } else {
        // Extra curried argument beyond declared signature
        valueArgs += eraseTerm(kernelEnv, localCtx, arg, nameEnv, indParamKeepMask, ctorFieldKeepMask, defRoles)
      }
    }

    val headWithTypes = constNameOpt match {
      case Some(name) => ExtractedExpr.EConst(name, typeArgs.result())
      case None       => baseExpr
    }
    valueArgs.result().foldLeft(headWithTypes)(ExtractedExpr.EApp(_, _))
  }
}
