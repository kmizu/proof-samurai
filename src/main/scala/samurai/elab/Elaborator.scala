package samurai.elab

import java.nio.file.{Files, Path}
import scala.util.boundary
import scala.util.boundary.break
import samurai.kernel.*
import samurai.syntax.*
import samurai.tactic.{ProofState, Tactics}
import samurai.util.{Diagnostic, Json, Span}

final case class HoleInfo(
  name: Option[String],
  span: Span,
  localCtx: LocalCtx,
  expectedType: Term
) {
  def toJson(kernelEnv: KernelEnv): Json = {
    val hyps = List.newBuilder[Json]
    var prefixNames: List[String] = Nil
    for (entry <- localCtx.entries.reverse) {
      hyps += Json.obj(
        "name" -> Json.Str(entry.name),
        "type" -> Json.Str(Pretty.show(entry.ty, prefixNames))
      )
      prefixNames = entry.name :: prefixNames
    }
    Json.obj(
      "name" -> name.map(Json.Str(_)).getOrElse(Json.Null),
      "span" -> span.toJson,
      "hypotheses" -> Json.Arr(hyps.result()),
      "expectedType" -> Json.Str(Pretty.show(NbE.normalize(kernelEnv, localCtx, expectedType), localCtx.names))
    )
  }
}

final case class DirectiveResult(
  directive: String,
  output: String,
  span: Span
) {
  def toJson: Json = Json.obj(
    "directive" -> Json.Str(directive),
    "output" -> Json.Str(output),
    "span" -> span.toJson
  )
}

final case class WfContext(
  fnName: String,
  wfHelperName: String,
  numBinders: Int,
  measureCore: Term, // in depth = numBinders (binders 0..numBinders-1)
  wfSelfLevel: Int,
  wfCurMeasureLevel: Int,
  wfInvLevel: Int,
  wfEqMLevel: Int,
  decreasingBy: Option[List[TacticStmt]]
)

/**
 * Rich surface-level elaboration environment backed by the immutable Trusted KernelEnv.
 */
final case class ElabEnv(
  kernelEnv: KernelEnv = KernelEnv.empty,
  implicitParamCounts: Map[String, Int] = Map.empty,
  shortConstructors: Map[String, List[(String, String)]] = Map.empty,
  recordFields: Map[String, List[String]] = Map.empty,
  simpLemmas: List[String] = Nil,
  hintLemmas: List[String] = Nil,
  wfHints: List[String] = Nil,
  noExtractNames: Set[String] = Set.empty,
  loadedModules: Set[String] = Set.empty,
  searchPaths: List[Path] = Nil,
  holes: List[HoleInfo] = Nil,
  directives: List[DirectiveResult] = Nil,
  holeCollectionMode: Boolean = false,
  localRecursiveNames: Set[String] = Set.empty,
  wfContext: Option[WfContext] = None
) {
  def withSearchPaths(paths: List[Path]): ElabEnv = copy(searchPaths = paths)

  def registerShortCtor(indName: String, ctorName: String): ElabEnv = {
    val existing = shortConstructors.getOrElse(ctorName, Nil)
    if (existing.contains((indName, ctorName))) this
    else copy(shortConstructors = shortConstructors + (ctorName -> ((indName, ctorName) :: existing)))
  }

  def ensureSorryAxiom: (ElabEnv, String) = {
    val sorryName = "$sorry"
    if (kernelEnv.axioms.contains(sorryName)) {
      (this, sorryName)
    } else {
      // axiom $sorry: (A: Type0) => A  (and a Prop version $sorryProp: (P: Prop) => P)
      val sorryPropName = "$sorryProp"
      val env1 = TypeChecker
        .checkAxiom(kernelEnv, sorryName, Term.Pi("A", Term.USort(Sort.Type(0)), Term.Var(0)))
        .fold(_ => kernelEnv, identity)
      val env2 = TypeChecker
        .checkAxiom(env1, sorryPropName, Term.Pi("P", Term.USort(Sort.Prop), Term.Var(0)))
        .fold(_ => env1, identity)
      (copy(kernelEnv = env2), sorryName)
    }
  }
}

final case class ElabError(diagnostic: Diagnostic)

/**
 * Bidirectional surface-to-core elaborator for Proof Samurai.
 *
 * Translates programmer-friendly Scala 3 brace syntax into explicit Core Kernel Terms,
 * performs implicit type argument inference via unification, compiles patterns and case classes,
 * runs tactic scripts, and ALWAYS validates every final declaration through the Trusted Kernel.
 */
object Elaborator {

  def checkSource(
    file: String,
    source: String,
    initialEnv: ElabEnv = ElabEnv()
  ): Either[Diagnostic, ElabEnv] =
    Parser.parseFile(file, source).flatMap(decls => elaborateDecls(initialEnv, decls))

  def checkFile(path: Path, initialEnv: ElabEnv = ElabEnv()): Either[Diagnostic, ElabEnv] = {
    if (!Files.exists(path)) {
      Left(Diagnostic(Diagnostic.Severity.Error, "E001", s"File not found: $path", Span.synthetic))
    } else {
      val content = Files.readString(path)
      val parentDir = Option(path.toAbsolutePath.getParent)
      val envWithPath = parentDir match {
        case Some(dir) if !initialEnv.searchPaths.contains(dir) =>
          initialEnv.copy(searchPaths = dir :: initialEnv.searchPaths)
        case _ => initialEnv
      }
      checkSource(path.toString, content, envWithPath)
    }
  }

  def elaborateDecls(initialEnv: ElabEnv, decls: List[TopDecl]): Either[Diagnostic, ElabEnv] = {
    boundary {
      var currentEnv = initialEnv
      for (decl <- decls) {
        elaborateDecl(currentEnv, decl) match {
          case Left(err)      => break(Left(err))
          case Right(nextEnv) => currentEnv = nextEnv
        }
      }
      Right(currentEnv)
    }
  }

  def elaborateDecl(env: ElabEnv, decl: TopDecl): Either[Diagnostic, ElabEnv] = decl match {
    case TopDecl.ModuleDecl(moduleName, innerDecls, _) =>
      elaborateDecls(env.copy(loadedModules = env.loadedModules + moduleName), innerDecls)

    case TopDecl.ImportDecl(moduleName, _, span) =>
      if (env.loadedModules.contains(moduleName)) {
        Right(env)
      } else {
        resolveModuleFile(env.searchPaths, moduleName) match {
          case Some(filePath) =>
            checkFile(filePath, env.copy(loadedModules = env.loadedModules + moduleName))
          case None =>
            Left(
              Diagnostic(
                Diagnostic.Severity.Error,
                "E002",
                s"Cannot find module '$moduleName' in search paths: ${env.searchPaths.mkString(", ")}",
                span,
                hint = Some(s"Ensure '${moduleName}.samurai' exists in the workspace or stdlib directory")
              )
            )
        }
      }

    case enumDecl: TopDecl.EnumDecl =>
      elaborateEnum(env, enumDecl)

    case caseClassDecl: TopDecl.CaseClassDecl =>
      elaborateCaseClass(env, caseClassDecl)

    case defDecl: TopDecl.DefDecl =>
      elaborateDef(env, defDecl)

    case mutualDecl: TopDecl.MutualDecl =>
      elaborateMutual(env, mutualDecl)

    case valDecl: TopDecl.ValDecl =>
      elaborateVal(env, valDecl)

    case axiomDecl: TopDecl.AxiomDecl =>
      elaborateAxiom(env, axiomDecl)

    case TopDecl.DirectiveDecl(dirName, target, span) =>
      elaborateDirective(env, dirName, target, span)
  }

  private def resolveModuleFile(searchPaths: List[Path], moduleName: String): Option[Path] = {
    val fileName = s"$moduleName.samurai"
    searchPaths.iterator
      .flatMap(dir => List(dir.resolve(fileName), dir.resolve("stdlib").resolve(fileName)))
      .find(Files.exists(_))
  }

  // ===========================================================================
  // Enum & Case Class Elaboration
  // ===========================================================================

  private def elaborateEnum(env: ElabEnv, decl: TopDecl.EnumDecl): Either[Diagnostic, ElabEnv] = {
    boundary {
      val metaCtx = new MetaContext()

      // 1. Elaborate type parameters (default type is Type0)
      var paramCtx = LocalCtx.empty
      val paramBinders = List.newBuilder[Binder]
      for (param <- decl.typeParams) {
        val paramType = param.typeAnnotation match {
          case Some(ann) =>
            elaborateType(env, metaCtx, paramCtx, ann) match {
              case Left(err) => break(Left(err))
              case Right(t)  => metaCtx.zonk(t, paramCtx.depth)
            }
          case None =>
            Term.USort(Sort.Type(0))
        }
        paramBinders += Binder(param.name, paramType)
        paramCtx = paramCtx.push(param.name, paramType)
      }
      val params = paramBinders.result()

      // 2. Elaborate index parameters under params
      var indexCtx = paramCtx
      val indexBinders = List.newBuilder[Binder]
      for (idxParam <- decl.indexParams) {
        val idxType = idxParam.typeAnnotation match {
          case Some(ann) =>
            elaborateType(env, metaCtx, indexCtx, ann) match {
              case Left(err) => break(Left(err))
              case Right(t)  => metaCtx.zonk(t, indexCtx.depth)
            }
          case None =>
            break(Left(Diagnostic(Diagnostic.Severity.Error, "E003", s"Index parameter '${idxParam.name}' requires a type annotation", idxParam.span)))
        }
        indexBinders += Binder(idxParam.name, idxType)
        indexCtx = indexCtx.push(idxParam.name, idxType)
      }
      val indices = indexBinders.result()

      // 3. Determine result Sort (defaults to Type(0))
      val resultSort: Sort = decl.sortAnnotation match {
        case None => Sort.Type(0)
        case Some(SurfaceExpr.SortExpr(true, _, _))  => Sort.Prop
        case Some(SurfaceExpr.SortExpr(false, l, _)) => Sort.Type(l)
        case Some(other) =>
          break(Left(Diagnostic(Diagnostic.Severity.Error, "E004", s"Enum sort must be 'Type', 'TypeN', or 'Prop'", other.span)))
      }

      // 4. Create tentative env so constructor fields can reference `decl.name`
      val tentativeInd = IndEntry(decl.name, params, indices, resultSort, Nil)
      val tentativeEnv = env.copy(
        kernelEnv = env.kernelEnv.addInductive(tentativeInd),
        implicitParamCounts = env.implicitParamCounts + (decl.name -> params.length)
      )

      // 5. Elaborate each constructor case
      val ctorEntries = List.newBuilder[CtorEntry]
      for (c <- decl.cases) {
        var fieldCtx = paramCtx
        val fieldBinders = List.newBuilder[Binder]
        for (field <- c.fields) {
          val fieldType = field.typeAnnotation match {
            case Some(ann) =>
              elaborateType(tentativeEnv, metaCtx, fieldCtx, ann) match {
                case Left(err) => break(Left(err))
                case Right(t)  => metaCtx.zonk(t, fieldCtx.depth)
              }
            case None =>
              break(Left(Diagnostic(Diagnostic.Severity.Error, "E005", s"Constructor field '${field.name}' requires a type annotation", field.span)))
          }
          fieldBinders += Binder(field.name, fieldType)
          fieldCtx = fieldCtx.push(field.name, fieldType)
        }
        val fields = fieldBinders.result()

        val resultIndices: List[Term] = c.resultType match {
          case None =>
            if (indices.nonEmpty) {
              break(
                Left(
                  Diagnostic(
                    Diagnostic.Severity.Error,
                    "E006",
                    s"Indexed enum constructor '${decl.name}.${c.name}' must specify return type with ${indices.length} index argument(s)",
                    c.span
                  )
                )
              )
            } else Nil

          case Some(retExpr) =>
            val elaboratedRet = elaborateType(tentativeEnv, metaCtx, fieldCtx, retExpr) match {
              case Left(err) => break(Left(err))
              case Right(t)  => metaCtx.zonk(t, fieldCtx.depth)
            }
            val (head, allArgs) = Term.splitApps(elaboratedRet)
            if (head != Term.Ind(decl.name)) {
              break(
                Left(
                  Diagnostic(
                    Diagnostic.Severity.Error,
                    "E007",
                    s"Constructor '${decl.name}.${c.name}' must return '${decl.name}', found '${Pretty.show(elaboratedRet, fieldCtx.names)}'",
                    retExpr.span
                  )
                )
              )
            }
            if (allArgs.length != params.length + indices.length) {
              break(
                Left(
                  Diagnostic(
                    Diagnostic.Severity.Error,
                    "E008",
                    s"Constructor '${decl.name}.${c.name}' return type has ${allArgs.length} argument(s), expected ${params.length + indices.length}",
                    retExpr.span
                  )
                )
              )
            }
            allArgs.drop(params.length)
        }

        ctorEntries += CtorEntry(c.name, fields, resultIndices)
      }

      val finalInd = IndEntry(decl.name, params, indices, resultSort, ctorEntries.result())

      // 6. Validate through the Trusted Kernel!
      TypeChecker.checkInductive(env.kernelEnv, finalInd) match {
        case Left(kErr) =>
          Left(Diagnostic(Diagnostic.Severity.Error, kErr.code, kErr.message, decl.span))
        case Right(checkedKernelEnv) =>
          var updatedEnv = env.copy(
            kernelEnv = checkedKernelEnv,
            implicitParamCounts = env.implicitParamCounts + (decl.name -> params.length)
          )
          for (ctor <- finalInd.constructors) {
            updatedEnv = updatedEnv
              .copy(implicitParamCounts = updatedEnv.implicitParamCounts + (s"${decl.name}.${ctor.name}" -> params.length))
              .registerShortCtor(decl.name, ctor.name)
          }
          if (decl.annotations.exists(_.name == "noextract")) {
            updatedEnv = updatedEnv.copy(noExtractNames = updatedEnv.noExtractNames + decl.name)
          }
          Right(updatedEnv)
      }
    }
  }

  private def elaborateCaseClass(env: ElabEnv, decl: TopDecl.CaseClassDecl): Either[Diagnostic, ElabEnv] = {
    val enumDecl = new TopDecl.EnumDecl(
      annotations = decl.annotations,
      name = decl.name,
      typeParams = decl.typeParams,
      indexParams = Nil,
      sortAnnotation = decl.sortAnnotation,
      cases = List(EnumCaseDecl("Mk", decl.fields, None, decl.span)),
      span = decl.span
    )
    elaborateEnum(env, enumDecl).map { envAfterEnum =>
      envAfterEnum.copy(
        recordFields = envAfterEnum.recordFields + (decl.name -> decl.fields.map(_.name))
      )
    }
  }

  // ===========================================================================
  // Def / Theorem / Val / Axiom Elaboration
  // ===========================================================================

  private def elaborateDef(env: ElabEnv, decl: TopDecl.DefDecl): Either[Diagnostic, ElabEnv] = {
    if (decl.isPartial && decl.isTheorem) {
      return Left(Diagnostic(Diagnostic.Severity.Error, "E016", s"Theorem '${decl.name}' cannot be declared partial", decl.span))
    }
    if (decl.isPartial && decl.terminationBy.isDefined) {
      return Left(Diagnostic(Diagnostic.Severity.Error, "E016", s"Partial function '${decl.name}' does not need a termination_by clause", decl.span))
    }
    if (decl.terminationBy.isDefined) {
      return elaborateWellFoundedDef(env, decl)
    }

    boundary {
      val metaCtx = new MetaContext()
      var localCtx = LocalCtx.empty
      val allBinders = List.newBuilder[Binder]

      // 1. Type parameters (implicit)
      for (tp <- decl.typeParams) {
        val paramType = tp.typeAnnotation match {
          case Some(ann) =>
            elaborateType(env, metaCtx, localCtx, ann) match {
              case Left(err) => break(Left(err))
              case Right(t)  => metaCtx.zonk(t, localCtx.depth)
            }
          case None => Term.USort(Sort.Type(0))
        }
        allBinders += Binder(tp.name, paramType)
        localCtx = localCtx.push(tp.name, paramType)
      }

      // 2. Value parameters
      for (vp <- decl.valueParams) {
        val paramType = vp.typeAnnotation match {
          case Some(ann) =>
            elaborateType(env, metaCtx, localCtx, ann) match {
              case Left(err) => break(Left(err))
              case Right(t)  => metaCtx.zonk(t, localCtx.depth)
            }
          case None =>
            break(Left(Diagnostic(Diagnostic.Severity.Error, "E010", s"Parameter '${vp.name}' in '${decl.name}' requires a type annotation", vp.span)))
        }
        allBinders += Binder(vp.name, paramType)
        localCtx = localCtx.push(vp.name, paramType)
      }

      val binders = allBinders.result()
      val isRecursive = !decl.body.isInstanceOf[SurfaceExpr.TacticBlockExpr] && mentionsIdent(decl.body, decl.name)

      // 3. Return type
      val returnTypeCore: Term = decl.returnType match {
        case Some(retExpr) =>
          elaborateType(env, metaCtx, localCtx, retExpr) match {
            case Left(err) => break(Left(err))
            case Right(t)  => metaCtx.zonk(t, localCtx.depth)
          }
        case None if isRecursive || decl.isPartial =>
          break(Left(Diagnostic(Diagnostic.Severity.Error, "E011", s"Recursive/partial function '${decl.name}' requires an explicit return type", decl.span)))
        case None =>
          metaCtx.freshMeta(localCtx.depth, Term.USort(Sort.Type(0)), Some("returnType"))
      }

      val fullTypeRaw = Term.pis(binders, returnTypeCore)

      // 4. Elaborate body (partial def, tactic block, non-recursive, or structural Fix)
      var currentEnv = env
      val finalBodyTerm: Term =
        if (decl.isPartial) {
          val fullTypeZonked = metaCtx.zonk(fullTypeRaw, 0)
          val tentativeSelf = DefEntry(
            name = decl.name,
            ty = fullTypeZonked,
            body = Term.Const(decl.name),
            transparent = false,
            isTheorem = false,
            axiomsUsed = Set.empty,
            isPartial = true
          )
          val envWithSelf = currentEnv.copy(
            kernelEnv = currentEnv.kernelEnv.addDef(tentativeSelf),
            implicitParamCounts = currentEnv.implicitParamCounts + (decl.name -> decl.typeParams.length)
          )
          val (elabBody, envAfterBody) = checkExpr(envWithSelf, metaCtx, localCtx, decl.body, returnTypeCore) match {
            case Left(err)  => break(Left(err))
            case Right(res) => res
          }
          currentEnv = currentEnv.copy(
            holes = envAfterBody.holes,
            directives = envAfterBody.directives
          )
          val zonkedBody = metaCtx.zonk(elabBody, localCtx.depth)
          checkAllMetasSolved(metaCtx, decl.span) match {
            case Left(err) => break(Left(err))
            case Right(()) => ()
          }
          Term.lams(binders, zonkedBody)
        } else decl.body match {
          case SurfaceExpr.TacticBlockExpr(tactics, tacticSpan) =>
            val initState = ProofState.initial(localCtx, returnTypeCore, label = decl.name)
            Tactics.runScript(currentEnv, initState, tactics) match {
              case Left(err) => break(Left(err))
              case Right((nextEnv, finalState)) =>
                currentEnv = nextEnv
                if (!finalState.isSolved) {
                  val goalsText = finalState.openGoals.map(_.formatHuman(currentEnv.kernelEnv)).mkString("\n")
                  break(
                    Left(
                      Diagnostic(
                        Diagnostic.Severity.Error,
                        "E020",
                        s"Incomplete proof for '${decl.name}': ${finalState.openGoals.length} unsolved goal(s)\n$goalsText",
                        tacticSpan
                      )
                    )
                  )
                }
                finalState.buildProofTerm match {
                  case Left(msg) =>
                    break(Left(Diagnostic(Diagnostic.Severity.Error, "E021", msg, tacticSpan)))
                  case Right(proofBody) =>
                    Term.lams(binders, proofBody)
                }
            }

          case bodyExpr if !isRecursive =>
            val (elabBody, envAfterBody) = checkExpr(currentEnv, metaCtx, localCtx, bodyExpr, returnTypeCore) match {
              case Left(err)  => break(Left(err))
              case Right(res) => res
            }
            currentEnv = envAfterBody
            val zonkedBody = metaCtx.zonk(elabBody, localCtx.depth)
            checkAllMetasSolved(metaCtx, decl.span) match {
              case Left(err) => break(Left(err))
              case Right(()) => ()
            }
            Term.lams(binders, zonkedBody)

          case bodyExpr =>
            // Recursive definition: bind self at outermost level inside Fix!
            val envWithSelfMeta = currentEnv.copy(
              implicitParamCounts = currentEnv.implicitParamCounts + (decl.name -> decl.typeParams.length),
              localRecursiveNames = currentEnv.localRecursiveNames + decl.name
            )
            val shiftedBinders = binders.zipWithIndex.map { case (b, i) =>
              Binder(b.name, Term.shift(b.ty, 1, i))
            }
            val shiftedReturn = Term.shift(returnTypeCore, 1, binders.length)
            var recCtx = LocalCtx.empty.push(decl.name, fullTypeRaw)
            for (b <- shiftedBinders) recCtx = recCtx.push(b.name, b.ty)

            val (elabBody, envAfterBody) = checkExpr(envWithSelfMeta, metaCtx, recCtx, bodyExpr, shiftedReturn) match {
              case Left(err)  => break(Left(err))
              case Right(res) => res
            }
            currentEnv = envAfterBody.copy(localRecursiveNames = currentEnv.localRecursiveNames)
            val zonkedBody = metaCtx.zonk(elabBody, recCtx.depth)
            checkAllMetasSolved(metaCtx, decl.span) match {
              case Left(err) => break(Left(err))
              case Right(()) => ()
            }
            val lambdaUnderFix = Term.lams(shiftedBinders, zonkedBody)
            val fullTypeZonked = metaCtx.zonk(fullTypeRaw, 0)

            // Select decreasing parameter index (explicit @decreasing or automatic detection!)
            val chosenRecIdx = chooseDecreasingArgIndex(currentEnv.kernelEnv, decl, binders, fullTypeZonked, lambdaUnderFix) match {
              case Left(err)  => break(Left(err))
              case Right(idx) => idx
            }
            Term.Fix(decl.name, chosenRecIdx, fullTypeZonked, lambdaUnderFix)
        }

      val fullTypeFinal = metaCtx.zonk(fullTypeRaw, 0)

      // 5. Verify completely from scratch with the Trusted Kernel!
      val isOpaque = decl.annotations.exists(_.name == "opaque") || decl.isTheorem || decl.isPartial
      TypeChecker.checkDef(
        currentEnv.kernelEnv,
        decl.name,
        fullTypeFinal,
        finalBodyTerm,
        transparent = !isOpaque,
        isTheorem = decl.isTheorem,
        isPartial = decl.isPartial
      ) match {
        case Left(kErr) =>
          Left(Diagnostic(Diagnostic.Severity.Error, kErr.code, kErr.message, decl.span))
        case Right(checkedKernelEnv) =>
          var updated = currentEnv.copy(
            kernelEnv = checkedKernelEnv,
            implicitParamCounts = currentEnv.implicitParamCounts + (decl.name -> decl.typeParams.length)
          )
          if (decl.annotations.exists(_.name == "simp")) {
            updated = updated.copy(simpLemmas = decl.name :: updated.simpLemmas)
          }
          if (decl.annotations.exists(_.name == "hint")) {
            updated = updated.copy(hintLemmas = decl.name :: updated.hintLemmas)
          }
          if (decl.annotations.exists(_.name == "wf")) {
            updated = updated.copy(wfHints = decl.name :: updated.wfHints)
          }
          if (decl.annotations.exists(_.name == "noextract")) {
            updated = updated.copy(noExtractNames = updated.noExtractNames + decl.name)
          }
          Right(updated)
      }
    }
  }

  // ===========================================================================
  // Mutual Recursion (`mutual { def ...; def ... }`)
  // ===========================================================================

  private def elaborateMutual(env: ElabEnv, decl: TopDecl.MutualDecl): Either[Diagnostic, ElabEnv] = boundary {
    val defs = decl.declarations
    if (defs.isEmpty) {
      break(Left(Diagnostic(Diagnostic.Severity.Error, "E017", "'mutual' block cannot be empty", decl.span)))
    }
    val anyPartial = defs.exists(_.isPartial)
    val allPartial = defs.forall(_.isPartial)
    if (anyPartial && !allPartial) {
      break(
        Left(
          Diagnostic(
            Diagnostic.Severity.Error,
            "E017",
            "Cannot mix total 'def' and 'partial def' inside the same 'mutual' block",
            decl.span
          )
        )
      )
    }
    if (defs.exists(_.terminationBy.isDefined)) {
      break(
        Left(
          Diagnostic(
            Diagnostic.Severity.Error,
            "E017",
            "'termination_by' is not supported inside 'mutual' blocks; use structural recursion or 'partial def'",
            decl.span
          )
        )
      )
    }

    // 1. Elaborate signatures for all declarations in the mutual block
    final case class SigInfo(
      decl: TopDecl.DefDecl,
      binders: List[Binder],
      returnTypeCore: Term,
      fullType: Term,
      localCtx: LocalCtx
    )
    val sigs = List.newBuilder[SigInfo]
    for (d <- defs) {
      val metaCtx = new MetaContext()
      var localCtx = LocalCtx.empty
      val allBinders = List.newBuilder[Binder]
      for (tp <- d.typeParams) {
        val paramType = tp.typeAnnotation match {
          case Some(ann) =>
            elaborateType(env, metaCtx, localCtx, ann) match {
              case Left(err) => break(Left(err))
              case Right(t)  => metaCtx.zonk(t, localCtx.depth)
            }
          case None => Term.USort(Sort.Type(0))
        }
        allBinders += Binder(tp.name, paramType)
        localCtx = localCtx.push(tp.name, paramType)
      }
      for (vp <- d.valueParams) {
        val paramType = vp.typeAnnotation match {
          case Some(ann) =>
            elaborateType(env, metaCtx, localCtx, ann) match {
              case Left(err) => break(Left(err))
              case Right(t)  => metaCtx.zonk(t, localCtx.depth)
            }
          case None =>
            break(Left(Diagnostic(Diagnostic.Severity.Error, "E010", s"Parameter '${vp.name}' in '${d.name}' requires a type annotation", vp.span)))
        }
        allBinders += Binder(vp.name, paramType)
        localCtx = localCtx.push(vp.name, paramType)
      }
      val returnTypeCore = d.returnType match {
        case Some(retExpr) =>
          elaborateType(env, metaCtx, localCtx, retExpr) match {
            case Left(err) => break(Left(err))
            case Right(t)  => metaCtx.zonk(t, localCtx.depth)
          }
        case None =>
          break(Left(Diagnostic(Diagnostic.Severity.Error, "E011", s"Mutually recursive function '${d.name}' requires an explicit return type", d.span)))
      }
      val bindersList = allBinders.result()
      val fullType = metaCtx.zonk(Term.pis(bindersList, returnTypeCore), 0)
      sigs += SigInfo(d, bindersList, returnTypeCore, fullType, localCtx)
    }
    val sigList = sigs.result()
    val implicitUpdates = sigList.map(s => s.decl.name -> s.decl.typeParams.length).toMap

    if (allPartial) {
      // Mutually recursive partial defs: register all as tentative opaque partial constants, check bodies, commit.
      var tentativeKernel = env.kernelEnv
      for (s <- sigList) {
        tentativeKernel = tentativeKernel.addDef(
          DefEntry(s.decl.name, s.fullType, Term.Const(s.decl.name), transparent = false, isTheorem = false, axiomsUsed = Set.empty, isPartial = true)
        )
      }
      val envForBodies = env.copy(
        kernelEnv = tentativeKernel,
        implicitParamCounts = env.implicitParamCounts ++ implicitUpdates
      )
      var collectedHoles = env.holes
      var collectedDirectives = env.directives
      val checkedEntries = List.newBuilder[(String, Term, Term)]
      for (s <- sigList) {
        val metaCtx = new MetaContext()
        val (elabBody, envAfter) = checkExpr(envForBodies, metaCtx, s.localCtx, s.decl.body, s.returnTypeCore) match {
          case Left(err)  => break(Left(err))
          case Right(res) => res
        }
        collectedHoles = envAfter.holes
        collectedDirectives = envAfter.directives
        val zonkedBody = metaCtx.zonk(elabBody, s.localCtx.depth)
        checkAllMetasSolved(metaCtx, s.decl.span) match {
          case Left(err) => break(Left(err))
          case Right(()) => ()
        }
        checkedEntries += ((s.decl.name, s.fullType, Term.lams(s.binders, zonkedBody)))
      }
      TypeChecker.checkMutualPartialDefs(env.kernelEnv, checkedEntries.result()) match {
        case Left(kErr) =>
          break(Left(Diagnostic(Diagnostic.Severity.Error, kErr.code, kErr.message, decl.span)))
        case Right(checkedKernel) =>
          var updated = env.copy(
            kernelEnv = checkedKernel,
            implicitParamCounts = env.implicitParamCounts ++ implicitUpdates,
            holes = collectedHoles,
            directives = collectedDirectives
          )
          for (s <- sigList) {
            if (s.decl.annotations.exists(_.name == "noextract")) {
              updated = updated.copy(noExtractNames = updated.noExtractNames + s.decl.name)
            }
          }
          break(Right(updated))
      }
    }

    // Total mutually recursive block -> Term.MutualFix
    val k = sigList.length
    val mutualNames = sigList.map(_.decl.name).toSet
    val envForBodies = env.copy(
      implicitParamCounts = env.implicitParamCounts ++ implicitUpdates,
      localRecursiveNames = env.localRecursiveNames ++ mutualNames
    )

    // Base mutual context has d_0, d_1, ..., d_{k-1} pushed (d_j's type shifted by +j)
    val baseMutualCtx = sigList.zipWithIndex.foldLeft(LocalCtx.empty) { case (ctxAcc, (s, j)) =>
      ctxAcc.push(s.decl.name, Term.shift(s.fullType, j))
    }

    var currentEnv = env
    val rawLambdas = List.newBuilder[Term]
    for (s <- sigList) {
      val metaCtx = new MetaContext()
      val shiftedBinders = s.binders.zipWithIndex.map { case (b, i) =>
        Binder(b.name, Term.shift(b.ty, k, i))
      }
      val shiftedReturn = Term.shift(s.returnTypeCore, k, s.binders.length)
      val recCtx = shiftedBinders.foldLeft(baseMutualCtx)((ctxAcc, b) => ctxAcc.push(b.name, b.ty))
      val (elabBody, envAfter) = checkExpr(envForBodies, metaCtx, recCtx, s.decl.body, shiftedReturn) match {
        case Left(err)  => break(Left(err))
        case Right(res) => res
      }
      currentEnv = currentEnv.copy(holes = envAfter.holes, directives = envAfter.directives)
      val zonkedBody = metaCtx.zonk(elabBody, recCtx.depth)
      checkAllMetasSolved(metaCtx, s.decl.span) match {
        case Left(err) => break(Left(err))
        case Right(()) => ()
      }
      rawLambdas += Term.lams(shiftedBinders, zonkedBody)
    }
    val lambdaList = rawLambdas.result()

    // Choose decreasing parameter index for each mutual function (explicit @decreasing or automatic search)
    val candidateLists: List[List[Int]] = sigList.map { s =>
      s.decl.annotations.find(_.name == "decreasing") match {
        case Some(ann) =>
          ann.args.headOption match {
            case Some(SurfaceExpr.IntLitExpr(i, _)) => List(i)
            case Some(SurfaceExpr.VarExpr(paramName, _)) =>
              val idx = s.binders.indexWhere(_.name == paramName)
              if (idx >= 0) List(idx) else Nil
            case _ => Nil
          }
        case None =>
          s.binders.zipWithIndex.collect {
            case (b, idx) if isInductiveHead(currentEnv.kernelEnv, b.ty) => idx
          }
      }
    }

    // Generate Cartesian product of candidate decreasing indices (usually tiny: 1-2 candidates per function)
    def cartesian(lists: List[List[Int]]): List[List[Int]] = lists match {
      case Nil          => List(Nil)
      case head :: tail => for (h <- head; t <- cartesian(tail)) yield h :: t
    }
    val tuples = cartesian(candidateLists)
    var chosenMutualDefs: Option[List[MutualFixDef]] = None
    var lastError = "No valid decreasing inductive parameter combination found"
    for (tuple <- tuples if chosenMutualDefs.isEmpty) {
      val defsCandidate = sigList.zip(lambdaList).zip(tuple).map { case ((s, lam), recIdx) =>
        MutualFixDef(s.decl.name, recIdx, s.fullType, lam)
      }
      Termination.checkMutualFix(currentEnv.kernelEnv, LocalCtx.empty, defsCandidate) match {
        case Right(()) => chosenMutualDefs = Some(defsCandidate)
        case Left(msg) => lastError = msg
      }
    }

    val verifiedDefs = chosenMutualDefs match {
      case Some(ds) => ds
      case None =>
        break(
          Left(
            Diagnostic(
              Diagnostic.Severity.Error,
              "K020",
              s"Could not prove mutual structural termination: $lastError",
              decl.span,
              hint = Some("Ensure every mutual recursive call passes a structurally smaller pattern-matched subterm of the same inductive type")
            )
          )
        )
    }

    // Register each function in the Trusted Kernel via TypeChecker.checkDef
    var updatedEnv = currentEnv
    for ((s, idx) <- sigList.zipWithIndex) {
      val isOpaque = s.decl.annotations.exists(_.name == "opaque")
      val mutualTerm = Term.MutualFix(verifiedDefs, idx)
      TypeChecker.checkDef(
        updatedEnv.kernelEnv,
        s.decl.name,
        s.fullType,
        mutualTerm,
        transparent = !isOpaque,
        isTheorem = false,
        isPartial = false
      ) match {
        case Left(kErr) =>
          break(Left(Diagnostic(Diagnostic.Severity.Error, kErr.code, kErr.message, s.decl.span)))
        case Right(nextKernel) =>
          updatedEnv = updatedEnv.copy(
            kernelEnv = nextKernel,
            implicitParamCounts = updatedEnv.implicitParamCounts + (s.decl.name -> s.decl.typeParams.length)
          )
          if (s.decl.annotations.exists(_.name == "simp")) {
            updatedEnv = updatedEnv.copy(simpLemmas = s.decl.name :: updatedEnv.simpLemmas)
          }
          if (s.decl.annotations.exists(_.name == "hint")) {
            updatedEnv = updatedEnv.copy(hintLemmas = s.decl.name :: updatedEnv.hintLemmas)
          }
          if (s.decl.annotations.exists(_.name == "wf")) {
            updatedEnv = updatedEnv.copy(wfHints = s.decl.name :: updatedEnv.wfHints)
          }
          if (s.decl.annotations.exists(_.name == "noextract")) {
            updatedEnv = updatedEnv.copy(noExtractNames = updatedEnv.noExtractNames + s.decl.name)
          }
      }
    }

    Right(updatedEnv)
  }

  // ===========================================================================
  // Well-Founded Recursion (`termination_by { measure }` -> 0-Axiom Acc[Nat, Lt])
  // ===========================================================================

  private def elaborateWellFoundedDef(env: ElabEnv, decl: TopDecl.DefDecl): Either[Diagnostic, ElabEnv] = boundary {
    // 1. Ensure WellFounded primitives (Acc, Lt, natWf, eqSubstLt, Eq, Nat) are in scope
    for (req <- List("Nat", "Eq", "Acc", "Lt", "natWf", "eqSubstLt")) {
      if (!env.kernelEnv.contains(req)) {
        break(
          Left(
            Diagnostic(
              Diagnostic.Severity.Error,
              "E018",
              s"'termination_by' requires '$req' to be in scope (add 'import WellFounded.*')",
              decl.span
            )
          )
        )
      }
    }

    val measureExpr = decl.terminationBy.get
    val metaCtx = new MetaContext()
    var localCtx = LocalCtx.empty
    val allBinders = List.newBuilder[Binder]

    for (tp <- decl.typeParams) {
      val paramType = tp.typeAnnotation match {
        case Some(ann) =>
          elaborateType(env, metaCtx, localCtx, ann) match {
            case Left(err) => break(Left(err))
            case Right(t)  => metaCtx.zonk(t, localCtx.depth)
          }
        case None => Term.USort(Sort.Type(0))
      }
      allBinders += Binder(tp.name, paramType)
      localCtx = localCtx.push(tp.name, paramType)
    }
    for (vp <- decl.valueParams) {
      val paramType = vp.typeAnnotation match {
        case Some(ann) =>
          elaborateType(env, metaCtx, localCtx, ann) match {
            case Left(err) => break(Left(err))
            case Right(t)  => metaCtx.zonk(t, localCtx.depth)
          }
        case None =>
          break(Left(Diagnostic(Diagnostic.Severity.Error, "E010", s"Parameter '${vp.name}' in '${decl.name}' requires a type annotation", vp.span)))
      }
      allBinders += Binder(vp.name, paramType)
      localCtx = localCtx.push(vp.name, paramType)
    }
    val binders = allBinders.result()
    val m = binders.length

    val returnTypeCore = decl.returnType match {
      case Some(retExpr) =>
        elaborateType(env, metaCtx, localCtx, retExpr) match {
          case Left(err) => break(Left(err))
          case Right(t)  => metaCtx.zonk(t, localCtx.depth)
        }
      case None =>
        break(Left(Diagnostic(Diagnostic.Severity.Error, "E011", s"Well-founded function '${decl.name}' requires an explicit return type", decl.span)))
    }

    // 2. Elaborate measure expression against Nat
    val (measureRaw, envAfterMeasure) = checkExpr(env, metaCtx, localCtx, measureExpr, Term.Ind("Nat")) match {
      case Left(err)  => break(Left(err))
      case Right(res) => res
    }
    val measureCore = metaCtx.zonk(measureRaw, m)
    checkAllMetasSolved(metaCtx, measureExpr.span) match {
      case Left(err) => break(Left(err))
      case Right(()) => ()
    }

    // 3. Build internal structurally-recursive helper `f_wf` on `acc: Acc[Nat, Lt](measureCore)`
    val wfHelperName = s"${decl.name}_wf"
    val accParamType = Term.apps(Term.Ind("Acc"), List(Term.Ind("Nat"), Term.Const("Lt"), measureCore))
    val wfBinders = binders :+ Binder("_wfAcc", accParamType)
    val wfReturnType = Term.shift(returnTypeCore, 1)
    val wfFullType = Term.pis(wfBinders, wfReturnType)

    // Inside Term.Fix(wfHelperName, recArgIdx = m, wfFullType, ...):
    //   level 0: wfHelperName
    //   levels 1..m: binders (shifted over level 0 -> shift(b.ty, 1, i))
    //   level m+1: _wfAcc : Acc[Nat, Lt](measureUnderFix)
    //   level m+2: _wfCurMeasure : Nat
    //   level m+3: _wfInv : (smaller: Nat) => Lt(smaller, _wfCurMeasure) => Acc[Nat, Lt](smaller)
    //   level m+4: _wfEqM : Eq(Nat, measureAtAcc, _wfCurMeasure)
    val shiftedWfBinders = wfBinders.zipWithIndex.map { case (b, i) =>
      Binder(b.name, Term.shift(b.ty, 1, i))
    }

    val measureAtAcc = Term.shift(measureCore, 1) // at depth m + 2 (under wfSelf, binders, _wfAcc)
    val retAtAcc = Term.shift(returnTypeCore, 1)

    // Build motive for Acc match at depth m + 2:
    //   (_wfM: Nat) => (_wfA: Acc(Nat, Lt, _wfM)) => Eq(Nat, shift(measureAtAcc, 2), _wfM) => shift(retAtAcc, 3)
    val accTypeAtM = Term.apps(Term.Ind("Acc"), List(Term.Ind("Nat"), Term.Const("Lt"), Term.Var(0)))
    val motiveEqTy = Term.apps(Term.Ind("Eq"), List(Term.Ind("Nat"), Term.shift(measureAtAcc, 2), Term.Var(1)))
    val motiveBody = Term.Pi("_wfEq", motiveEqTy, Term.shift(retAtAcc, 3))
    val accMotive = Term.Lam("_wfM", Term.Ind("Nat"), Term.Lam("_wfA", accTypeAtM, motiveBody))

    // Construct context inside Acc.Intro(_wfCurMeasure, _wfInv) and Lam(_wfEqM, ...) at depth m + 5
    var innerCtx = LocalCtx.empty.push(wfHelperName, wfFullType)
    for (b <- shiftedWfBinders) innerCtx = innerCtx.push(b.name, b.ty)
    innerCtx = innerCtx.push("_wfCurMeasure", Term.Ind("Nat"))
    val invFieldTy = Term.Pi(
      "smaller",
      Term.Ind("Nat"),
      Term.Pi(
        "relProof",
        Term.apps(Term.Const("Lt"), List(Term.Var(0), Term.Var(1))),
        Term.apps(Term.Ind("Acc"), List(Term.Ind("Nat"), Term.Const("Lt"), Term.Var(1)))
      )
    )
    innerCtx = innerCtx.push("_wfInv", invFieldTy)
    val eqMType = Term.apps(Term.Ind("Eq"), List(Term.Ind("Nat"), Term.shift(measureAtAcc, 2), Term.Var(1)))
    innerCtx = innerCtx.push("_wfEqM", eqMType)

    val expectedInnerRet = Term.shift(retAtAcc, 3)

    val wfCtx = WfContext(
      fnName = decl.name,
      wfHelperName = wfHelperName,
      numBinders = m,
      measureCore = measureCore,
      wfSelfLevel = 0,
      wfCurMeasureLevel = m + 2,
      wfInvLevel = m + 3,
      wfEqMLevel = m + 4,
      decreasingBy = decl.decreasingBy
    )
    val envForBody = envAfterMeasure.copy(
      implicitParamCounts = envAfterMeasure.implicitParamCounts + (decl.name -> decl.typeParams.length),
      wfContext = Some(wfCtx)
    )

    val bodyMetaCtx = new MetaContext()
    val (elabBody, envAfterBody) = checkExpr(envForBody, bodyMetaCtx, innerCtx, decl.body, expectedInnerRet) match {
      case Left(err)  => break(Left(err))
      case Right(res) => res
    }
    val zonkedBody = bodyMetaCtx.zonk(elabBody, innerCtx.depth)
    checkAllMetasSolved(bodyMetaCtx, decl.span) match {
      case Left(err) => break(Left(err))
      case Right(()) => ()
    }

    val introBranchBody = Term.Lam("_wfEqM", eqMType, zonkedBody)
    val accMatch = Term.Match(
      indName = "Acc",
      params = List(Term.Ind("Nat"), Term.Const("Lt")),
      motive = accMotive,
      scrutinee = Term.Var(0), // _wfAcc at depth m + 2
      branches = List(MatchBranch("Intro", List("_wfCurMeasure", "_wfInv"), introBranchBody))
    )
    val reflMeasure = Term.apps(Term.Ctor("Eq", "Refl"), List(Term.Ind("Nat"), measureAtAcc))
    val wfHelperCoreBody = Term.App(accMatch, reflMeasure)
    val wfLambdaUnderFix = Term.lams(shiftedWfBinders, wfHelperCoreBody)
    val wfFixTerm = Term.Fix(wfHelperName, m, wfFullType, wfLambdaUnderFix)

    // 4. Verify `f_wf` from scratch with the Trusted Kernel (checks Acc structural recursion!)
    val kernelAfterWf = TypeChecker.checkDef(
      envAfterBody.kernelEnv,
      wfHelperName,
      wfFullType,
      wfFixTerm,
      transparent = true,
      isTheorem = false,
      isPartial = false
    ) match {
      case Left(kErr) =>
        break(Left(Diagnostic(Diagnostic.Severity.Error, kErr.code, kErr.message, decl.span)))
      case Right(k) => k
    }

    // 5. Define clean user-facing wrapper `f(p_0, ..., p_{m-1}) = f_wf(p_0, ..., p_{m-1}, natWf(measureCore))`
    val fullTypeFinal = Term.pis(binders, returnTypeCore)
    val paramVars = (0 until m).toList.map(i => Term.Var(m - 1 - i))
    val wfCall = Term.apps(
      Term.Const(wfHelperName),
      paramVars :+ Term.App(Term.Const("natWf"), measureCore)
    )
    val wrapperBody = Term.lams(binders, wfCall)
    val isOpaque = decl.annotations.exists(_.name == "opaque")

    TypeChecker.checkDef(
      kernelAfterWf,
      decl.name,
      fullTypeFinal,
      wrapperBody,
      transparent = !isOpaque,
      isTheorem = false,
      isPartial = false
    ) match {
      case Left(kErr) =>
        Left(Diagnostic(Diagnostic.Severity.Error, kErr.code, kErr.message, decl.span))
      case Right(finalKernel) =>
        var updated = envAfterBody.copy(
          kernelEnv = finalKernel,
          implicitParamCounts = envAfterBody.implicitParamCounts + (decl.name -> decl.typeParams.length),
          wfContext = None
        )
        if (decl.annotations.exists(_.name == "simp")) {
          updated = updated.copy(simpLemmas = decl.name :: updated.simpLemmas)
        }
        if (decl.annotations.exists(_.name == "hint")) {
          updated = updated.copy(hintLemmas = decl.name :: updated.hintLemmas)
        }
        if (decl.annotations.exists(_.name == "wf")) {
          updated = updated.copy(wfHints = decl.name :: updated.wfHints)
        }
        if (decl.annotations.exists(_.name == "noextract")) {
          updated = updated.copy(noExtractNames = updated.noExtractNames + decl.name)
        }
        Right(updated)
    }
  }

  /**
   * Automatically discharges a well-founded decrease proof obligation `Lt(nextMeasure, curMeasure)`
   * using either user-supplied `decreasing_by` tactics or bounded tactic search with `@wf` lemmas.
   * Every synthesized proof term is re-verified by the Trusted Kernel.
   */
  private def proveWellFoundedDecrease(
    env: ElabEnv,
    localCtx: LocalCtx,
    goalType: Term,
    decreasingBy: Option[List[TacticStmt]],
    callSpan: Span
  ): Either[Diagnostic, Term] = boundary {
    val cleanEnv = env.copy(wfContext = None)
    val initState = ProofState.initial(localCtx, goalType, label = "termination_by")

    // 1. If user provided explicit `decreasing_by { ... }`, run it directly!
    decreasingBy.foreach { userTactics =>
      Tactics.runScript(cleanEnv, initState, userTactics) match {
        case Left(err) => break(Left(err))
        case Right((_, finalState)) =>
          if (!finalState.isSolved) {
            val rem = finalState.openGoals.map(_.formatHuman(cleanEnv.kernelEnv)).mkString("\n")
            break(
              Left(
                Diagnostic(
                  Diagnostic.Severity.Error,
                  "K020",
                  s"Well-founded termination proof incomplete in 'decreasing_by':\n$rem",
                  callSpan
                )
              )
            )
          }
          finalState.buildProofTerm match {
            case Left(msg) => break(Left(Diagnostic(Diagnostic.Severity.Error, "K020", msg, callSpan)))
            case Right(pt) => break(Right(pt))
          }
      }
    }

    // 2. Apply each matching branch equality (`_wf_eq_*`) individually without aborting on non-matching ones
    val eqHypNames = localCtx.entries.map(_.name).filter(_.startsWith("_wf_eq_"))
    val rewrittenState: ProofState = eqHypNames.foldLeft(initState) { (st, hypName) =>
      Tactics.step(cleanEnv, st, TacticStmt.Rewrite(List(SurfaceExpr.VarExpr(hypName, callSpan)), reverse = false, target = None, callSpan)) match {
        case Right((_, nextSt)) => nextSt
        case Left(_)            => st
      }
    }

    // Build a state where the two Nat arguments inside `Lt(lhs, rhs)` are normalized while keeping `Lt` folded!
    def normalizeInsideLt(st: ProofState): ProofState = {
      if (st.openGoals.isEmpty) st
      else {
        val g = st.openGoals.head
        val (hd, args) = Term.splitApps(g.targetType)
        hd match {
          case Term.Const("Lt") if args.length == 2 =>
            val lhsNorm = NbE.normalize(cleanEnv.kernelEnv, g.localCtx, args(0))
            val rhsNorm = NbE.normalize(cleanEnv.kernelEnv, g.localCtx, args(1))
            val foldedTarget = Term.apps(Term.Const("Lt"), List(lhsNorm, rhsNorm))
            // Definitionally equal to g.targetType, so identity proof term is kernel-valid!
            val newGoal = g.copy(targetType = foldedTarget)
            st.replaceHead(List(newGoal), children => children(newGoal.goalId), st.nextGoalId)
          case _ => st
        }
      }
    }

    val simpStep = TacticStmt.Simp(Nil, includeLocalHyps = true, target = None, callSpan)
    val decideStep = TacticStmt.Decide(callSpan)
    val omegaStep = TacticStmt.Omega(callSpan)
    val autoStep = TacticStmt.Auto(Some(6), callSpan)

    val normLtRewritten = normalizeInsideLt(rewrittenState)
    val normLtInit = normalizeInsideLt(initState)

    // Helper to close all open subgoals with simp / assumption / decide / omega / auto / @wf lemmas
    def solveState(state: ProofState, depth: Int): Option[ProofState] = boundary {
      if (state.isSolved) break(Some(state))
      if (depth <= 0) break(None)

      // Try simple closing tactics on head goal
      val quickTactics: List[TacticStmt] = List(
        TacticStmt.Assumption(callSpan),
        TacticStmt.Refl(callSpan),
        decideStep,
        omegaStep,
        autoStep
      )
      for (qt <- quickTactics) {
        Tactics.step(cleanEnv, state, qt) match {
          case Right((_, next)) if next.openGoals.length < state.openGoals.length =>
            solveState(next, depth - 1).foreach(s => break(Some(s)))
          case _ => ()
        }
      }

      // Try @wf lemmas (e.g. ltOfLeSucc, lengthFilterLe, subLtSelf, modLtDivisor, halfLtSelf, ltSelfSucc)
      val wfCandidates = (cleanEnv.wfHints ++ List("ltSelfSucc", "ltOfLeSucc", "leSuccMono", "subLtSelf", "modLtDivisor", "halfLtSelf", "lengthFilterLe"))
        .distinct
        .filter(cleanEnv.kernelEnv.defs.contains)
      for (lemName <- wfCandidates) {
        Tactics.step(cleanEnv, state, TacticStmt.Apply(SurfaceExpr.VarExpr(lemName, callSpan), callSpan)) match {
          case Right((_, next)) =>
            solveState(next, depth - 1).foreach(s => break(Some(s)))
          case _ => ()
        }
      }
      None
    }

    // Try folded states FIRST (so `Lt` stays intact for `@wf` lemma unification), then simplified fallback
    val prepStates: List[ProofState] = List(
      Some(initState),
      Some(rewrittenState),
      Some(normLtRewritten),
      Some(normLtInit),
      Tactics.step(cleanEnv, rewrittenState, simpStep).toOption.map(_._2),
      Tactics.step(cleanEnv, initState, simpStep).toOption.map(_._2)
    ).flatten

    for (st <- prepStates) {
      solveState(st, depth = 4).flatMap(_.buildProofTerm.toOption).foreach { pt =>
        if (TypeChecker.check(cleanEnv.kernelEnv, localCtx, pt, goalType).isRight) {
          break(Right(pt))
        }
      }
    }

    val normGoal = NbE.normalize(cleanEnv.kernelEnv, localCtx, goalType)
    Left(
      Diagnostic(
        Diagnostic.Severity.Error,
        "K020",
        s"Could not automatically prove well-founded measure decrease:\n  ⊢ ${Pretty.show(normGoal, localCtx.names)}",
        callSpan,
        hint = Some("Add a 'decreasing_by { ... }' tactic block or annotate a helper lemma with '@wf'")
      )
    )
  }

  private def zonkLocalCtx(metaCtx: MetaContext, localCtx: LocalCtx): LocalCtx = {
    val entriesOuterFirst = localCtx.entries.reverse
    var acc = LocalCtx.empty
    for (entry <- entriesOuterFirst) {
      val d = acc.depth
      acc = acc.push(entry.name, metaCtx.zonk(entry.ty, d), entry.value.map(metaCtx.zonk(_, d)))
    }
    acc
  }

  private def chooseDecreasingArgIndex(
    kernelEnv: KernelEnv,
    decl: TopDecl.DefDecl,
    binders: List[Binder],
    fullType: Term,
    lambdaUnderFix: Term
  ): Either[Diagnostic, Int] = {
    // Check explicit @decreasing annotation first
    decl.annotations.find(_.name == "decreasing") match {
      case Some(ann) =>
        val idxOpt = ann.args.headOption match {
          case Some(SurfaceExpr.IntLitExpr(i, _)) => Some(i)
          case Some(SurfaceExpr.VarExpr(paramName, _)) =>
            val found = binders.indexWhere(_.name == paramName)
            if (found >= 0) Some(found) else None
          case _ => None
        }
        idxOpt match {
          case Some(idx) =>
            Termination.checkFix(kernelEnv, LocalCtx.empty, decl.name, idx, fullType, lambdaUnderFix) match {
              case Right(()) => Right(idx)
              case Left(msg) => Left(Diagnostic(Diagnostic.Severity.Error, "K020", msg, decl.span))
            }
          case None =>
            Left(Diagnostic(Diagnostic.Severity.Error, "E012", s"Invalid @decreasing annotation on '${decl.name}'", ann.span))
        }

      case None =>
        // Automatically try each parameter whose type is an inductive type!
        val candidateIndices = binders.zipWithIndex.collect {
          case (b, idx) if isInductiveHead(kernelEnv, b.ty) => idx
        }
        if (candidateIndices.isEmpty) {
          return Left(
            Diagnostic(
              Diagnostic.Severity.Error,
              "K020",
              s"Termination error in '${decl.name}': recursive function has no inductive parameter to decrease on",
              decl.span
            )
          )
        }
        var lastError = ""
        boundary {
          for (idx <- candidateIndices) {
            Termination.checkFix(kernelEnv, LocalCtx.empty, decl.name, idx, fullType, lambdaUnderFix) match {
              case Right(()) => break(Right(idx))
              case Left(msg) => lastError = msg
            }
          }
          Left(
            Diagnostic(
              Diagnostic.Severity.Error,
              "K020",
              s"Could not prove termination of '${decl.name}' on any inductive parameter. Last check: $lastError",
              decl.span,
              hint = Some("Ensure recursive calls pass a structurally smaller pattern-matched subterm")
            )
          )
        }
    }
  }

  private def isInductiveHead(kernelEnv: KernelEnv, term: Term): Boolean = {
    val (head, _) = Term.splitApps(term)
    head match {
      case Term.Ind(name) => kernelEnv.inductives.contains(name)
      case _              => false
    }
  }

  private def elaborateVal(env: ElabEnv, decl: TopDecl.ValDecl): Either[Diagnostic, ElabEnv] = {
    val metaCtx = new MetaContext()
    decl.typeAnnotation match {
      case Some(typeExpr) =>
        for {
          valTypeRaw <- elaborateType(env, metaCtx, LocalCtx.empty, typeExpr)
          valType = metaCtx.zonk(valTypeRaw, 0)
          res <- checkExpr(env, metaCtx, LocalCtx.empty, decl.value, valType)
          (bodyRaw, envAfter) = res
          body = metaCtx.zonk(bodyRaw, 0)
          _ <- checkAllMetasSolved(metaCtx, decl.span)
          checkedKernel <- TypeChecker
            .checkDef(envAfter.kernelEnv, decl.name, valType, body, transparent = true, isTheorem = false)
            .left
            .map(e => Diagnostic(Diagnostic.Severity.Error, e.code, e.message, decl.span))
        } yield envAfter.copy(kernelEnv = checkedKernel)

      case None =>
        for {
          res <- inferExpr(env, metaCtx, LocalCtx.empty, decl.value)
          (bodyRaw, inferredTyRaw, envAfter) = res
          body = metaCtx.zonk(bodyRaw, 0)
          valType = metaCtx.zonk(inferredTyRaw, 0)
          _ <- checkAllMetasSolved(metaCtx, decl.span)
          checkedKernel <- TypeChecker
            .checkDef(envAfter.kernelEnv, decl.name, valType, body, transparent = true, isTheorem = false)
            .left
            .map(e => Diagnostic(Diagnostic.Severity.Error, e.code, e.message, decl.span))
        } yield envAfter.copy(kernelEnv = checkedKernel)
    }
  }

  private def elaborateAxiom(env: ElabEnv, decl: TopDecl.AxiomDecl): Either[Diagnostic, ElabEnv] = {
    boundary {
      val metaCtx = new MetaContext()
      var localCtx = LocalCtx.empty
      val binders = List.newBuilder[Binder]
      for (tp <- decl.typeParams) {
        val paramType = tp.typeAnnotation match {
          case Some(ann) =>
            elaborateType(env, metaCtx, localCtx, ann) match {
              case Left(err) => break(Left(err))
              case Right(t)  => metaCtx.zonk(t, localCtx.depth)
            }
          case None => Term.USort(Sort.Type(0))
        }
        binders += Binder(tp.name, paramType)
        localCtx = localCtx.push(tp.name, paramType)
      }
      for (vp <- decl.valueParams) {
        val paramType = vp.typeAnnotation match {
          case Some(ann) =>
            elaborateType(env, metaCtx, localCtx, ann) match {
              case Left(err) => break(Left(err))
              case Right(t)  => metaCtx.zonk(t, localCtx.depth)
            }
          case None =>
            break(Left(Diagnostic(Diagnostic.Severity.Error, "E010", s"Axiom parameter '${vp.name}' requires a type annotation", vp.span)))
        }
        binders += Binder(vp.name, paramType)
        localCtx = localCtx.push(vp.name, paramType)
      }
      val retType = elaborateType(env, metaCtx, localCtx, decl.returnType) match {
        case Left(err) => break(Left(err))
        case Right(t)  => metaCtx.zonk(t, localCtx.depth)
      }
      val fullType = Term.pis(binders.result(), retType)
      TypeChecker.checkAxiom(env.kernelEnv, decl.name, fullType) match {
        case Left(kErr) => Left(Diagnostic(Diagnostic.Severity.Error, kErr.code, kErr.message, decl.span))
        case Right(checkedKernel) =>
          Right(
            env.copy(
              kernelEnv = checkedKernel,
              implicitParamCounts = env.implicitParamCounts + (decl.name -> decl.typeParams.length)
            )
          )
      }
    }
  }

  private def elaborateDirective(
    env: ElabEnv,
    dirName: String,
    target: SurfaceExpr,
    span: Span
  ): Either[Diagnostic, ElabEnv] = dirName match {
    case "check" =>
      val metaCtx = new MetaContext()
      inferExpr(env, metaCtx, LocalCtx.empty, target).map { case (term, termType, nextEnv) =>
        val zTerm = metaCtx.zonk(term, 0)
        val zType = NbE.normalize(nextEnv.kernelEnv, LocalCtx.empty, metaCtx.zonk(termType, 0))
        val msg = s"${Pretty.show(zTerm)} : ${Pretty.show(zType)}"
        nextEnv.copy(directives = nextEnv.directives :+ DirectiveResult("check", msg, span))
      }

    case "eval" =>
      val metaCtx = new MetaContext()
      inferExpr(env, metaCtx, LocalCtx.empty, target).flatMap { case (term, _, nextEnv) =>
        val zTerm = metaCtx.zonk(term, 0)
        NbE.normalizeAllowPartial(nextEnv.kernelEnv, LocalCtx.empty, zTerm) match {
          case Right(normalized) =>
            Right(nextEnv.copy(directives = nextEnv.directives :+ DirectiveResult("eval", Pretty.show(normalized), span)))
          case Left(errMsg) =>
            Left(Diagnostic(Diagnostic.Severity.Error, "E033", errMsg, span))
        }
      }

    case "print" =>
      target match {
        case SurfaceExpr.VarExpr(name, _) =>
          val output = env.kernelEnv.defs.get(name) match {
            case Some(defEntry) =>
              val kind =
                if (defEntry.isTheorem) "theorem"
                else if (defEntry.isPartial) "partial def"
                else "def"
              s"$kind $name : ${Pretty.show(defEntry.ty)} = ${Pretty.show(defEntry.body)}"
            case None =>
              env.kernelEnv.inductives.get(name) match {
                case Some(ind) =>
                  s"enum ${ind.name} : ${Pretty.show(ind.fullType)} { ${ind.constructors.map(_.name).mkString(", ")} }"
                case None =>
                  env.kernelEnv.axioms.get(name) match {
                    case Some(ax) => s"axiom ${ax.name} : ${Pretty.show(ax.ty)}"
                    case None     => s"Unknown symbol '$name'"
                  }
              }
          }
          Right(env.copy(directives = env.directives :+ DirectiveResult("print", output, span)))
        case _ =>
          Left(Diagnostic(Diagnostic.Severity.Error, "E030", "#print expects an identifier", span))
      }

    case "axioms" =>
      target match {
        case SurfaceExpr.VarExpr(name, _) =>
          val output = env.kernelEnv.defs.get(name) match {
            case Some(defEntry) =>
              if (defEntry.axiomsUsed.isEmpty) s"'$name' is 100% axiom-free and kernel-verified!"
              else s"'$name' depends on axiom(s): ${defEntry.axiomsUsed.mkString(", ")}"
            case None => s"Unknown definition '$name'"
          }
          Right(env.copy(directives = env.directives :+ DirectiveResult("axioms", output, span)))
        case _ =>
          Left(Diagnostic(Diagnostic.Severity.Error, "E031", "#axioms expects an identifier", span))
      }

    case other =>
      Left(Diagnostic(Diagnostic.Severity.Error, "E032", s"Unknown directive '#$other'", span))
  }

  // ===========================================================================
  // Expression Elaboration (Bidirectional: Type, Check, Infer)
  // ===========================================================================

  def elaborateType(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    expr: SurfaceExpr
  ): Either[Diagnostic, Term] = expr match {
    case SurfaceExpr.ArrowExpr(params, body, _, _) =>
      elaboratePiChain(env, metaCtx, localCtx, params, body)

    case SurfaceExpr.ExistsExpr(params, body, span) =>
      elaborateExists(env, metaCtx, localCtx, params, body, span)

    case SurfaceExpr.BinaryOpExpr("/\\", left, right, span) =>
      for {
        l <- elaborateType(env, metaCtx, localCtx, left)
        r <- elaborateType(env, metaCtx, localCtx, right)
        _ <- requireSymbol(env, "And", span)
      } yield Term.apps(Term.Ind("And"), List(l, r))

    case SurfaceExpr.BinaryOpExpr("\\/", left, right, span) =>
      for {
        l <- elaborateType(env, metaCtx, localCtx, left)
        r <- elaborateType(env, metaCtx, localCtx, right)
        _ <- requireSymbol(env, "Or", span)
      } yield Term.apps(Term.Ind("Or"), List(l, r))

    case SurfaceExpr.UnaryOpExpr("~", operand, span) =>
      for {
        p <- elaborateType(env, metaCtx, localCtx, operand)
        _ <- requireSymbol(env, "Not", span)
      } yield Term.App(Term.Const("Not"), p)

    case SurfaceExpr.BinaryOpExpr("===", left, right, span) =>
      elaborateEq(env, metaCtx, localCtx, left, right, span).map(_._1)

    case SurfaceExpr.BinaryOpExpr("!==", left, right, span) =>
      for {
        eqRes <- elaborateEq(env, metaCtx, localCtx, left, right, span)
        _ <- requireSymbol(env, "Not", span)
      } yield Term.App(Term.Const("Not"), eqRes._1)

    case other =>
      inferExpr(env, metaCtx, localCtx, other).flatMap { case (term, inferredTy, _) =>
        val normTy = evalToValue(env.kernelEnv, localCtx, metaCtx.zonk(inferredTy, localCtx.depth))
        normTy match {
          case Value.VSort(_) => Right(term)
          case Value.VNeutral(NeutralHead.NConst(m), Nil) if MetaContext.isMeta(m) => Right(term)
          case _ =>
            Left(
              Diagnostic(
                Diagnostic.Severity.Error,
                "E040",
                s"Expected a type expression, found term of type '${Pretty.show(metaCtx.zonk(inferredTy, localCtx.depth), localCtx.names)}'",
                other.span
              )
            )
        }
      }
  }

  private def elaboratePiChain(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    params: List[ParamBinder],
    body: SurfaceExpr
  ): Either[Diagnostic, Term] = params match {
    case Nil => elaborateType(env, metaCtx, localCtx, body)
    case head :: tail =>
      val domainEither: Either[Diagnostic, Term] = head.typeAnnotation match {
        case Some(ann) => elaborateType(env, metaCtx, localCtx, ann)
        case None      => Right(Term.USort(Sort.Type(0)))
      }
      for {
        dom <- domainEither
        cod <- elaboratePiChain(env, metaCtx, localCtx.push(head.name, dom), tail, body)
      } yield Term.Pi(head.name, dom, cod)
  }

  private def elaborateExists(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    params: List[ParamBinder],
    body: SurfaceExpr,
    span: Span
  ): Either[Diagnostic, Term] = params match {
    case Nil => elaborateType(env, metaCtx, localCtx, body)
    case head :: tail =>
      for {
        _ <- requireSymbol(env, "Exists", span)
        dom <- head.typeAnnotation match {
          case Some(ann) => elaborateType(env, metaCtx, localCtx, ann)
          case None =>
            Left(Diagnostic(Diagnostic.Severity.Error, "E041", s"Exists binder '${head.name}' requires a type annotation", head.span))
        }
        predBody <- elaborateExists(env, metaCtx, localCtx.push(head.name, dom), tail, body, span)
      } yield Term.apps(Term.Ind("Exists"), List(dom, Term.Lam(head.name, dom, predBody)))
  }

  private def elaborateEq(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    left: SurfaceExpr,
    right: SurfaceExpr,
    span: Span
  ): Either[Diagnostic, (Term, ElabEnv)] = {
    for {
      _ <- requireSymbol(env, "Eq", span)
      lRes <- inferExpr(env, metaCtx, localCtx, left)
      (lTerm, lType, env1) = lRes
      rRes <- checkExpr(env1, metaCtx, localCtx, right, lType)
      (rTerm, env2) = rRes
    } yield (Term.apps(Term.Ind("Eq"), List(metaCtx.zonk(lType, localCtx.depth), lTerm, rTerm)), env2)
  }

  def checkExpr(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    expr: SurfaceExpr,
    expectedType: Term
  ): Either[Diagnostic, (Term, ElabEnv)] = {
    val zonkedExpected = metaCtx.zonk(expectedType, localCtx.depth)
    val expectedVal = evalToValue(env.kernelEnv, localCtx, zonkedExpected)

    expr match {
      case SurfaceExpr.HoleExpr(nameOpt, span) =>
        val holeInfo = HoleInfo(nameOpt, span, localCtx, zonkedExpected)
        if (env.holeCollectionMode) {
          val (envWithSorry, _) = env.ensureSorryAxiom
          val isProp = TypeChecker.inferSort(envWithSorry.kernelEnv, localCtx, zonkedExpected).contains(Sort.Prop)
          val sorryConst = if (isProp) "$sorryProp" else "$sorry"
          Right((Term.App(Term.Const(sorryConst), zonkedExpected), envWithSorry.copy(holes = envWithSorry.holes :+ holeInfo)))
        } else {
          val meta = metaCtx.freshMeta(localCtx.depth, zonkedExpected, nameOpt)
          Right((meta, env.copy(holes = env.holes :+ holeInfo)))
        }

      case SurfaceExpr.SorryExpr(_) =>
        val (envWithSorry, _) = env.ensureSorryAxiom
        val isProp = TypeChecker.inferSort(envWithSorry.kernelEnv, localCtx, zonkedExpected).contains(Sort.Prop)
        val sorryConst = if (isProp) "$sorryProp" else "$sorry"
        Right((Term.App(Term.Const(sorryConst), zonkedExpected), envWithSorry))

      case SurfaceExpr.TacticBlockExpr(tactics, tacticSpan) =>
        val initState = ProofState.initial(localCtx, zonkedExpected, label = "by")
        Tactics.runScript(env, initState, tactics).flatMap { case (nextEnv, finalState) =>
          if (!finalState.isSolved) {
            val goalsText = finalState.openGoals.map(_.formatHuman(nextEnv.kernelEnv)).mkString("\n")
            Left(Diagnostic(Diagnostic.Severity.Error, "E020", s"Incomplete tactic proof:\n$goalsText", tacticSpan))
          } else {
            finalState.buildProofTerm
              .left
              .map(msg => Diagnostic(Diagnostic.Severity.Error, "E021", msg, tacticSpan))
              .map(proof => (proof, nextEnv))
          }
        }

      case SurfaceExpr.BlockExpr(stmts, result, _) =>
        elaborateBlock(env, metaCtx, localCtx, stmts, result, Some(zonkedExpected)).map { case (t, _, nextEnv) =>
          (t, nextEnv)
        }

      case SurfaceExpr.VarExpr("refl", span) if isUnboundTermBuiltin(env, localCtx, "refl") =>
        expectedVal match {
          case Value.VInd("Eq", List(eqTyVal, lhsVal, rhsVal)) =>
            val fuel = new NbE.Fuel()
            val eqTyTerm = NbE.quote(env.kernelEnv, localCtx.depth, eqTyVal, fuel)
            val lhsTerm = NbE.quote(env.kernelEnv, localCtx.depth, lhsVal, fuel)
            val rhsTerm = NbE.quote(env.kernelEnv, localCtx.depth, rhsVal, fuel)
            metaCtx.unify(env.kernelEnv, localCtx, lhsTerm, rhsTerm) match {
              case Right(()) =>
                val zonkedTy = metaCtx.zonk(eqTyTerm, localCtx.depth)
                val zonkedLhs = metaCtx.zonk(lhsTerm, localCtx.depth)
                Right((Term.apps(Term.Ctor("Eq", "Refl"), List(zonkedTy, zonkedLhs)), env))
              case Left(_) =>
                val normLhs = NbE.normalize(env.kernelEnv, localCtx, metaCtx.zonk(lhsTerm, localCtx.depth))
                val normRhs = NbE.normalize(env.kernelEnv, localCtx, metaCtx.zonk(rhsTerm, localCtx.depth))
                Left(
                  Diagnostic(
                    Diagnostic.Severity.Error,
                    "E058",
                    s"'refl' failed: '${Pretty.show(normLhs, localCtx.names)}' is not definitionally equal to '${Pretty.show(normRhs, localCtx.names)}'",
                    span
                  )
                )
            }
          case _ =>
            Left(
              Diagnostic(
                Diagnostic.Severity.Error,
                "E058",
                s"'refl' expects an equality type ('a === b'), found '${Pretty.show(zonkedExpected, localCtx.names)}'",
                span
              )
            )
        }

      case SurfaceExpr.VarExpr("prove", span) if isUnboundTermBuiltin(env, localCtx, "prove") =>
        Tactics.tryAutoProve(env, localCtx, zonkedExpected, span)

      case SurfaceExpr.IfExpr(cond, thenBranch, elseBranch, span) =>
        val isPropTarget =
          env.kernelEnv.inductives.contains("Eq") &&
            env.kernelEnv.inductives.contains("Bool") &&
            TypeChecker.inferSort(env.kernelEnv, localCtx, zonkedExpected).contains(Sort.Prop)
        if (isPropTarget) {
          elaborateFlowSensitiveIf(env, metaCtx, localCtx, cond, thenBranch, elseBranch, zonkedExpected, span)
        } else {
          val desugared = SurfaceExpr.MatchExpr(
            cond,
            None,
            List(
              MatchCase(Pattern.BoolLit(true, span), thenBranch, thenBranch.span),
              MatchCase(Pattern.BoolLit(false, span), elseBranch, elseBranch.span)
            ),
            span
          )
          checkExpr(env, metaCtx, localCtx, desugared, zonkedExpected)
        }

      case matchExpr: SurfaceExpr.MatchExpr =>
        elaborateMatch(env, metaCtx, localCtx, matchExpr, Some(zonkedExpected)).map { case (t, _, nextEnv) =>
          (t, nextEnv)
        }

      case SurfaceExpr.ArrowExpr(params, body, alwaysPi, span) =>
        expectedVal match {
          case Value.VSort(_) =>
            elaboratePiChain(env, metaCtx, localCtx, params, body).map(t => (t, env))

          case Value.VPi(_, _, _) if !alwaysPi =>
            elaborateLamAgainstPi(env, metaCtx, localCtx, params, body, zonkedExpected, span)

          case _ =>
            // Fallback to infer + unify
            inferAndUnify(env, metaCtx, localCtx, expr, zonkedExpected)
        }

      case _ =>
        inferAndUnify(env, metaCtx, localCtx, expr, zonkedExpected)
    }
  }

  private def inferAndUnify(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    expr: SurfaceExpr,
    expectedType: Term
  ): Either[Diagnostic, (Term, ElabEnv)] = {
    inferExpr(env, metaCtx, localCtx, expr).flatMap { case (term, inferredType, nextEnv) =>
      metaCtx.unify(nextEnv.kernelEnv, localCtx, inferredType, expectedType, allowSubtyping = true) match {
        case Right(()) => Right((term, nextEnv))
        case Left(_) =>
          val normExp = NbE.normalize(nextEnv.kernelEnv, localCtx, metaCtx.zonk(expectedType, localCtx.depth))
          val normInf = NbE.normalize(nextEnv.kernelEnv, localCtx, metaCtx.zonk(inferredType, localCtx.depth))
          Left(
            Diagnostic(
              Diagnostic.Severity.Error,
              "E042",
              "Type mismatch",
              expr.span,
              expected = Some(Pretty.show(normExp, localCtx.names)),
              found = Some(Pretty.show(normInf, localCtx.names))
            )
          )
      }
    }
  }

  private def elaborateLamAgainstPi(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    params: List[ParamBinder],
    body: SurfaceExpr,
    expectedType: Term,
    span: Span
  ): Either[Diagnostic, (Term, ElabEnv)] = params match {
    case Nil => checkExpr(env, metaCtx, localCtx, body, expectedType)
    case head :: tail =>
      val fuel = new NbE.Fuel()
      val evalEnv = NbE.buildEvalEnv(env.kernelEnv, localCtx, fuel)
      NbE.evaluate(env.kernelEnv, evalEnv, metaCtx.zonk(expectedType, localCtx.depth), fuel) match {
        case Value.VPi(piName, piDomVal, piCodClosure) =>
          val piDomTerm = NbE.quote(env.kernelEnv, localCtx.depth, piDomVal, fuel)
          // Handle bare `x => body` parsed as `ParamBinder("_", Some(VarExpr("x")), isBareArrowLeft = true)`
          // without misinterpreting an explicit `(_: Nat) => body` wildcard annotation.
          val (binderName, explicitAnn) =
            if (head.isBareArrowLeft && head.name == "_") {
              head.typeAnnotation match {
                case Some(SurfaceExpr.VarExpr(varName, _)) => (varName, None)
                case other                                 => (piName, other)
              }
            } else (head.name, head.typeAnnotation)

          val domainChecked: Either[Diagnostic, Term] = explicitAnn match {
            case Some(ann) =>
              elaborateType(env, metaCtx, localCtx, ann).flatMap { annTerm =>
                metaCtx.unify(env.kernelEnv, localCtx, annTerm, piDomTerm) match {
                  case Right(()) => Right(annTerm)
                  case Left(err) => Left(Diagnostic(Diagnostic.Severity.Error, "E043", s"Lambda parameter type mismatch: $err", ann.span))
                }
              }
            case None => Right(piDomTerm)
          }

          for {
            domTerm <- domainChecked
            freshVar = Value.VNeutral(NeutralHead.NVar(localCtx.depth), Nil)
            codVal = NbE.applyClosure(env.kernelEnv, piCodClosure, freshVar, fuel)
            codTerm = NbE.quote(env.kernelEnv, localCtx.depth + 1, codVal, fuel)
            res <- elaborateLamAgainstPi(env, metaCtx, localCtx.push(binderName, domTerm), tail, body, codTerm, span)
            (bodyTerm, nextEnv) = res
          } yield (Term.Lam(binderName, domTerm, bodyTerm), nextEnv)

        case other =>
          val quoted = NbE.quote(env.kernelEnv, localCtx.depth, other, fuel)
          Left(
            Diagnostic(
              Diagnostic.Severity.Error,
              "E044",
              s"Lambda expression cannot have non-function type '${Pretty.show(quoted, localCtx.names)}'",
              span
            )
          )
      }
  }

  def inferExpr(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    expr: SurfaceExpr
  ): Either[Diagnostic, (Term, Term, ElabEnv)] = expr match {
    case SurfaceExpr.SortExpr(true, _, _) =>
      Right((Term.USort(Sort.Prop), Term.USort(Sort.Type(0)), env))

    case SurfaceExpr.SortExpr(false, level, _) =>
      Right((Term.USort(Sort.Type(level)), Term.USort(Sort.Type(level + 1)), env))

    case SurfaceExpr.IntLitExpr(value, span) =>
      if (!env.kernelEnv.inductives.contains("Nat")) {
        Left(Diagnostic(Diagnostic.Severity.Error, "E050", s"Integer literal '$value' requires 'Nat' to be in scope", span))
      } else {
        def buildNat(n: Int): Term =
          if (n <= 0) Term.Ctor("Nat", "Zero")
          else Term.App(Term.Ctor("Nat", "Succ"), buildNat(n - 1))
        Right((buildNat(value), Term.Ind("Nat"), env))
      }

    case SurfaceExpr.BoolLitExpr(value, span) =>
      if (!env.kernelEnv.inductives.contains("Bool")) {
        Left(Diagnostic(Diagnostic.Severity.Error, "E051", s"Boolean literal '$value' requires 'Bool' to be in scope", span))
      } else {
        val ctor = if (value) "True" else "False"
        Right((Term.Ctor("Bool", ctor), Term.Ind("Bool"), env))
      }

    case SurfaceExpr.ListLitExpr(elements, span) =>
      if (!env.kernelEnv.inductives.contains("List")) {
        Left(Diagnostic(Diagnostic.Severity.Error, "E056", "List literal '[...]' requires 'List' to be in scope (try 'import List.*')", span))
      } else {
        val desugared = elements.foldRight[SurfaceExpr](
          SurfaceExpr.SelectExpr(SurfaceExpr.VarExpr("List", span), "Nil", span)
        ) { (elem, tail) =>
          SurfaceExpr.BinaryOpExpr("::", elem, tail, elem.span.merge(tail.span))
        }
        inferExpr(env, metaCtx, localCtx, desugared)
      }

    case SurfaceExpr.CalcExpr(start, steps, span) =>
      elaborateCalc(env, metaCtx, localCtx, start, steps, span)

    case SurfaceExpr.HoleExpr(nameOpt, span) =>
      val tyMeta = metaCtx.freshMeta(localCtx.depth, Term.USort(Sort.Type(0)), Some("holeType"))
      val termMeta = metaCtx.freshMeta(localCtx.depth, tyMeta, nameOpt)
      val holeInfo = HoleInfo(nameOpt, span, localCtx, tyMeta)
      Right((termMeta, tyMeta, env.copy(holes = env.holes :+ holeInfo)))

    case SurfaceExpr.SorryExpr(_) =>
      val (envWithSorry, sorryConst) = env.ensureSorryAxiom
      val tyMeta = metaCtx.freshMeta(localCtx.depth, Term.USort(Sort.Type(0)), Some("sorryType"))
      Right((Term.App(Term.Const(sorryConst), tyMeta), tyMeta, envWithSorry))

    case SurfaceExpr.AscribeExpr(inner, expectedTyExpr, _) =>
      for {
        ty <- elaborateType(env, metaCtx, localCtx, expectedTyExpr)
        res <- checkExpr(env, metaCtx, localCtx, inner, ty)
      } yield (res._1, ty, res._2)

    case SurfaceExpr.VarExpr(name, span) =>
      resolveIdentifier(env, metaCtx, localCtx, name, insertImplicits = true, span)

    case SurfaceExpr.SelectExpr(receiver, member, span) =>
      elaborateSelect(env, metaCtx, localCtx, receiver, member, insertImplicits = true, span)

    case SurfaceExpr.TypeAppExpr(callee, typeArgs, span) =>
      elaborateTypeApp(env, metaCtx, localCtx, callee, typeArgs, span)

    case SurfaceExpr.CallExpr(SurfaceExpr.VarExpr("sym", _), List(eqExpr), span)
        if isUnboundTermBuiltin(env, localCtx, "sym") =>
      elaborateTermSym(env, metaCtx, localCtx, eqExpr, span)

    case SurfaceExpr.CallExpr(SurfaceExpr.VarExpr("trans", _), List(eq1Expr, eq2Expr), span)
        if isUnboundTermBuiltin(env, localCtx, "trans") =>
      elaborateTermTrans(env, metaCtx, localCtx, eq1Expr, eq2Expr, span)

    case SurfaceExpr.CallExpr(SurfaceExpr.VarExpr("cong", _), List(fnExpr, eqExpr), span)
        if isUnboundTermBuiltin(env, localCtx, "cong") =>
      elaborateTermCong(env, metaCtx, localCtx, fnExpr, eqExpr, span)

    case SurfaceExpr.CallExpr(callee, args, span) =>
      elaborateCall(env, metaCtx, localCtx, callee, args, span)

    case SurfaceExpr.UnaryOpExpr(op, operand, span) =>
      op match {
        case "!" => elaborateCall(env, metaCtx, localCtx, SurfaceExpr.VarExpr("notBool", span), List(operand), span)
        case "~" =>
          for {
            p <- elaborateType(env, metaCtx, localCtx, operand)
            _ <- requireSymbol(env, "Not", span)
          } yield (Term.App(Term.Const("Not"), p), Term.USort(Sort.Prop), env)
        case other =>
          Left(Diagnostic(Diagnostic.Severity.Error, "E052", s"Unknown unary operator '$other'", span))
      }

    case SurfaceExpr.BinaryOpExpr(op, left, right, span) =>
      op match {
        case "===" =>
          elaborateEq(env, metaCtx, localCtx, left, right, span).map { case (t, e) => (t, Term.USort(Sort.Prop), e) }
        case "!==" =>
          for {
            eqRes <- elaborateEq(env, metaCtx, localCtx, left, right, span)
            _ <- requireSymbol(eqRes._2, "Not", span)
          } yield (Term.App(Term.Const("Not"), eqRes._1), Term.USort(Sort.Prop), eqRes._2)
        case "/\\" =>
          for {
            l <- elaborateType(env, metaCtx, localCtx, left)
            r <- elaborateType(env, metaCtx, localCtx, right)
            _ <- requireSymbol(env, "And", span)
          } yield (Term.apps(Term.Ind("And"), List(l, r)), Term.USort(Sort.Prop), env)
        case "\\/" =>
          for {
            l <- elaborateType(env, metaCtx, localCtx, left)
            r <- elaborateType(env, metaCtx, localCtx, right)
            _ <- requireSymbol(env, "Or", span)
          } yield (Term.apps(Term.Ind("Or"), List(l, r)), Term.USort(Sort.Prop), env)
        case "+"  => elaborateCall(env, metaCtx, localCtx, SurfaceExpr.VarExpr("add", span), List(left, right), span)
        case "-"  => elaborateCall(env, metaCtx, localCtx, SurfaceExpr.VarExpr("sub", span), List(left, right), span)
        case "*"  => elaborateCall(env, metaCtx, localCtx, SurfaceExpr.VarExpr("mul", span), List(left, right), span)
        case "&&" => elaborateCall(env, metaCtx, localCtx, SurfaceExpr.VarExpr("andBool", span), List(left, right), span)
        case "||" => elaborateCall(env, metaCtx, localCtx, SurfaceExpr.VarExpr("orBool", span), List(left, right), span)
        case "==" => elaborateCall(env, metaCtx, localCtx, SurfaceExpr.VarExpr("beq", span), List(left, right), span)
        case "!=" =>
          val eqCall = SurfaceExpr.CallExpr(SurfaceExpr.VarExpr("beq", span), List(left, right), span)
          elaborateCall(env, metaCtx, localCtx, SurfaceExpr.VarExpr("notBool", span), List(eqCall), span)
        case "<=" => elaborateCall(env, metaCtx, localCtx, SurfaceExpr.VarExpr("ble", span), List(left, right), span)
        case "<"  => elaborateCall(env, metaCtx, localCtx, SurfaceExpr.VarExpr("blt", span), List(left, right), span)
        case ">=" => elaborateCall(env, metaCtx, localCtx, SurfaceExpr.VarExpr("ble", span), List(right, left), span)
        case ">"  => elaborateCall(env, metaCtx, localCtx, SurfaceExpr.VarExpr("blt", span), List(right, left), span)
        case "::" =>
          val consRef = SurfaceExpr.SelectExpr(SurfaceExpr.VarExpr("List", span), "Cons", span)
          elaborateCall(env, metaCtx, localCtx, consRef, List(left, right), span)
        case "++" => elaborateCall(env, metaCtx, localCtx, SurfaceExpr.VarExpr("append", span), List(left, right), span)
        case other =>
          Left(Diagnostic(Diagnostic.Severity.Error, "E053", s"Unknown binary operator '$other'", span))
      }

    case SurfaceExpr.ArrowExpr(params, body, alwaysPi, span) =>
      if (alwaysPi || params.forall(_.name == "_")) {
        elaboratePiChain(env, metaCtx, localCtx, params, body).flatMap { piTerm =>
          TypeChecker.infer(env.kernelEnv, localCtx, metaCtx.zonk(piTerm, localCtx.depth)) match {
            case Right(sortTerm) => Right((piTerm, sortTerm, env))
            case Left(_)         => Right((piTerm, Term.USort(Sort.Type(0)), env))
          }
        }
      } else {
        // Explicit typed lambda `(x: A) => body`
        elaborateTypedLam(env, metaCtx, localCtx, params, body, span)
      }

    case SurfaceExpr.ExistsExpr(params, body, span) =>
      elaborateExists(env, metaCtx, localCtx, params, body, span).map(t => (t, Term.USort(Sort.Prop), env))

    case SurfaceExpr.BlockExpr(stmts, result, _) =>
      elaborateBlock(env, metaCtx, localCtx, stmts, result, None)

    case SurfaceExpr.IfExpr(cond, thenBranch, elseBranch, span) =>
      val desugared = new SurfaceExpr.MatchExpr(
        cond,
        None,
        List(
          MatchCase(Pattern.BoolLit(true, span), thenBranch, thenBranch.span),
          MatchCase(Pattern.BoolLit(false, span), elseBranch, elseBranch.span)
        ),
        span
      )
      elaborateMatch(env, metaCtx, localCtx, desugared, None)

    case matchExpr: SurfaceExpr.MatchExpr =>
      elaborateMatch(env, metaCtx, localCtx, matchExpr, None)

    case SurfaceExpr.TacticBlockExpr(_, span) =>
      Left(Diagnostic(Diagnostic.Severity.Error, "E054", "Tactic block 'by { ... }' requires a known expected type (e.g. a theorem return type)", span))
  }

  private def elaborateTypedLam(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    params: List[ParamBinder],
    body: SurfaceExpr,
    span: Span
  ): Either[Diagnostic, (Term, Term, ElabEnv)] = params match {
    case Nil => inferExpr(env, metaCtx, localCtx, body)
    case head :: tail =>
      val domEither: Either[Diagnostic, Term] = head.typeAnnotation match {
        case Some(ann) => elaborateType(env, metaCtx, localCtx, ann)
        case None =>
          Left(Diagnostic(Diagnostic.Severity.Error, "E055", s"Cannot infer type of lambda parameter '${head.name}' without expected function type", head.span))
      }
      for {
        dom <- domEither
        res <- elaborateTypedLam(env, metaCtx, localCtx.push(head.name, dom), tail, body, span)
        (bodyTerm, bodyType, nextEnv) = res
      } yield (Term.Lam(head.name, dom, bodyTerm), Term.Pi(head.name, dom, bodyType), nextEnv)
  }

  private def elaborateBlock(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    stmts: List[BlockStatement],
    result: SurfaceExpr,
    expectedType: Option[Term]
  ): Either[Diagnostic, (Term, Term, ElabEnv)] = stmts match {
    case Nil =>
      expectedType match {
        case Some(exp) => checkExpr(env, metaCtx, localCtx, result, exp).map { case (t, e) => (t, exp, e) }
        case None      => inferExpr(env, metaCtx, localCtx, result)
      }

    case BlockStatement.LocalVal(name, typeAnn, valueExpr, _) :: rest =>
      val valRes: Either[Diagnostic, (Term, Term, ElabEnv)] = typeAnn match {
        case Some(ann) =>
          for {
            ty <- elaborateType(env, metaCtx, localCtx, ann)
            res <- checkExpr(env, metaCtx, localCtx, valueExpr, ty)
          } yield (res._1, ty, res._2)
        case None =>
          inferExpr(env, metaCtx, localCtx, valueExpr)
      }
      for {
        (valTerm, valType, env1) <- valRes
        zValType = metaCtx.zonk(valType, localCtx.depth)
        zValTerm = metaCtx.zonk(valTerm, localCtx.depth)
        nextCtx = localCtx.push(name, zValType, Some(zValTerm))
        shiftedExp = expectedType.map(Term.shift(_, 1))
        (bodyTerm, bodyType, env2) <- elaborateBlock(env1, metaCtx, nextCtx, rest, result, shiftedExp)
      } yield (
        Term.Let(name, zValType, zValTerm, bodyTerm),
        Term.subst(bodyType, 0, zValTerm),
        env2
      )

    case BlockStatement.ExprStmt(e) :: rest =>
      for {
        (valTerm, valType, env1) <- inferExpr(env, metaCtx, localCtx, e)
        nextCtx = localCtx.push("_", valType, Some(valTerm))
        shiftedExp = expectedType.map(Term.shift(_, 1))
        (bodyTerm, bodyType, env2) <- elaborateBlock(env1, metaCtx, nextCtx, rest, result, shiftedExp)
      } yield (
        Term.Let("_", valType, valTerm, bodyTerm),
        Term.subst(bodyType, 0, valTerm),
        env2
      )
  }

  // ===========================================================================
  // Name Resolution, Implicit Arguments, Calls & Dot Notation (UFCS / Records)
  // ===========================================================================

  private def resolveIdentifier(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    name: String,
    insertImplicits: Boolean,
    span: Span
  ): Either[Diagnostic, (Term, Term, ElabEnv)] = {
    // 1. Local variable (De Bruijn lookup)
    val localIdx = localCtx.entries.indexWhere(_.name == name)
    if (localIdx >= 0) {
      val varType = localCtx.lookupType(localIdx).get
      val baseTerm = Term.Var(localIdx)
      if (insertImplicits) {
        val impCount = env.implicitParamCounts.getOrElse(name, 0)
        val (applied, appliedTy) =
          if (impCount > 0 && env.localRecursiveNames.contains(name))
            insertImplicitMetas(env.kernelEnv, metaCtx, localCtx, baseTerm, varType, impCount)
          else (baseTerm, varType)
        return Right((applied, appliedTy, env))
      } else {
        return Right((baseTerm, varType, env))
      }
    }

    // 2. Top-level def / theorem / axiom
    env.kernelEnv.lookupConstType(name) match {
      case Some(constTy) =>
        val baseTerm = Term.Const(name)
        val (term, ty) =
          if (insertImplicits)
            insertImplicitMetas(env.kernelEnv, metaCtx, localCtx, baseTerm, constTy, env.implicitParamCounts.getOrElse(name, 0))
          else (baseTerm, constTy)
        return Right((term, ty, env))
      case None => ()
    }

    // 3. Inductive type name
    env.kernelEnv.inductives.get(name) match {
      case Some(ind) =>
        return Right((Term.Ind(name), ind.fullType, env))
      case None => ()
    }

    // 4. Unqualified constructor name (if unambiguous!)
    env.shortConstructors.get(name) match {
      case Some(List((indName, ctorName))) =>
        val ind = env.kernelEnv.inductives(indName)
        val ctor = ind.ctor(ctorName).get
        val baseTerm = Term.Ctor(indName, ctorName)
        val ctorTy = ind.ctorType(ctor)
        val (term, ty) =
          if (insertImplicits)
            insertImplicitMetas(env.kernelEnv, metaCtx, localCtx, baseTerm, ctorTy, ind.numParams)
          else (baseTerm, ctorTy)
        return Right((term, ty, env))
      case Some(multiple) if multiple.length > 1 =>
        val options = multiple.map { case (i, c) => s"$i.$c" }.mkString(", ")
        return Left(
          Diagnostic(
            Diagnostic.Severity.Error,
            "E060",
            s"Ambiguous constructor '$name'; qualify with inductive type name: $options",
            span
          )
        )
      case _ => ()
    }

    Left(Diagnostic(Diagnostic.Severity.Error, "E061", s"Undefined identifier '$name'", span))
  }

  private def elaborateSelect(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    receiver: SurfaceExpr,
    member: String,
    insertImplicits: Boolean,
    span: Span
  ): Either[Diagnostic, (Term, Term, ElabEnv)] = {
    // 1. Enum constructor access (`EnumName.CtorName`) OR qualified module member (`ModuleName.defName`)
    receiver match {
      case SurfaceExpr.VarExpr(qualName, _) if env.kernelEnv.inductives.contains(qualName) =>
        val ind = env.kernelEnv.inductives(qualName)
        ind.ctor(member) match {
          case Some(ctor) =>
            val baseTerm = Term.Ctor(qualName, member)
            val ctorTy = ind.ctorType(ctor)
            val (term, ty) =
              if (insertImplicits) insertImplicitMetas(env.kernelEnv, metaCtx, localCtx, baseTerm, ctorTy, ind.numParams)
              else (baseTerm, ctorTy)
            return Right((term, ty, env))
          case None if env.loadedModules.contains(qualName) && env.kernelEnv.contains(member) =>
            return resolveIdentifier(env, metaCtx, localCtx, member, insertImplicits, span)
          case None =>
            return Left(Diagnostic(Diagnostic.Severity.Error, "E062", s"Inductive '$qualName' has no constructor '$member'", span))
        }
      case SurfaceExpr.VarExpr(modName, _) if env.loadedModules.contains(modName) && env.kernelEnv.contains(member) =>
        return resolveIdentifier(env, metaCtx, localCtx, member, insertImplicits, span)
      case _ => ()
    }

    // 2. Record field projection (`pair.first`) OR UFCS 0-arg method call (`xs.length`, `xs.reverse`)!
    inferExpr(env, metaCtx, localCtx, receiver).flatMap { case (recvTerm, recvType, env1) =>
      val fuel = new NbE.Fuel()
      val evalEnv = NbE.buildEvalEnv(env1.kernelEnv, localCtx, fuel)
      val normRecvType = NbE.evaluate(env1.kernelEnv, evalEnv, metaCtx.zonk(recvType, localCtx.depth), fuel)

      // Check case class field projection first
      var projMatchOpt: Option[(Term, Term)] = None
      normRecvType match {
        case Value.VInd(indName, allArgs) if env1.recordFields.contains(indName) =>
          val fields = env1.recordFields(indName)
          val fieldIdx = fields.indexOf(member)
          if (fieldIdx >= 0) {
            val ind = env1.kernelEnv.inductives(indName)
            val ctor = ind.constructors.head
            val params = allArgs.take(ind.numParams).map(NbE.quote(env1.kernelEnv, localCtx.depth, _, fuel))
            val instFields = ind.instantiateFields(ctor, params)
            val fieldTy = instFields(fieldIdx).ty
            // Check non-dependent field type (or simple projection)
            val resultTy =
              if ((0 until fieldIdx).exists(i => Term.freeVarOccurs(fieldTy, i))) {
                // Substitute earlier fields via projections!
                val earlierProjs = (0 until fieldIdx).toList.map { prevIdx =>
                  val prevMotive = Term.Lam("_s", Term.apps(Term.Ind(indName), params), Term.shift(instFields(prevIdx).ty, 1))
                  Term.Match(
                    indName,
                    params,
                    prevMotive,
                    recvTerm,
                    List(MatchBranch(ctor.name, fields, Term.Var(fields.length - 1 - prevIdx)))
                  )
                }
                Term.substMany(fieldTy, earlierProjs)
              } else {
                Term.shift(fieldTy, -fieldIdx, fieldIdx)
              }
            val motive = Term.Lam("_s", Term.apps(Term.Ind(indName), params), Term.shift(resultTy, 1))
            val projMatch = Term.Match(
              indName,
              params,
              motive,
              recvTerm,
              List(MatchBranch(ctor.name, fields, Term.Var(fields.length - 1 - fieldIdx)))
            )
            projMatchOpt = Some((projMatch, resultTy))
          }
        case _ => ()
      }

      projMatchOpt match {
        case Some((projMatch, resultTy)) => Right((projMatch, resultTy, env1))
        case None =>
          // Otherwise try UFCS: `recv.member` -> `member(recv)`
          if (env1.kernelEnv.lookupConstType(member).isDefined) {
            elaborateCall(env1, metaCtx, localCtx, SurfaceExpr.VarExpr(member, span), List(receiver), span)
          } else {
            Left(
              Diagnostic(
                Diagnostic.Severity.Error,
                "E063",
                s"No field or function '$member' applicable to value of type '${Pretty.show(metaCtx.zonk(recvType, localCtx.depth), localCtx.names)}'",
                span
              )
            )
          }
      }
    }
  }

  private def elaborateTypeApp(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    callee: SurfaceExpr,
    typeArgs: List[SurfaceExpr],
    span: Span
  ): Either[Diagnostic, (Term, Term, ElabEnv)] = {
    val headRes: Either[Diagnostic, (Term, Term, ElabEnv)] = callee match {
      case SurfaceExpr.VarExpr(name, s) =>
        resolveIdentifier(env, metaCtx, localCtx, name, insertImplicits = false, s)
      case SurfaceExpr.SelectExpr(recv, mem, s) =>
        elaborateSelect(env, metaCtx, localCtx, recv, mem, insertImplicits = false, s)
      case other =>
        inferExpr(env, metaCtx, localCtx, other)
    }
    headRes.flatMap { case (headTerm, headType, env1) =>
      applyArgsList(env1, metaCtx, localCtx, headTerm, headType, typeArgs, span)
    }
  }

  private def elaborateCall(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    callee: SurfaceExpr,
    args: List[SurfaceExpr],
    span: Span
  ): Either[Diagnostic, (Term, Term, ElabEnv)] = {
    // 0. Well-founded recursive call inside `termination_by` body:
    //    `f(a_0, ..., a_{m-1})` -> `f_wf(a_0, ..., a_{m-1}, _wfInv(nextMeasure, eqSubstLt(..., decreaseProof, _wfEqM)))`
    env.wfContext match {
      case Some(wf) =>
        val matchedWfCall: Option[List[SurfaceExpr]] = callee match {
          case SurfaceExpr.VarExpr(name, _) if name == wf.fnName =>
            Some(args)
          case SurfaceExpr.TypeAppExpr(SurfaceExpr.VarExpr(name, _), tArgs, _) if name == wf.fnName =>
            Some(tArgs ++ args)
          case _ => None
        }
        matchedWfCall match {
          case Some(allSurfaceArgs) =>
            val depth = localCtx.depth
            val wfSelfIdx = depth - 1 - wf.wfSelfLevel
            val wfSelfType = localCtx.lookupType(wfSelfIdx).get
            val wfSelfBase = Term.Var(wfSelfIdx)
            val impCount =
              callee match {
                case SurfaceExpr.TypeAppExpr(_, _, _) => 0
                case _                                => env.implicitParamCounts.getOrElse(wf.fnName, 0)
              }
            val (fnWithImplicits, tyAfterImplicits) =
              if (impCount > 0) insertImplicitMetas(env.kernelEnv, metaCtx, localCtx, wfSelfBase, wfSelfType, impCount)
              else (wfSelfBase, wfSelfType)

            return applyArgsList(env, metaCtx, localCtx, fnWithImplicits, tyAfterImplicits, allSurfaceArgs, span).flatMap {
              case (appliedTerm, tyAfterArgs, env1) =>
                val (_, allAppliedArgs) = Term.splitApps(metaCtx.zonk(appliedTerm, depth))
                if (allAppliedArgs.length != wf.numBinders) {
                  Left(
                    Diagnostic(
                      Diagnostic.Severity.Error,
                      "E065",
                      s"Recursive call to '${wf.fnName}' expected ${wf.numBinders} total argument(s), got ${allAppliedArgs.length}",
                      span
                    )
                  )
                } else {
                  val nextMeasure = metaCtx.zonk(Term.substMany(wf.measureCore, allAppliedArgs), depth)
                  val curMeasureShift = depth - 1 - wf.numBinders
                  val curMeasureInCtx = Term.shift(wf.measureCore, curMeasureShift)
                  val decreaseGoal = Term.apps(Term.Const("Lt"), List(nextMeasure, curMeasureInCtx))
                  val zonkedLocalCtx = zonkLocalCtx(metaCtx, localCtx)

                  proveWellFoundedDecrease(env1, zonkedLocalCtx, decreaseGoal, wf.decreasingBy, span).flatMap { decreaseProof =>
                    val wfCurMeasureVar = Term.Var(depth - 1 - wf.wfCurMeasureLevel)
                    val wfInvVar = Term.Var(depth - 1 - wf.wfInvLevel)
                    val wfEqMVar = Term.Var(depth - 1 - wf.wfEqMLevel)
                    val liftedProof = Term.apps(
                      Term.Const("eqSubstLt"),
                      List(nextMeasure, curMeasureInCtx, wfCurMeasureVar, decreaseProof, wfEqMVar)
                    )
                    val smallerAcc = Term.apps(wfInvVar, List(nextMeasure, liftedProof))
                    val fullCall = Term.App(appliedTerm, smallerAcc)
                    // Peel final Acc Pi from tyAfterArgs to obtain result type
                    val fuel = new NbE.Fuel()
                    val evalEnv = NbE.buildEvalEnv(env1.kernelEnv, localCtx, fuel)
                    NbE.evaluate(env1.kernelEnv, evalEnv, metaCtx.zonk(tyAfterArgs, depth), fuel) match {
                      case Value.VPi(_, _, codClosure) =>
                        val accVal = NbE.evaluate(env1.kernelEnv, evalEnv, smallerAcc, fuel)
                        val resTy = NbE.quote(env1.kernelEnv, depth, NbE.applyClosure(env1.kernelEnv, codClosure, accVal, fuel), fuel)
                        Right((fullCall, resTy, env1))
                      case _ =>
                        Right((fullCall, tyAfterArgs, env1))
                    }
                  }
                }
            }
          case None => ()
        }
      case None => ()
    }

    // 1. Check UFCS method call: `receiver.method(arg1, arg2)` -> `method(receiver, arg1, arg2)`
    callee match {
      case SurfaceExpr.SelectExpr(receiver, methodName, selSpan) =>
        val isEnumOrModule = receiver match {
          case SurfaceExpr.VarExpr(qualName, _)
              if env.kernelEnv.inductives.contains(qualName) || env.loadedModules.contains(qualName) =>
            true
          case _ => false
        }
        if (!isEnumOrModule && env.kernelEnv.lookupConstType(methodName).isDefined) {
          return elaborateCall(env, metaCtx, localCtx, SurfaceExpr.VarExpr(methodName, selSpan), receiver :: args, span)
        }
      // 2. Check case class constructor sugar: `Pair(a, b)` -> `Pair.Mk(a, b)` (when NOT applied to Type args!)
      case SurfaceExpr.VarExpr(className, clsSpan) if env.recordFields.contains(className) =>
        val mkRef = SurfaceExpr.SelectExpr(SurfaceExpr.VarExpr(className, clsSpan), "Mk", clsSpan)
        return elaborateCall(env, metaCtx, localCtx, mkRef, args, span)
      case SurfaceExpr.TypeAppExpr(SurfaceExpr.VarExpr(className, clsSpan), tArgs, _)
          if env.recordFields.contains(className) =>
        val mkRef = SurfaceExpr.TypeAppExpr(
          SurfaceExpr.SelectExpr(SurfaceExpr.VarExpr(className, clsSpan), "Mk", clsSpan),
          tArgs,
          clsSpan
        )
        return elaborateCall(env, metaCtx, localCtx, mkRef, args, span)
      case _ => ()
    }

    inferExpr(env, metaCtx, localCtx, callee).flatMap { case (fnTerm, fnType, env1) =>
      applyArgsList(env1, metaCtx, localCtx, fnTerm, fnType, args, span)
    }
  }

  private def applyArgsList(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    initialFn: Term,
    initialType: Term,
    args: List[SurfaceExpr],
    callSpan: Span
  ): Either[Diagnostic, (Term, Term, ElabEnv)] = {
    boundary {
      var curFn = initialFn
      var curType = initialType
      var curEnv = env
      for (argExpr <- args) {
        val fuel = new NbE.Fuel()
        val evalEnv = NbE.buildEvalEnv(curEnv.kernelEnv, localCtx, fuel)
        val fnTyVal = NbE.evaluate(curEnv.kernelEnv, evalEnv, metaCtx.zonk(curType, localCtx.depth), fuel)
        fnTyVal match {
          case Value.VPi(_, domVal, codClosure) =>
            val domTerm = NbE.quote(curEnv.kernelEnv, localCtx.depth, domVal, fuel)
            checkExpr(curEnv, metaCtx, localCtx, argExpr, domTerm) match {
              case Left(err) => break(Left(err))
              case Right((argTerm, nextEnv)) =>
                curEnv = nextEnv
                curFn = Term.App(curFn, argTerm)
                val argVal = NbE.evaluate(curEnv.kernelEnv, evalEnv, metaCtx.zonk(argTerm, localCtx.depth), fuel)
                val nextTyVal = NbE.applyClosure(curEnv.kernelEnv, codClosure, argVal, fuel)
                curType = NbE.quote(curEnv.kernelEnv, localCtx.depth, nextTyVal, fuel)
            }
          case other =>
            val quoted = NbE.quote(curEnv.kernelEnv, localCtx.depth, other, fuel)
            break(
              Left(
                Diagnostic(
                  Diagnostic.Severity.Error,
                  "E064",
                  s"Cannot apply argument to non-function of type '${Pretty.show(quoted, localCtx.names)}'",
                  argExpr.span
                )
              )
            )
        }
      }
      Right((curFn, curType, curEnv))
    }
  }

  private def insertImplicitMetas(
    kernelEnv: KernelEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    baseTerm: Term,
    baseType: Term,
    count: Int
  ): (Term, Term) = {
    var curTerm = baseTerm
    var curType = baseType
    var remaining = count
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(kernelEnv, localCtx, fuel)

    while (remaining > 0) {
      val tyVal = NbE.evaluate(kernelEnv, evalEnv, metaCtx.zonk(curType, localCtx.depth), fuel)
      tyVal match {
        case Value.VPi(name, domVal, codClosure) =>
          val domTerm = NbE.quote(kernelEnv, localCtx.depth, domVal, fuel)
          val meta = metaCtx.freshMeta(localCtx.depth, domTerm, Some(name))
          curTerm = Term.App(curTerm, meta)
          val metaVal = NbE.evaluate(kernelEnv, evalEnv, meta, fuel)
          val nextTyVal = NbE.applyClosure(kernelEnv, codClosure, metaVal, fuel)
          curType = NbE.quote(kernelEnv, localCtx.depth, nextTyVal, fuel)
          remaining -= 1
        case _ =>
          remaining = 0
      }
    }
    (curTerm, curType)
  }

  // ===========================================================================
  // Pattern Matching Elaboration (Dependent Motives + Unreachable Case Synthesis!)
  // ===========================================================================

  private def elaborateMatch(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    matchExpr: SurfaceExpr.MatchExpr,
    expectedTypeOpt: Option[Term]
  ): Either[Diagnostic, (Term, Term, ElabEnv)] = {
    boundary {
      val (scrutTerm, scrutTypeRaw, env1) = inferExpr(env, metaCtx, localCtx, matchExpr.scrutinee) match {
        case Left(err) => break(Left(err))
        case Right(r)  => r
      }
      val fuel = new NbE.Fuel()
      val evalEnv = NbE.buildEvalEnv(env1.kernelEnv, localCtx, fuel)
      val scrutTypeVal = NbE.evaluate(env1.kernelEnv, evalEnv, metaCtx.zonk(scrutTypeRaw, localCtx.depth), fuel)

      val (indName, paramTerms, indexTerms) = scrutTypeVal match {
        case Value.VInd(name, allArgs) =>
          val ind = env1.kernelEnv.inductives(name)
          val (pVals, iVals) = allArgs.splitAt(ind.numParams)
          (
            name,
            pVals.map(NbE.quote(env1.kernelEnv, localCtx.depth, _, fuel)),
            iVals.map(NbE.quote(env1.kernelEnv, localCtx.depth, _, fuel))
          )
        case other =>
          val quoted = NbE.quote(env1.kernelEnv, localCtx.depth, other, fuel)
          break(
            Left(
              Diagnostic(
                Diagnostic.Severity.Error,
                "E070",
                s"Match scrutinee must have an inductive type, found '${Pretty.show(quoted, localCtx.names)}'",
                matchExpr.scrutinee.span
              )
            )
          )
      }

      val indEntry = env1.kernelEnv.inductives(indName)
      val resultType: Term = expectedTypeOpt.getOrElse(
        metaCtx.freshMeta(localCtx.depth, Term.USort(Sort.Type(0)), Some("matchResult"))
      )

      // Map user cases to constructors (handling wildcards, literals, cons, and nested patterns)
      val expandedCases = expandUserCases(indEntry, matchExpr.cases, matchExpr.span) match {
        case Left(err) => break(Left(err))
        case Right(m)  => m
      }

      // Check for omitted unreachable constructors on indexed types (e.g. Vec[A](Succ(n)) omitting Nil!)
      val missingCtors = indEntry.constructors.filterNot(c => expandedCases.contains(c.name))

      if (missingCtors.nonEmpty && indEntry.numIndices > 0) {
        // Attempt discriminating motive synthesis for impossible constructors!
        tryBuildIndexedDiscriminatingMatch(
          env1,
          metaCtx,
          localCtx,
          indEntry,
          paramTerms,
          indexTerms,
          scrutTerm,
          resultType,
          expandedCases,
          matchExpr.span
        ) match {
          case Right(res) => return Right(res)
          case Left(err)  => break(Left(err))
        }
      }

      if (missingCtors.nonEmpty) {
        break(
          Left(
            Diagnostic(
              Diagnostic.Severity.Error,
              "E071",
              s"Non-exhaustive match on '${indEntry.name}': missing case(s) for ${missingCtors.map(_.name).mkString(", ")}",
              matchExpr.span
            )
          )
        )
      }

      // Inside a well-founded `termination_by` body, track branch equalities `_wf_eq : scrut === Ctor(...)`
      // so `if` conditions and `match` patterns are available automatically to the decrease prover!
      if (
        env1.wfContext.isDefined &&
        matchExpr.motive.isEmpty &&
        indEntry.numIndices == 0 &&
        env1.kernelEnv.inductives.contains("Eq")
      ) {
        val scrutTypeClean = Term.apps(Term.Ind(indName), paramTerms)
        val eqPi = Term.Pi(
          "_wfBranchEq",
          Term.apps(Term.Ind("Eq"), List(Term.shift(scrutTypeClean, 1), Term.shift(scrutTerm, 1), Term.Var(0))),
          Term.shift(resultType, 2)
        )
        val eqMotiveTerm = Term.Lam("_wfScrut", scrutTypeClean, eqPi)
        var curEnv = env1
        val kernelBranches = List.newBuilder[MatchBranch]
        for (ctor <- indEntry.constructors) {
          val (fieldBinders, bodyExpr) = expandedCases(ctor.name)
          val instFields = indEntry.instantiateFields(ctor, paramTerms)
          val branchCtx = instFields.zip(fieldBinders).foldLeft(localCtx) { case (ctx, (binder, fieldName)) =>
            ctx.push(fieldName, binder.ty)
          }
          val r = ctor.arity
          val ctorApp = Term.apps(
            Term.Ctor(indName, ctor.name),
            paramTerms.map(Term.shift(_, r)) ++ (0 until r).toList.map(k => Term.Var(r - 1 - k))
          )
          val eqHypName = s"_wf_eq_${localCtx.depth}"
          val eqHypType = Term.apps(Term.Ind("Eq"), List(Term.shift(scrutTypeClean, r), Term.shift(scrutTerm, r), ctorApp))
          val branchCtxWithEq = branchCtx.push(eqHypName, eqHypType)
          val expectedBranchRet = Term.shift(resultType, r + 1)
          checkExpr(curEnv, metaCtx, branchCtxWithEq, bodyExpr, expectedBranchRet) match {
            case Left(err) => break(Left(err))
            case Right((branchBodyTerm, nextEnv)) =>
              curEnv = nextEnv
              kernelBranches += MatchBranch(ctor.name, fieldBinders, Term.Lam(eqHypName, eqHypType, branchBodyTerm))
          }
        }
        val matchTerm = Term.Match(indName, paramTerms, eqMotiveTerm, scrutTerm, kernelBranches.result())
        val reflScrut = Term.apps(Term.Ctor("Eq", "Refl"), List(scrutTypeClean, scrutTerm))
        break(Right((Term.App(matchTerm, reflScrut), resultType, curEnv)))
      }

      // Build motive (explicit `returning`, dependent abstraction on scrutinee var, or constant motive)
      val motiveTerm: Term = matchExpr.motive match {
        case Some(motiveExpr) =>
          elaborateMatchMotive(env1, metaCtx, localCtx, indEntry, paramTerms, motiveExpr) match {
            case Left(err) => break(Left(err))
            case Right(m)  => m
          }
        case None =>
          synthesizeMotive(indEntry, paramTerms, indexTerms, scrutTerm, resultType)
      }

      // Elaborate each constructor branch in kernel order
      var curEnv = env1
      val kernelBranches = List.newBuilder[MatchBranch]
      for (ctor <- indEntry.constructors) {
        val (fieldBinders, bodyExpr) = expandedCases(ctor.name)
        val instFields = indEntry.instantiateFields(ctor, paramTerms)
        val branchCtx = instFields.zip(fieldBinders).foldLeft(localCtx) { case (ctx, (binder, fieldName)) =>
          ctx.push(fieldName, binder.ty)
        }
        val expectedBranchTy = indEntry.branchBodyType(ctor, paramTerms, motiveTerm)
        checkExpr(curEnv, metaCtx, branchCtx, bodyExpr, expectedBranchTy) match {
          case Left(err) => break(Left(err))
          case Right((branchBodyTerm, nextEnv)) =>
            curEnv = nextEnv
            kernelBranches += MatchBranch(ctor.name, fieldBinders, branchBodyTerm)
        }
      }

      val matchTerm = Term.Match(indName, paramTerms, motiveTerm, scrutTerm, kernelBranches.result())
      val inferredMatchType = Term.apps(motiveTerm, indexTerms :+ scrutTerm)
      Right((matchTerm, inferredMatchType, curEnv))
    }
  }

  private def synthesizeMotive(
    indEntry: IndEntry,
    paramTerms: List[Term],
    indexTerms: List[Term],
    scrutTerm: Term,
    resultType: Term
  ): Term = {
    val instIndices = indEntry.instantiateIndices(paramTerms)
    val numIdx = indEntry.numIndices
    val idxVars = (0 until numIdx).toList.map(j => Term.Var(numIdx - 1 - j))
    val scrutBinderTy = Term.apps(Term.Ind(indEntry.name), paramTerms.map(Term.shift(_, numIdx)) ++ idxVars)

    // Dependent abstraction when scrutinee (and indices) are local variables!
    val bodyUnderBinders: Term = {
      var body = Term.shift(resultType, numIdx + 1)
      // Replace shifted scrutinee variable with Var(0)
      scrutTerm match {
        case Term.Var(scrutIdx) =>
          body = replaceVar(body, scrutIdx + numIdx + 1, Term.Var(0))
        case _ => ()
      }
      // Replace shifted index variables with their motive index binders
      for ((idxTerm, pos) <- indexTerms.zipWithIndex) {
        idxTerm match {
          case Term.Var(varIdx) =>
            val targetBinderIdx = numIdx - pos // since scrutinee is at 0, last index is at 1, first at numIdx
            body = replaceVar(body, varIdx + numIdx + 1, Term.Var(targetBinderIdx))
          case _ => ()
        }
      }
      body
    }

    val scrutLam = Term.Lam("_scrut", scrutBinderTy, bodyUnderBinders)
    Term.lams(instIndices, scrutLam)
  }

  private def replaceVar(term: Term, targetIdx: Int, replacement: Term): Term = term match {
    case Term.Var(i) if i == targetIdx => replacement
    case Term.USort(_) | Term.Var(_) | Term.Const(_) | Term.Ind(_) | Term.Ctor(_, _) => term
    case Term.Pi(n, d, c) => Term.Pi(n, replaceVar(d, targetIdx, replacement), replaceVar(c, targetIdx + 1, Term.shift(replacement, 1)))
    case Term.Lam(n, d, b) => Term.Lam(n, replaceVar(d, targetIdx, replacement), replaceVar(b, targetIdx + 1, Term.shift(replacement, 1)))
    case Term.App(f, a) => Term.App(replaceVar(f, targetIdx, replacement), replaceVar(a, targetIdx, replacement))
    case Term.Let(n, ty, v, b) =>
      Term.Let(n, replaceVar(ty, targetIdx, replacement), replaceVar(v, targetIdx, replacement), replaceVar(b, targetIdx + 1, Term.shift(replacement, 1)))
    case Term.Match(ind, ps, m, s, brs) =>
      Term.Match(
        ind,
        ps.map(replaceVar(_, targetIdx, replacement)),
        replaceVar(m, targetIdx, replacement),
        replaceVar(s, targetIdx, replacement),
        brs.map(br => br.copy(body = replaceVar(br.body, targetIdx + br.arity, Term.shift(replacement, br.arity))))
      )
    case Term.Fix(n, r, ty, b) =>
      Term.Fix(n, r, replaceVar(ty, targetIdx, replacement), replaceVar(b, targetIdx + 1, Term.shift(replacement, 1)))
    case Term.MutualFix(defs, sel) =>
      val k = defs.length
      Term.MutualFix(
        defs.map(d =>
          d.copy(
            ty = replaceVar(d.ty, targetIdx, replacement),
            body = replaceVar(d.body, targetIdx + k, Term.shift(replacement, k))
          )
        ),
        sel
      )
  }

  private def elaborateMatchMotive(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    indEntry: IndEntry,
    paramTerms: List[Term],
    motiveExpr: SurfaceExpr
  ): Either[Diagnostic, Term] = {
    val expectedMotiveType = indEntry.motiveType(paramTerms, Sort.Type(0))
    checkExpr(env, metaCtx, localCtx, motiveExpr, expectedMotiveType).map(_._1).orElse {
      val propMotiveType = indEntry.motiveType(paramTerms, Sort.Prop)
      checkExpr(env, metaCtx, localCtx, motiveExpr, propMotiveType).map(_._1)
    }
  }

  /**
   * Automatically constructs a 100% kernel-verified discriminating motive for indexed matches
   * with unreachable constructors (e.g. `head(v: Vec[A](Succ(n)))` omitting `Vec.Nil`!).
   */
  private def tryBuildIndexedDiscriminatingMatch(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    indEntry: IndEntry,
    paramTerms: List[Term],
    indexTerms: List[Term],
    scrutTerm: Term,
    resultType: Term,
    expandedCases: Map[String, (List[String], SurfaceExpr)],
    span: Span
  ): Either[Diagnostic, (Term, Term, ElabEnv)] = {
    boundary {
      // Find an index position `discIdxPos` whose actual scrutinee index is headed by a constructor `actualCtor`
      // of an inductive type `idxIndName`, and every missing constructor of `indEntry` has a DIFFERENT constructor head!
      val instIndices = indEntry.instantiateIndices(paramTerms)
      val numIdx = indEntry.numIndices

      var chosenOpt: Option[(Int, IndEntry, List[Term], String)] = None
      for (pos <- 0 until numIdx if chosenOpt.isEmpty) {
        val actualIdxNorm = NbE.normalize(env.kernelEnv, localCtx, indexTerms(pos))
        val (actualHead, _) = Term.splitApps(actualIdxNorm)
        actualHead match {
          case Term.Ctor(idxIndName, actualCtorName) =>
            env.kernelEnv.inductives.get(idxIndName).foreach { idxInd =>
              val allMissingDisjoint = indEntry.constructors.forall { ctor =>
                if (expandedCases.contains(ctor.name)) true
                else {
                  val ctorResIdx = ctor.resultIndices(pos)
                  val (ctorIdxHead, _) = Term.splitApps(ctorResIdx)
                  ctorIdxHead match {
                    case Term.Ctor(ci, cc) if ci == idxIndName && cc != actualCtorName => true
                    case _ => false
                  }
                }
              }
              if (allMissingDisjoint) {
                val (idxTyHead, idxTyArgs) = Term.splitApps(instIndices(pos).ty)
                if (idxTyHead == Term.Ind(idxIndName)) {
                  chosenOpt = Some((pos, idxInd, idxTyArgs.take(idxInd.numParams), actualCtorName))
                }
              }
            }
          case _ => ()
        }
      }

      val (discPos, idxInd, idxIndParams, actualCtorName) = chosenOpt match {
        case Some(found) => found
        case None =>
          val missing = indEntry.constructors.filterNot(c => expandedCases.contains(c.name)).map(_.name)
          return Left(
            Diagnostic(
              Diagnostic.Severity.Error,
              "E071",
              s"Non-exhaustive match on '${indEntry.name}': missing case(s) for ${missing.mkString(", ")}",
              span
            )
          )
      }

      // Build discriminating motive:
      // (i_0..i_{m-1}) => (_s: Ind(params, i_0..i_{m-1})) =>
      //   i_{discPos} match {
      //     case actualCtor(...) => resultType
      //     case otherCtor(...)  => idxIndType (inhabited by i_{discPos} itself!)
      //   }
      val idxVars = (0 until numIdx).toList.map(j => Term.Var(numIdx - 1 - j))
      val scrutBinderTy = Term.apps(Term.Ind(indEntry.name), paramTerms.map(Term.shift(_, numIdx)) ++ idxVars)
      val discVarUnderMotive = Term.Var(numIdx - discPos) // scrut is 0, last idx is 1, discPos is numIdx - discPos
      val discTypeUnderMotive = Term.shift(instIndices(discPos).ty, numIdx - discPos + 1)
      val shiftedResultType = Term.shift(resultType, numIdx + 1)

      val targetSort = TypeChecker.inferSort(env.kernelEnv, localCtx, metaCtx.zonk(resultType, localCtx.depth)).getOrElse(Sort.Type(0))
      val innerMotive = Term.Lam("_d", discTypeUnderMotive, Term.USort(targetSort))

      val dummyTypeForImpossible: Term =
        if (targetSort == Sort.Prop && env.kernelEnv.inductives.contains("True")) Term.Ind("True")
        else if (env.kernelEnv.inductives.contains("Unit")) Term.Ind("Unit")
        else discTypeUnderMotive

      val discBranches = idxInd.constructors.map { idxCtor =>
        val arity = idxCtor.arity
        val body =
          if (idxCtor.name == actualCtorName) Term.shift(shiftedResultType, arity)
          else Term.shift(dummyTypeForImpossible, arity)
        MatchBranch(idxCtor.name, idxCtor.fields.map(_.name), body)
      }

      val motiveBody = Term.Match(
        idxInd.name,
        idxIndParams.map(Term.shift(_, numIdx + 1)),
        innerMotive,
        discVarUnderMotive,
        discBranches
      )
      val motiveTerm = Term.lams(instIndices, Term.Lam("_scrut", scrutBinderTy, motiveBody))

      // Build branches for every constructor of `indEntry`
      var curEnv = env
      val kernelBranches = List.newBuilder[MatchBranch]
      for (ctor <- indEntry.constructors) {
        val instFields = indEntry.instantiateFields(ctor, paramTerms)
        expandedCases.get(ctor.name) match {
          case Some((fieldBinders, bodyExpr)) =>
            val branchCtx = instFields.zip(fieldBinders).foldLeft(localCtx) { case (ctx, (binder, fieldName)) =>
              ctx.push(fieldName, binder.ty)
            }
            val expectedBranchTy = indEntry.branchBodyType(ctor, paramTerms, motiveTerm)
            checkExpr(curEnv, metaCtx, branchCtx, bodyExpr, expectedBranchTy) match {
              case Left(err) => break(Left(err))
              case Right((branchBodyTerm, nextEnv)) =>
                curEnv = nextEnv
                kernelBranches += MatchBranch(ctor.name, fieldBinders, branchBodyTerm)
            }

          case None =>
            // Impossible constructor! Synthesize dummy inhabitant matching `dummyTypeForImpossible`!
            val dummyInhabitant: Term =
              if (targetSort == Sort.Prop && env.kernelEnv.inductives.contains("True")) Term.Ctor("True", "Intro")
              else if (env.kernelEnv.inductives.contains("Unit")) Term.Ctor("Unit", "Mk")
              else indEntry.instantiateResultIndices(ctor, paramTerms)(discPos)
            kernelBranches += MatchBranch(ctor.name, ctor.fields.map(_.name), dummyInhabitant)
        }
      }

      val matchTerm = Term.Match(indEntry.name, paramTerms, motiveTerm, scrutTerm, kernelBranches.result())
      val inferredMatchType = Term.apps(motiveTerm, indexTerms :+ scrutTerm)
      Right((matchTerm, inferredMatchType, curEnv))
    }
  }

  /**
   * Decision-tree pattern matrix compiler: expands surface match cases (wildcards, variable
   * fallbacks, Nat/Bool/Cons literals, and multi-clause overlapping nested patterns such as
   * `case 0 => ...; case 1 => ...; case _ => ...` or `case a :: b :: rest => ...`)
   * into a map `ctorName -> (fieldBinderNames, bodySurfaceExpr)`.
   */
  private def expandUserCases(
    indEntry: IndEntry,
    cases: List[MatchCase],
    span: Span
  ): Either[Diagnostic, Map[String, (List[String], SurfaceExpr)]] = {
    boundary {
      val normalizedRows: List[(Pattern, SurfaceExpr)] = cases.map { mc =>
        (normalizePattern(indEntry.name, mc.pattern), mc.body)
      }

      // Validate all top-level constructor patterns belong to `indEntry` and have right arity
      for ((pat, _) <- normalizedRows) {
        pat match {
          case Pattern.Ctor(qualOpt, ctorName, subPats, patSpan) =>
            qualOpt.foreach { q =>
              if (q != indEntry.name) {
                break(Left(Diagnostic(Diagnostic.Severity.Error, "E072", s"Pattern constructor '$q.$ctorName' does not match type '${indEntry.name}'", patSpan)))
              }
            }
            val ctor = indEntry.ctor(ctorName) match {
              case Some(c) => c
              case None =>
                break(Left(Diagnostic(Diagnostic.Severity.Error, "E073", s"Inductive '${indEntry.name}' has no constructor '$ctorName'", patSpan)))
            }
            if (subPats.length != ctor.arity) {
              break(
                Left(
                  Diagnostic(
                    Diagnostic.Severity.Error,
                    "E074",
                    s"Constructor '${indEntry.name}.$ctorName' expects ${ctor.arity} pattern argument(s), got ${subPats.length}",
                    patSpan
                  )
                )
              )
            }
          case Pattern.Wildcard(_) | Pattern.Var(_, _) => ()
          case other =>
            break(Left(Diagnostic(Diagnostic.Severity.Error, "E075", s"Unsupported pattern '$other' for '${indEntry.name}'", other.span)))
        }
      }

      var result = Map.empty[String, (List[String], SurfaceExpr)]

      // Specialize the ordered pattern matrix for each constructor of `indEntry`
      for (ctor <- indEntry.constructors) {
        val defaultFieldNames = ctor.fields.zipWithIndex.map { case (f, i) => s"_f${i}_${f.name}" }
        val specializedRows = List.newBuilder[(List[Pattern], SurfaceExpr)]

        for ((pat, body) <- normalizedRows) {
          pat match {
            case Pattern.Ctor(_, cName, subPats, _) if cName == ctor.name =>
              specializedRows += ((subPats, body))
            case Pattern.Wildcard(pSpan) =>
              specializedRows += ((List.fill(ctor.arity)(Pattern.Wildcard(pSpan)), body))
            case Pattern.Var(boundName, pSpan) =>
              val ctorExpr =
                if (defaultFieldNames.isEmpty) SurfaceExpr.SelectExpr(SurfaceExpr.VarExpr(indEntry.name, pSpan), ctor.name, pSpan)
                else SurfaceExpr.CallExpr(
                  SurfaceExpr.SelectExpr(SurfaceExpr.VarExpr(indEntry.name, pSpan), ctor.name, pSpan),
                  defaultFieldNames.map(SurfaceExpr.VarExpr(_, pSpan)),
                  pSpan
                )
              val wrappedBody = SurfaceExpr.BlockExpr(
                List(BlockStatement.LocalVal(boundName, None, ctorExpr, pSpan)),
                body,
                pSpan
              )
              specializedRows += ((List.fill(ctor.arity)(Pattern.Wildcard(pSpan)), wrappedBody))
            case _ => ()
          }
        }

        val rows = specializedRows.result()
        if (rows.nonEmpty) {
          val (firstSubPats, firstBody) = rows.head
          val firstIsFlat = firstSubPats.forall {
            case Pattern.Var(_, _) | Pattern.Wildcard(_) => true
            case _                                       => false
          }
          if (firstIsFlat) {
            val binderNames = firstSubPats.zipWithIndex.map {
              case (Pattern.Var(n, _), _) => n
              case (_, i)                 => defaultFieldNames(i)
            }
            result = result + (ctor.name -> (binderNames, firstBody))
          } else {
            val compiledBody = compileSubpatternMatrix(defaultFieldNames, rows, span)
            result = result + (ctor.name -> (defaultFieldNames, compiledBody))
          }
        }
      }

      Right(result)
    }
  }

  /**
   * Compile a multi-column sub-pattern matrix (for nested constructor patterns like `case 1 => ...; case 2 => ...`).
   */
  private def compileSubpatternMatrix(
    colVarNames: List[String],
    rows: List[(List[Pattern], SurfaceExpr)],
    span: Span
  ): SurfaceExpr = {
    val firstRow = rows.head
    // Find first column containing a nested constructor/literal pattern in any row
    val nestedColIdx = (0 until colVarNames.length).indexWhere { col =>
      rows.exists { case (pats, _) =>
        pats(col) match {
          case Pattern.Var(_, _) | Pattern.Wildcard(_) => false
          case _                                       => true
        }
      }
    }

    if (nestedColIdx < 0) {
      // Base case: bind any Var patterns in the first matching row via local val
      val bindings = firstRow._1.zip(colVarNames).collect {
        case (Pattern.Var(userName, pSpan), colVar) if userName != colVar =>
          BlockStatement.LocalVal(userName, None, SurfaceExpr.VarExpr(colVar, pSpan), pSpan)
      }
      if (bindings.isEmpty) firstRow._2
      else SurfaceExpr.BlockExpr(bindings, firstRow._2, span)
    } else {
      val scrutVarName = colVarNames(nestedColIdx)
      val remainingCols = colVarNames.patch(nestedColIdx, Nil, 1)
      val innerCases = rows.map { case (pats, body) =>
        val colPat = pats(nestedColIdx)
        val otherPats = pats.patch(nestedColIdx, Nil, 1)
        val innerBody =
          if (remainingCols.isEmpty) body
          else compileSubpatternMatrix(remainingCols, List((otherPats, body)), span)
        MatchCase(colPat, innerBody, colPat.span)
      }
      SurfaceExpr.MatchExpr(SurfaceExpr.VarExpr(scrutVarName, span), None, innerCases, span)
    }
  }

  private def normalizePattern(indName: String, pat: Pattern): Pattern = pat match {
    case Pattern.NatLit(0, s) => Pattern.Ctor(Some("Nat"), "Zero", Nil, s)
    case Pattern.NatLit(n, s) if n > 0 =>
      Pattern.Ctor(Some("Nat"), "Succ", List(normalizePattern("Nat", Pattern.NatLit(n - 1, s))), s)
    case Pattern.BoolLit(true, s)  => Pattern.Ctor(Some("Bool"), "True", Nil, s)
    case Pattern.BoolLit(false, s) => Pattern.Ctor(Some("Bool"), "False", Nil, s)
    case Pattern.Cons(h, t, s) => Pattern.Ctor(Some("List"), "Cons", List(h, t), s)
    case Pattern.ListLit(elems, s) =>
      elems.foldRight[Pattern](Pattern.Ctor(Some("List"), "Nil", Nil, s)) { (headPat, tailPat) =>
        Pattern.Ctor(Some("List"), "Cons", List(headPat, tailPat), headPat.span.merge(tailPat.span))
      }
    case other => other
  }

  // ===========================================================================
  // Helpers
  // ===========================================================================

  private def evalToValue(kernelEnv: KernelEnv, localCtx: LocalCtx, term: Term): Value = {
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(kernelEnv, localCtx, fuel)
    NbE.evaluate(kernelEnv, evalEnv, term, fuel)
  }

  private def requireSymbol(env: ElabEnv, name: String, span: Span): Either[Diagnostic, Unit] =
    if (env.kernelEnv.contains(name)) Right(())
    else Left(Diagnostic(Diagnostic.Severity.Error, "E080", s"Operator requires '$name' to be in scope (try 'import Prelude.*')", span))

  private def checkAllMetasSolved(metaCtx: MetaContext, span: Span): Either[Diagnostic, Unit] = {
    val unsolved = metaCtx.unsolvedEntries
    if (unsolved.isEmpty) Right(())
    else {
      val details = unsolved.map(e => s"?${e.nameHint.getOrElse(e.id.toString)} : ${Pretty.show(e.expectedType)}").mkString(", ")
      Left(
        Diagnostic(
          Diagnostic.Severity.Error,
          "E081",
          s"Could not infer implicit argument(s) or unsolved hole(s): $details",
          span,
          hint = Some("Provide explicit type arguments with [...] or fill in '?' holes")
        )
      )
    }
  }

  private def mentionsIdent(expr: SurfaceExpr, targetName: String): Boolean = expr match {
    case SurfaceExpr.VarExpr(n, _)                 => n == targetName
    case SurfaceExpr.SelectExpr(r, _, _)           => mentionsIdent(r, targetName)
    case SurfaceExpr.TypeAppExpr(c, args, _)       => mentionsIdent(c, targetName) || args.exists(mentionsIdent(_, targetName))
    case SurfaceExpr.CallExpr(c, args, _)          => mentionsIdent(c, targetName) || args.exists(mentionsIdent(_, targetName))
    case SurfaceExpr.UnaryOpExpr(_, o, _)          => mentionsIdent(o, targetName)
    case SurfaceExpr.BinaryOpExpr(_, l, r, _)      => mentionsIdent(l, targetName) || mentionsIdent(r, targetName)
    case SurfaceExpr.ArrowExpr(ps, b, _, _)        => !ps.exists(_.name == targetName) && mentionsIdent(b, targetName)
    case SurfaceExpr.ExistsExpr(ps, b, _)          => !ps.exists(_.name == targetName) && mentionsIdent(b, targetName)
    case SurfaceExpr.BlockExpr(stmts, res, _) =>
      stmts.exists {
        case BlockStatement.LocalVal(_, _, v, _) => mentionsIdent(v, targetName)
        case BlockStatement.ExprStmt(e)          => mentionsIdent(e, targetName)
      } || mentionsIdent(res, targetName)
    case SurfaceExpr.IfExpr(c, t, e, _)            => mentionsIdent(c, targetName) || mentionsIdent(t, targetName) || mentionsIdent(e, targetName)
    case SurfaceExpr.MatchExpr(s, m, cs, _) =>
      mentionsIdent(s, targetName) || m.exists(mentionsIdent(_, targetName)) || cs.exists(c => mentionsIdent(c.body, targetName))
    case SurfaceExpr.AscribeExpr(e, t, _)          => mentionsIdent(e, targetName) || mentionsIdent(t, targetName)
    case SurfaceExpr.ListLitExpr(elems, _)         => elems.exists(mentionsIdent(_, targetName))
    case SurfaceExpr.CalcExpr(start, steps, _) =>
      mentionsIdent(start, targetName) || steps.exists(s => mentionsIdent(s.rhs, targetName) || mentionsIdent(s.proof, targetName))
    case _                                         => false
  }

  /**
   * Elaborate a human- and AI-readable `calc { a === b by { ... } === c by { ... } }`
   * equational reasoning block into a pure kernel `Eq` transitivity chain!
   */
  private def elaborateCalc(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    startExpr: SurfaceExpr,
    steps: List[CalcStep],
    span: Span
  ): Either[Diagnostic, (Term, Term, ElabEnv)] = boundary {
    requireSymbol(env, "Eq", span) match {
      case Left(err) => break(Left(err))
      case Right(()) => ()
    }
    val (startTerm, eqTypeRaw, env0) = inferExpr(env, metaCtx, localCtx, startExpr) match {
      case Left(err) => break(Left(err))
      case Right(r)  => r
    }
    val eqType = metaCtx.zonk(eqTypeRaw, localCtx.depth)
    var curEnv = env0
    var curTerm = startTerm
    var accProofOpt: Option[Term] = None

    for (step <- steps) {
      val (nextTerm, env1) = checkExpr(curEnv, metaCtx, localCtx, step.rhs, eqType) match {
        case Left(err) => break(Left(err))
        case Right(r)  => r
      }
      val stepEqType = Term.apps(Term.Ind("Eq"), List(eqType, curTerm, nextTerm))
      val (stepProof, env2) = checkExpr(env1, metaCtx, localCtx, step.proof, stepEqType) match {
        case Left(err) => break(Left(err))
        case Right(r)  => r
      }
      accProofOpt = Some(accProofOpt match {
        case None => stepProof
        case Some(prevProof) =>
          // Transitivity via pure kernel Match on Eq: prevProof: start === curTerm, stepProof: curTerm === nextTerm
          val eqType1 = Term.shift(eqType, 1)
          val cur1 = Term.shift(curTerm, 1)
          val eqType2 = Term.shift(eqType, 2)
          val start2 = Term.shift(startTerm, 2)
          val transMotive = Term.Lam(
            "_y",
            eqType,
            Term.Lam(
              "_q",
              Term.apps(Term.Ind("Eq"), List(eqType1, cur1, Term.Var(0))),
              Term.apps(Term.Ind("Eq"), List(eqType2, start2, Term.Var(1)))
            )
          )
          Term.Match("Eq", List(eqType, curTerm), transMotive, stepProof, List(MatchBranch("Refl", Nil, prevProof)))
      })
      curTerm = nextTerm
      curEnv = env2
    }

    val finalProof = accProofOpt.get
    val finalType = Term.apps(Term.Ind("Eq"), List(eqType, startTerm, curTerm))
    Right((finalProof, finalType, curEnv))
  }

  private def isUnboundTermBuiltin(env: ElabEnv, localCtx: LocalCtx, name: String): Boolean =
    !localCtx.entries.exists(_.name == name) && !env.kernelEnv.contains(name)

  /**
   * Flow-sensitive `if (cond) { thenBranch } else { elseBranch }` in Prop positions:
   * automatically provides `_if_eq : cond === true` in the then branch and
   * `_if_eq : cond === false` in the else branch via a pure 0-axiom `Eq.Refl` motive!
   */
  private def elaborateFlowSensitiveIf(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    cond: SurfaceExpr,
    thenBranch: SurfaceExpr,
    elseBranch: SurfaceExpr,
    expectedType: Term,
    span: Span
  ): Either[Diagnostic, (Term, ElabEnv)] = {
    val boolTy = Term.Ind("Bool")
    for {
      condRes <- checkExpr(env, metaCtx, localCtx, cond, boolTy)
      (condTermRaw, env1) = condRes
      condTerm = metaCtx.zonk(condTermRaw, localCtx.depth)
      eqName = s"_if_eq_${localCtx.depth}"
      trueEqTy = Term.apps(Term.Ind("Eq"), List(boolTy, condTerm, Term.Ctor("Bool", "True")))
      falseEqTy = Term.apps(Term.Ind("Eq"), List(boolTy, condTerm, Term.Ctor("Bool", "False")))
      expectedShifted = Term.shift(expectedType, 1)
      thenRes <- checkExpr(env1, metaCtx, localCtx.push(eqName, trueEqTy), thenBranch, expectedShifted)
      (thenTerm, env2) = thenRes
      elseRes <- checkExpr(env2, metaCtx, localCtx.push(eqName, falseEqTy), elseBranch, expectedShifted)
      (elseTerm, env3) = elseRes
    } yield {
      val motive = Term.Lam(
        "_ifScrut",
        boolTy,
        Term.Pi(
          "_ifEq",
          Term.apps(Term.Ind("Eq"), List(boolTy, Term.shift(condTerm, 1), Term.Var(0))),
          Term.shift(expectedType, 2)
        )
      )
      val matchTerm = Term.Match(
        "Bool",
        Nil,
        motive,
        condTerm,
        List(
          MatchBranch("True", Nil, Term.Lam(eqName, trueEqTy, thenTerm)),
          MatchBranch("False", Nil, Term.Lam(eqName, falseEqTy, elseTerm))
        )
      )
      val reflCond = Term.apps(Term.Ctor("Eq", "Refl"), List(boolTy, condTerm))
      (Term.App(matchTerm, reflCond), env3)
    }
  }

  private def extractInferredEq(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    tyTerm: Term,
    helperName: String,
    span: Span
  ): Either[Diagnostic, (Term, Term, Term)] = {
    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(env.kernelEnv, localCtx, fuel)
    NbE.evaluate(env.kernelEnv, evalEnv, metaCtx.zonk(tyTerm, localCtx.depth), fuel) match {
      case Value.VInd("Eq", List(aVal, lhsVal, rhsVal)) =>
        Right(
          (
            NbE.quote(env.kernelEnv, localCtx.depth, aVal, fuel),
            NbE.quote(env.kernelEnv, localCtx.depth, lhsVal, fuel),
            NbE.quote(env.kernelEnv, localCtx.depth, rhsVal, fuel)
          )
        )
      case _ =>
        Left(
          Diagnostic(
            Diagnostic.Severity.Error,
            "E059",
            s"'$helperName' expects an equality proof ('a === b'), found '${Pretty.show(metaCtx.zonk(tyTerm, localCtx.depth), localCtx.names)}'",
            span
          )
        )
    }
  }

  /** Term-mode `sym(eq)` — infers `A, a, b` and builds a pure 0-axiom `Eq` symmetry `Match`. */
  private def elaborateTermSym(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    eqExpr: SurfaceExpr,
    span: Span
  ): Either[Diagnostic, (Term, Term, ElabEnv)] = {
    for {
      _ <- requireSymbol(env, "Eq", span)
      eqRes <- inferExpr(env, metaCtx, localCtx, eqExpr)
      (eqTerm, eqTyRaw, env1) = eqRes
      eqParts <- extractInferredEq(env1, metaCtx, localCtx, eqTyRaw, "sym", eqExpr.span)
      (aTerm, lhsTerm, rhsTerm) = eqParts
    } yield {
      val a1 = Term.shift(aTerm, 1)
      val lhs1 = Term.shift(lhsTerm, 1)
      val a2 = Term.shift(aTerm, 2)
      val lhs2 = Term.shift(lhsTerm, 2)
      val symMotive = Term.Lam(
        "_y",
        aTerm,
        Term.Lam(
          "_q",
          Term.apps(Term.Ind("Eq"), List(a1, lhs1, Term.Var(0))),
          Term.apps(Term.Ind("Eq"), List(a2, Term.Var(1), lhs2))
        )
      )
      val symProof = Term.Match(
        "Eq",
        List(aTerm, lhsTerm),
        symMotive,
        eqTerm,
        List(MatchBranch("Refl", Nil, Term.apps(Term.Ctor("Eq", "Refl"), List(aTerm, lhsTerm))))
      )
      val resultTy = Term.apps(Term.Ind("Eq"), List(aTerm, rhsTerm, lhsTerm))
      (symProof, resultTy, env1)
    }
  }

  /** Term-mode `trans(eq1, eq2)` — infers types & middle term and builds a pure 0-axiom `Eq` transitivity `Match`. */
  private def elaborateTermTrans(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    eq1Expr: SurfaceExpr,
    eq2Expr: SurfaceExpr,
    span: Span
  ): Either[Diagnostic, (Term, Term, ElabEnv)] = {
    for {
      _ <- requireSymbol(env, "Eq", span)
      r1 <- inferExpr(env, metaCtx, localCtx, eq1Expr)
      (eq1Term, eq1TyRaw, env1) = r1
      p1 <- extractInferredEq(env1, metaCtx, localCtx, eq1TyRaw, "trans", eq1Expr.span)
      (a1Term, xTerm, y1Term) = p1
      r2 <- inferExpr(env1, metaCtx, localCtx, eq2Expr)
      (eq2Term, eq2TyRaw, env2) = r2
      p2 <- extractInferredEq(env2, metaCtx, localCtx, eq2TyRaw, "trans", eq2Expr.span)
      (a2Term, y2Term, zTerm) = p2
      _ <- metaCtx.unify(env2.kernelEnv, localCtx, a1Term, a2Term).left.map(err =>
        Diagnostic(Diagnostic.Severity.Error, "E059", s"'trans' type mismatch: $err", span)
      )
      _ <- metaCtx.unify(env2.kernelEnv, localCtx, y1Term, y2Term).left.map(err =>
        Diagnostic(Diagnostic.Severity.Error, "E059", s"'trans' middle-term mismatch: $err", span)
      )
    } yield {
      val aTerm = metaCtx.zonk(a1Term, localCtx.depth)
      val xZ = metaCtx.zonk(xTerm, localCtx.depth)
      val yZ = metaCtx.zonk(y1Term, localCtx.depth)
      val zZ = metaCtx.zonk(zTerm, localCtx.depth)
      val a1 = Term.shift(aTerm, 1)
      val y1 = Term.shift(yZ, 1)
      val a2 = Term.shift(aTerm, 2)
      val x2 = Term.shift(xZ, 2)
      val transMotive = Term.Lam(
        "_y",
        aTerm,
        Term.Lam(
          "_q",
          Term.apps(Term.Ind("Eq"), List(a1, y1, Term.Var(0))),
          Term.apps(Term.Ind("Eq"), List(a2, x2, Term.Var(1)))
        )
      )
      val transProof = Term.Match(
        "Eq",
        List(aTerm, yZ),
        transMotive,
        eq2Term,
        List(MatchBranch("Refl", Nil, eq1Term))
      )
      val resultTy = Term.apps(Term.Ind("Eq"), List(aTerm, xZ, zZ))
      (transProof, resultTy, env2)
    }
  }

  /** Term-mode `cong(fn, eq)` — supports constructors (`Nat.Succ`) and unannotated lambdas (`k => h + k`)! */
  private def elaborateTermCong(
    env: ElabEnv,
    metaCtx: MetaContext,
    localCtx: LocalCtx,
    fnExpr: SurfaceExpr,
    eqExpr: SurfaceExpr,
    span: Span
  ): Either[Diagnostic, (Term, Term, ElabEnv)] = {
    for {
      _ <- requireSymbol(env, "Eq", span)
      eqRes <- inferExpr(env, metaCtx, localCtx, eqExpr)
      (eqTerm, eqTyRaw, env1) = eqRes
      eqParts <- extractInferredEq(env1, metaCtx, localCtx, eqTyRaw, "cong", eqExpr.span)
      (aTerm, lhsTerm, rhsTerm) = eqParts
      codMeta = metaCtx.freshMeta(localCtx.depth, Term.USort(Sort.Type(0)), Some("congCodomain"))
      expectedFnTy = Term.Pi("_x", aTerm, Term.shift(codMeta, 1))
      fnRes <- checkExpr(env1, metaCtx, localCtx, fnExpr, expectedFnTy)
      (fnTermRaw, env2) = fnRes
    } yield {
      val fnTerm = metaCtx.zonk(fnTermRaw, localCtx.depth)
      val bTerm = metaCtx.zonk(codMeta, localCtx.depth)
      val a1 = Term.shift(aTerm, 1)
      val lhs1 = Term.shift(lhsTerm, 1)
      val b2 = Term.shift(bTerm, 2)
      val fn2 = Term.shift(fnTerm, 2)
      val lhs2 = Term.shift(lhsTerm, 2)
      val congMotive = Term.Lam(
        "_y",
        aTerm,
        Term.Lam(
          "_q",
          Term.apps(Term.Ind("Eq"), List(a1, lhs1, Term.Var(0))),
          Term.apps(Term.Ind("Eq"), List(b2, Term.App(fn2, lhs2), Term.App(fn2, Term.Var(1))))
        )
      )
      val congProof = Term.Match(
        "Eq",
        List(aTerm, lhsTerm),
        congMotive,
        eqTerm,
        List(MatchBranch("Refl", Nil, Term.apps(Term.Ctor("Eq", "Refl"), List(bTerm, Term.App(fnTerm, lhsTerm)))))
      )
      val resultTy = Term.apps(Term.Ind("Eq"), List(bTerm, Term.App(fnTerm, lhsTerm), Term.App(fnTerm, rhsTerm)))
      (congProof, resultTy, env2)
    }
  }
}
