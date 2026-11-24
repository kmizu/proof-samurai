package samurai.ai

import java.io.{BufferedReader, InputStreamReader, PrintWriter}
import java.nio.file.{Path, Paths}
import scala.collection.mutable
import scala.util.boundary
import scala.util.boundary.break
import samurai.elab.{ElabEnv, Elaborator, MetaContext}
import samurai.extract.{Erasure, HaskellEmitter, JsEmitter, OCamlEmitter, Scala3Emitter, TsEmitter}
import samurai.kernel.*
import samurai.syntax.Parser
import samurai.tactic.{ProofGoal, ProofSearch, ProofState, Tactics}
import samurai.util.Json

final case class SavedProofNode(
  stateId: Int,
  parentStateId: Option[Int],
  theoremName: String,
  theoremType: Term,
  tacticApplied: Option[String],
  proofState: ProofState
)

/**
 * Stateful, branching, backtracking-friendly proof session designed specifically for AI agents
 * (LLMs, tree search / MCTS provers) and IDE tooling.
 *
 * Every `step(stateId, tactic)` creates a new immutable state ID without mutating `stateId`,
 * enabling zero-cost exploration of multiple proof branches. When all goals close, the
 * reconstructed proof term is independently verified by the Trusted Kernel before acceptance.
 */
final class ProofSession(initialSearchPaths: List[Path] = List(Paths.get("."), Paths.get("stdlib"))) {
  private var currentEnv: ElabEnv = ElabEnv(searchPaths = initialSearchPaths)
  private val proofNodes: mutable.Map[Int, SavedProofNode] = mutable.LinkedHashMap.empty
  private var nextStateId: Int = 1

  def environment: ElabEnv = currentEnv

  def handleRequest(request: Json): Json = {
    val requestId = request.field("id").getOrElse(Json.Null)
    val method = request.field("method").flatMap(_.asString).getOrElse("")
    val params = request.field("params").getOrElse(Json.obj())

    val responseBody: Either[(String, String), Json] = method match {
      case "loadSource"    => handleLoadSource(params)
      case "loadFile"      => handleLoadFile(params)
      case "startProof"    => handleStartProof(params)
      case "step"          => handleStep(params)
      case "batchStep"     => handleBatchStep(params)
      case "proveGoal"     => handleProveGoal(params)
      case "autoSolve"     => handleAutoSolve(params)
      case "getProofTrace" => handleGetProofTrace(params)
      case "inspectHoles"  => handleInspectHoles(params)
      case "listSymbols"   => Right(handleListSymbols())
      case "suggest"       => handleSuggest(params)
      case "searchLemmas"  => handleSearchLemmas(params)
      case "extract"       => handleExtract(params)
      case "envSummary"    => Right(handleEnvSummary())
      case "ping"          => Right(Json.obj("status" -> Json.Str("ready"), "engine" -> Json.Str("proof-samurai")))
      case other           => Left(("RPC001", s"Unknown method '$other'"))
    }

    responseBody match {
      case Right(result) =>
        Json.obj("id" -> requestId, "ok" -> Json.Bool(true), "result" -> result)
      case Left((code, msg)) =>
        Json.obj(
          "id" -> requestId,
          "ok" -> Json.Bool(false),
          "error" -> Json.obj("code" -> Json.Str(code), "message" -> Json.Str(msg))
        )
    }
  }

  private def handleLoadSource(params: Json): Either[(String, String), Json] = {
    val fileName = params.field("file").flatMap(_.asString).getOrElse("<session>")
    val source = params.field("source").flatMap(_.asString).getOrElse("")
    Elaborator.checkSource(fileName, source, currentEnv) match {
      case Left(diag) =>
        Left((diag.code, diag.formatHuman(Some(source))))
      case Right(nextEnv) =>
        val newDirectives = nextEnv.directives.drop(currentEnv.directives.length)
        val newHoles = nextEnv.holes.drop(currentEnv.holes.length)
        currentEnv = nextEnv
        Right(
          Json.obj(
            "declarations" -> Json.Arr(currentEnv.kernelEnv.declOrder.map(Json.Str(_))),
            "directives" -> Json.Arr(newDirectives.map(_.toJson)),
            "holes" -> Json.Arr(newHoles.map(_.toJson(currentEnv.kernelEnv))),
            "axiomsUsed" -> Json.Arr(currentEnv.kernelEnv.allAxiomsUsed.toList.sorted.map(Json.Str(_))),
            "isAxiomFree" -> Json.Bool(currentEnv.kernelEnv.allAxiomsUsed.isEmpty)
          )
        )
    }
  }

  private def handleLoadFile(params: Json): Either[(String, String), Json] = {
    val pathStr = params.field("path").flatMap(_.asString).getOrElse("")
    if (pathStr.isEmpty) return Left(("RPC002", "Missing 'path' parameter"))
    Elaborator.checkFile(Paths.get(pathStr), currentEnv) match {
      case Left(diag) => Left((diag.code, diag.formatHuman()))
      case Right(nextEnv) =>
        currentEnv = nextEnv
        Right(handleEnvSummary())
    }
  }

  private def handleStartProof(params: Json): Either[(String, String), Json] = {
    val theoremName = params.field("name").flatMap(_.asString).getOrElse(s"goal_$nextStateId")
    val statementStr = params.field("statement").flatMap(_.asString).getOrElse("")
    if (statementStr.isEmpty) return Left(("RPC003", "Missing 'statement' parameter"))

    Parser.parseExprString("<proof-goal>", statementStr) match {
      case Left(diag) => Left((diag.code, diag.message))
      case Right(surfaceExpr) =>
        val metaCtx = new MetaContext()
        Elaborator.elaborateType(currentEnv, metaCtx, LocalCtx.empty, surfaceExpr) match {
          case Left(diag) => Left((diag.code, diag.message))
          case Right(goalTypeRaw) =>
            val goalType = metaCtx.zonk(goalTypeRaw, 0)
            TypeChecker.inferSort(currentEnv.kernelEnv, LocalCtx.empty, goalType) match {
              case Left(kErr) => Left((kErr.code, kErr.message))
              case Right(_) =>
                val initState = ProofState.initial(LocalCtx.empty, goalType, label = theoremName)
                val stateId = nextStateId
                nextStateId += 1
                proofNodes(stateId) = SavedProofNode(stateId, None, theoremName, goalType, None, initState)
                val suggestions = initState.currentGoal.map(ProofSearch.suggest(currentEnv, _)).getOrElse(Nil)
                Right(
                  Json.obj(
                    "stateId" -> Json.Num(stateId),
                    "theoremName" -> Json.Str(theoremName),
                    "isSolved" -> Json.Bool(false),
                    "openGoals" -> Json.Arr(initState.openGoals.map(_.toJson(currentEnv.kernelEnv))),
                    "suggestions" -> Json.Arr(suggestions.map(_.toJson))
                  )
                )
            }
        }
    }
  }

  private def handleStep(params: Json): Either[(String, String), Json] = {
    val stateId = params.field("stateId").flatMap(_.asInt).getOrElse(-1)
    val tacticText = params.field("tactic").flatMap(_.asString).getOrElse("")
    val node = proofNodes.get(stateId) match {
      case Some(n) => n
      case None    => return Left(("RPC004", s"Unknown proof stateId: $stateId"))
    }
    if (node.proofState.isSolved) {
      return Left(("RPC005", s"Proof state $stateId is already solved"))
    }

    Parser.parseTacticString("<tactic-step>", tacticText) match {
      case Left(diag) => Left((diag.code, diag.message))
      case Right(stmts) =>
        Tactics.runScript(currentEnv, node.proofState, stmts) match {
          case Left(diag) => Left((diag.code, diag.message))
          case Right((nextEnv, nextState)) =>
            val newId = nextStateId
            nextStateId += 1
            proofNodes(newId) = SavedProofNode(
              stateId = newId,
              parentStateId = Some(stateId),
              theoremName = node.theoremName,
              theoremType = node.theoremType,
              tacticApplied = Some(tacticText),
              proofState = nextState
            )

            if (nextState.isSolved) {
              // Kernel-verify the reconstructed proof term immediately!
              nextState.buildProofTerm match {
                case Left(err) => Left(("RPC006", err))
                case Right(proofTerm) =>
                  TypeChecker.checkDef(
                    nextEnv.kernelEnv,
                    node.theoremName,
                    node.theoremType,
                    proofTerm,
                    transparent = false,
                    isTheorem = true
                  ) match {
                    case Left(kErr) =>
                      Left((kErr.code, s"Kernel rejected synthesized proof: ${kErr.message}"))
                    case Right(verifiedKernel) =>
                      currentEnv = nextEnv.copy(kernelEnv = verifiedKernel)
                      val defEntry = verifiedKernel.defs(node.theoremName)
                      Right(
                        Json.obj(
                          "stateId" -> Json.Num(newId),
                          "parentStateId" -> Json.Num(stateId),
                          "isSolved" -> Json.Bool(true),
                          "kernelVerified" -> Json.Bool(true),
                          "proofTerm" -> Json.Str(Pretty.show(proofTerm)),
                          "axiomsUsed" -> Json.Arr(defEntry.axiomsUsed.toList.sorted.map(Json.Str(_))),
                          "isAxiomFree" -> Json.Bool(defEntry.axiomsUsed.isEmpty),
                          "openGoals" -> Json.Arr(Nil)
                        )
                      )
                  }
              }
            } else {
              val suggestions = nextState.currentGoal.map(ProofSearch.suggest(nextEnv, _)).getOrElse(Nil)
              Right(
                Json.obj(
                  "stateId" -> Json.Num(newId),
                  "parentStateId" -> Json.Num(stateId),
                  "isSolved" -> Json.Bool(false),
                  "kernelVerified" -> Json.Bool(false),
                  "openGoals" -> Json.Arr(nextState.openGoals.map(_.toJson(nextEnv.kernelEnv))),
                  "suggestions" -> Json.Arr(suggestions.map(_.toJson))
                )
              )
            }
        }
    }
  }

  private def handleBatchStep(params: Json): Either[(String, String), Json] = {
    val stateId = params.field("stateId").flatMap(_.asInt).getOrElse(-1)
    val tactics = params.field("tactics").flatMap(_.asArr).getOrElse(Nil).flatMap(_.asString)
    if (!proofNodes.contains(stateId)) return Left(("RPC004", s"Unknown proof stateId: $stateId"))
    val outcomes = tactics.map { tacticText =>
      val stepRes = handleStep(Json.obj("stateId" -> Json.Num(stateId), "tactic" -> Json.Str(tacticText)))
      stepRes match {
        case Right(res) =>
          Json.obj("tactic" -> Json.Str(tacticText), "ok" -> Json.Bool(true), "result" -> res)
        case Left((code, msg)) =>
          Json.obj(
            "tactic" -> Json.Str(tacticText),
            "ok" -> Json.Bool(false),
            "error" -> Json.obj("code" -> Json.Str(code), "message" -> Json.Str(msg))
          )
      }
    }
    Right(Json.obj("parentStateId" -> Json.Num(stateId), "outcomes" -> Json.Arr(outcomes)))
  }

  private def handleAutoSolve(params: Json): Either[(String, String), Json] = {
    val stateId = params.field("stateId").flatMap(_.asInt).getOrElse(-1)
    val maxDepth = params.field("maxDepth").flatMap(_.asInt).getOrElse(6)
    handleStep(Json.obj("stateId" -> Json.Num(stateId), "tactic" -> Json.Str(s"auto($maxDepth)")))
  }

  private def handleGetProofTrace(params: Json): Either[(String, String), Json] = {
    val stateId = params.field("stateId").flatMap(_.asInt).getOrElse(-1)
    if (!proofNodes.contains(stateId)) return Left(("RPC004", s"Unknown proof stateId: $stateId"))

    val stepsRev = List.newBuilder[String]
    var curOpt: Option[SavedProofNode] = proofNodes.get(stateId)
    val leafNode = curOpt.get
    while (curOpt.isDefined) {
      val n = curOpt.get
      n.tacticApplied.foreach(stepsRev += _)
      curOpt = n.parentStateId.flatMap(proofNodes.get)
    }
    val orderedSteps = stepsRev.result().reverse
    val script =
      if (orderedSteps.isEmpty) "by {\n}"
      else "by {\n" + orderedSteps.map(s => s"  $s").mkString("\n") + "\n}"

    Right(
      Json.obj(
        "stateId" -> Json.Num(stateId),
        "theoremName" -> Json.Str(leafNode.theoremName),
        "isSolved" -> Json.Bool(leafNode.proofState.isSolved),
        "steps" -> Json.Arr(orderedSteps.map(Json.Str(_))),
        "script" -> Json.Str(script)
      )
    )
  }

  /**
   * One-shot AI proof refinement call: tests a candidate tactic sequence against a theorem statement.
   * Returns either kernel verification confirmation OR the exact failing step, folded goal state,
   * and ranked tactic suggestions for the next LLM refinement turn.
   */
  private def handleProveGoal(params: Json): Either[(String, String), Json] = boundary {
    val theoremName = params.field("name").flatMap(_.asString).getOrElse(s"goal_$nextStateId")
    val statementStr = params.field("statement").flatMap(_.asString).getOrElse("")
    val tacticsList = params.field("tactics").flatMap(_.asArr).getOrElse(Nil).flatMap(_.asString)
    if (statementStr.isEmpty) break(Left(("RPC003", "Missing 'statement' parameter")))

    val goalType: Term = Parser.parseExprString("<proveGoal>", statementStr) match {
      case Left(diag) => break(Left((diag.code, diag.message)))
      case Right(surfaceExpr) =>
        val metaCtx = new MetaContext()
        Elaborator.elaborateType(currentEnv, metaCtx, LocalCtx.empty, surfaceExpr) match {
          case Left(diag) => break(Left((diag.code, diag.message)))
          case Right(raw) =>
            val z = metaCtx.zonk(raw, 0)
            TypeChecker.inferSort(currentEnv.kernelEnv, LocalCtx.empty, z) match {
              case Left(kErr) => break(Left((kErr.code, kErr.message)))
              case Right(_)   => z
            }
        }
    }

    var workingEnv = currentEnv
    var state = ProofState.initial(LocalCtx.empty, goalType, label = theoremName)

    for ((tacticStr, stepIdx) <- tacticsList.zipWithIndex) {
      Parser.parseTacticString("<proveGoal-step>", tacticStr) match {
        case Left(diag) =>
          val sugs = state.currentGoal.map(ProofSearch.suggest(workingEnv, _)).getOrElse(Nil)
          break(
            Right(
              Json.obj(
                "verified" -> Json.Bool(false),
                "failedAtStep" -> Json.Num(stepIdx),
                "failedTactic" -> Json.Str(tacticStr),
                "error" -> Json.Str(diag.message),
                "remainingGoals" -> Json.Arr(state.openGoals.map(_.toJson(workingEnv.kernelEnv))),
                "suggestions" -> Json.Arr(sugs.map(_.toJson))
              )
            )
          )
        case Right(stmts) =>
          Tactics.runScript(workingEnv, state, stmts) match {
            case Left(diag) =>
              val sugs = state.currentGoal.map(ProofSearch.suggest(workingEnv, _)).getOrElse(Nil)
              break(
                Right(
                  Json.obj(
                    "verified" -> Json.Bool(false),
                    "failedAtStep" -> Json.Num(stepIdx),
                    "failedTactic" -> Json.Str(tacticStr),
                    "error" -> Json.Str(diag.message),
                    "remainingGoals" -> Json.Arr(state.openGoals.map(_.toJson(workingEnv.kernelEnv))),
                    "suggestions" -> Json.Arr(sugs.map(_.toJson))
                  )
                )
              )
            case Right((nextEnv, nextState)) =>
              workingEnv = nextEnv
              state = nextState
          }
      }
    }

    if (!state.isSolved) {
      val sugs = state.currentGoal.map(ProofSearch.suggest(workingEnv, _)).getOrElse(Nil)
      Right(
        Json.obj(
          "verified" -> Json.Bool(false),
          "error" -> Json.Str(s"Proof incomplete: ${state.openGoals.length} remaining goal(s)"),
          "remainingGoals" -> Json.Arr(state.openGoals.map(_.toJson(workingEnv.kernelEnv))),
          "suggestions" -> Json.Arr(sugs.map(_.toJson))
        )
      )
    } else {
      state.buildProofTerm match {
        case Left(err) => Left(("RPC006", err))
        case Right(proofTerm) =>
          TypeChecker.checkDef(
            workingEnv.kernelEnv,
            theoremName,
            goalType,
            proofTerm,
            transparent = false,
            isTheorem = true
          ) match {
            case Left(kErr) =>
              Left((kErr.code, s"Kernel rejected proof: ${kErr.message}"))
            case Right(verifiedKernel) =>
              currentEnv = workingEnv.copy(kernelEnv = verifiedKernel)
              val defEntry = verifiedKernel.defs(theoremName)
              Right(
                Json.obj(
                  "verified" -> Json.Bool(true),
                  "kernelVerified" -> Json.Bool(true),
                  "theoremName" -> Json.Str(theoremName),
                  "axiomsUsed" -> Json.Arr(defEntry.axiomsUsed.toList.sorted.map(Json.Str(_))),
                  "isAxiomFree" -> Json.Bool(defEntry.axiomsUsed.isEmpty),
                  "proofTerm" -> Json.Str(Pretty.show(proofTerm))
                )
              )
          }
      }
    }
  }

  private def handleListSymbols(): Json = {
    val kEnv = currentEnv.kernelEnv
    val inds = kEnv.inductives.values.toList.sortBy(_.name).map { ind =>
      Json.obj(
        "name" -> Json.Str(ind.name),
        "sort" -> Json.Str(ind.sort.toString),
        "type" -> Json.Str(Pretty.show(ind.fullType)),
        "constructors" -> Json.Arr(ind.constructors.map { c =>
          Json.obj("name" -> Json.Str(c.name), "type" -> Json.Str(Pretty.show(ind.ctorType(c))))
        })
      )
    }
    val fns = kEnv.defs.values.filterNot(_.isTheorem).toList.sortBy(_.name).map { d =>
      Json.obj("name" -> Json.Str(d.name), "type" -> Json.Str(Pretty.show(d.ty)))
    }
    val thms = kEnv.defs.values.filter(_.isTheorem).toList.sortBy(_.name).map { d =>
      Json.obj(
        "name" -> Json.Str(d.name),
        "type" -> Json.Str(Pretty.show(d.ty)),
        "isSimp" -> Json.Bool(currentEnv.simpLemmas.contains(d.name)),
        "isAxiomFree" -> Json.Bool(d.axiomsUsed.isEmpty)
      )
    }
    Json.obj(
      "inductives" -> Json.Arr(inds),
      "functions" -> Json.Arr(fns),
      "theorems" -> Json.Arr(thms),
      "simpLemmas" -> Json.Arr(currentEnv.simpLemmas.distinct.sorted.map(Json.Str(_)))
    )
  }

  private def handleInspectHoles(params: Json): Either[(String, String), Json] = {
    val fileName = params.field("file").flatMap(_.asString).getOrElse("<inspect>")
    val source = params.field("source").flatMap(_.asString).getOrElse("")
    // Resilient whole-file hole collection mode!
    val envBefore = currentEnv.copy(holes = Nil, holeCollectionMode = true)
    Elaborator.checkSource(fileName, source, envBefore) match {
      case Right(nextEnv) =>
        val holesJson = nextEnv.holes.map { h =>
          val goal = ProofGoal(0, h.name.getOrElse("hole"), h.localCtx, h.expectedType)
          val sugs = ProofSearch.suggest(nextEnv, goal)
          val relevant = ProofSearch.searchMatchingLemmas(nextEnv, goal, limit = 5).map { case (n, t) =>
            Json.obj("name" -> Json.Str(n), "type" -> Json.Str(t))
          }
          Json.obj(
            "hole" -> h.toJson(nextEnv.kernelEnv),
            "goalShape" -> Json.Str(goal.goalShape(nextEnv.kernelEnv)),
            "suggestions" -> Json.Arr(sugs.map(_.toJson)),
            "relevantLemmas" -> Json.Arr(relevant)
          )
        }
        Right(Json.obj("holeCount" -> Json.Num(holesJson.length), "holes" -> Json.Arr(holesJson)))
      case Left(diag) =>
        Left((diag.code, diag.formatHuman(Some(source))))
    }
  }

  private def handleSuggest(params: Json): Either[(String, String), Json] = {
    val stateId = params.field("stateId").flatMap(_.asInt).getOrElse(-1)
    proofNodes.get(stateId) match {
      case None => Left(("RPC004", s"Unknown proof stateId: $stateId"))
      case Some(node) =>
        val suggestions = node.proofState.currentGoal.map(ProofSearch.suggest(currentEnv, _)).getOrElse(Nil)
        Right(
          Json.obj(
            "stateId" -> Json.Num(stateId),
            "suggestions" -> Json.Arr(suggestions.map(_.toJson))
          )
        )
    }
  }

  private def handleSearchLemmas(params: Json): Either[(String, String), Json] = {
    val query = params.field("query").flatMap(_.asString)
    val stateIdOpt = params.field("stateId").flatMap(_.asInt)
    val limit = params.field("limit").flatMap(_.asInt).getOrElse(15)

    val results: List[(String, String)] = stateIdOpt match {
      case Some(sid) =>
        proofNodes.get(sid).flatMap(_.proofState.currentGoal) match {
          case Some(goal) => ProofSearch.searchMatchingLemmas(currentEnv, goal, limit)
          case None       => Nil
        }
      case None =>
        val qLower = query.getOrElse("").toLowerCase
        currentEnv.kernelEnv.defs.toList
          .collect {
            case (name, entry)
                if qLower.isEmpty || name.toLowerCase.contains(qLower) || Pretty.show(entry.ty).toLowerCase.contains(qLower) =>
              (name, Pretty.show(entry.ty))
          }
          .take(limit)
    }

    Right(
      Json.obj(
        "matches" -> Json.Arr(
          results.map { case (n, t) => Json.obj("name" -> Json.Str(n), "type" -> Json.Str(t)) }
        )
      )
    )
  }

  private def handleExtract(params: Json): Either[(String, String), Json] = {
    val target = params.field("target").flatMap(_.asString).getOrElse("scala3").toLowerCase
    val moduleName = params.field("moduleName").flatMap(_.asString).getOrElse("ExtractedSamurai")
    val requireAxiomFree = params.field("requireAxiomFree").flatMap(_.asBool).getOrElse(false)
    val requireTotal = params.field("requireTotal").flatMap(_.asBool).getOrElse(false)

    Erasure.extract(currentEnv, Erasure.ExtractionOptions(moduleName, requireAxiomFree, requireTotal)) match {
      case Left(err) => Left(("EXT001", err))
      case Right(module) =>
        val code = target match {
          case "ts" | "typescript" => TsEmitter.emit(module)
          case "js" | "javascript" => JsEmitter.emit(module)
          case "hs" | "haskell"    => HaskellEmitter.emit(module)
          case "ml" | "ocaml"      => OCamlEmitter.emit(module)
          case _                   => Scala3Emitter.emit(module)
        }
        Right(
          Json.obj(
            "target" -> Json.Str(target),
            "code" -> Json.Str(code),
            "manifest" -> module.manifest.toJson
          )
        )
    }
  }

  private def handleEnvSummary(): Json = {
    val kEnv = currentEnv.kernelEnv
    Json.obj(
      "inductives" -> Json.Arr(kEnv.inductives.keys.toList.sorted.map(Json.Str(_))),
      "definitions" -> Json.Arr(kEnv.defs.values.filterNot(_.isTheorem).map(_.name).toList.sorted.map(Json.Str(_))),
      "theorems" -> Json.Arr(kEnv.defs.values.filter(_.isTheorem).map(_.name).toList.sorted.map(Json.Str(_))),
      "axiomsUsed" -> Json.Arr(kEnv.allAxiomsUsed.toList.sorted.map(Json.Str(_))),
      "isAxiomFree" -> Json.Bool(kEnv.allAxiomsUsed.isEmpty)
    )
  }
}

object ProofSessionServer {
  /** Run NDJSON (one JSON request per line) server on stdin/stdout for AI agent integration. */
  def runStdio(searchPaths: List[Path]): Unit = {
    val session = new ProofSession(searchPaths)
    val reader = new BufferedReader(new InputStreamReader(System.in))
    val writer = new PrintWriter(System.out, true)
    var line = reader.readLine()
    while (line != null) {
      val trimmed = line.trim
      if (trimmed.nonEmpty) {
        val response = Json.parse(trimmed) match {
          case Left(parseErr) =>
            Json.obj(
              "ok" -> Json.Bool(false),
              "error" -> Json.obj("code" -> Json.Str("JSON001"), "message" -> Json.Str(parseErr))
            )
          case Right(reqJson) =>
            session.handleRequest(reqJson)
        }
        writer.println(response.compact)
      }
      line = reader.readLine()
    }
  }
}
