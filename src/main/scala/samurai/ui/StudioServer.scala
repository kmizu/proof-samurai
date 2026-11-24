package samurai.ui

import com.sun.net.httpserver.{HttpExchange, HttpServer}
import java.net.InetSocketAddress
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}
import java.util.UUID
import java.util.concurrent.{ConcurrentHashMap, Executors}
import samurai.ai.ProofSession
import samurai.elab.{ElabEnv, Elaborator}
import samurai.extract.{Erasure, HaskellEmitter, JsEmitter, OCamlEmitter, Scala3Emitter, TsEmitter}
import samurai.kernel.Pretty
import samurai.tactic.{ProofGoal, ProofSearch}
import samurai.util.Json

/**
 * Zero-dependency embedded HTTP server powering **Proof Samurai Studio** —
 * an interactive Web IDE, Live Proof Tree Stepper, Code Extractor, and Docs Hub
 * for both humans and AI-assisted workflows.
 */
final class StudioServer private (
  private val httpServer: HttpServer,
  val port: Int
) {
  def url: String = s"http://localhost:$port"

  def stop(): Unit = {
    httpServer.stop(0)
  }
}

object StudioServer {

  private final case class CuratedItem(
    id: String,
    title: String,
    category: String,
    description: String,
    path: Path
  )

  def start(
    port: Int = 8080,
    searchPaths: List[Path] = List(Paths.get("."), Paths.get("stdlib"))
  ): StudioServer = {
    val server = HttpServer.create(new InetSocketAddress("127.0.0.1", port), 0)
    val actualPort = server.getAddress.getPort
    val sessions = new ConcurrentHashMap[String, ProofSession]()

    def getOrCreateSession(sessionIdOpt: Option[String]): (String, ProofSession) = {
      sessionIdOpt match {
        case Some(existingId) =>
          val existing = sessions.get(existingId)
          if (existing != null) (existingId, existing)
          else {
            val fresh = new ProofSession(searchPaths)
            sessions.put(existingId, fresh)
            (existingId, fresh)
          }
        case None =>
          val freshId = UUID.randomUUID().toString
          val fresh = new ProofSession(searchPaths)
          sessions.put(freshId, fresh)
          (freshId, fresh)
      }
    }

    // Static UI assets
    server.createContext(
      "/",
      exchange => {
        val reqPath = exchange.getRequestURI.getPath
        val resourcePath = reqPath match {
          case "/" | "/index.html" => "/studio/index.html"
          case "/styles.css"       => "/studio/styles.css"
          case "/app.js"           => "/studio/app.js"
          case "/favicon.svg"      => "/studio/favicon.svg"
          case _                   => ""
        }
        if (resourcePath.isEmpty) {
          sendText(exchange, 404, "text/plain; charset=utf-8", "Not found")
        } else {
          val stream = getClass.getResourceAsStream(resourcePath)
          if (stream == null) {
            sendText(exchange, 404, "text/plain; charset=utf-8", s"Missing studio asset: $resourcePath")
          } else {
            val bytes = try stream.readAllBytes() finally stream.close()
            val contentType =
              if (resourcePath.endsWith(".html")) "text/html; charset=utf-8"
              else if (resourcePath.endsWith(".css")) "text/css; charset=utf-8"
              else if (resourcePath.endsWith(".svg")) "image/svg+xml; charset=utf-8"
              else "application/javascript; charset=utf-8"
            sendBytes(exchange, 200, contentType, bytes)
          }
        }
      }
    )

    // GET /api/examples — curated examples & stdlib files
    server.createContext(
      "/api/examples",
      exchange => {
        if (exchange.getRequestMethod != "GET") {
          sendJson(exchange, 405, Json.obj("ok" -> Json.Bool(false), "error" -> Json.Str("Use GET")))
        } else {
          val items = discoverCuratedFiles()
          val jsonItems = items.map { item =>
            val code = if (Files.exists(item.path)) Files.readString(item.path) else ""
            Json.obj(
              "id" -> Json.Str(item.id),
              "title" -> Json.Str(item.title),
              "category" -> Json.Str(item.category),
              "description" -> Json.Str(item.description),
              "path" -> Json.Str(item.path.toString.replace('\\', '/')),
              "code" -> Json.Str(code)
            )
          }
          sendJson(exchange, 200, Json.obj("ok" -> Json.Bool(true), "examples" -> Json.Arr(jsonItems)))
        }
      }
    )

    // POST /api/check — check source code + collect holes + diagnostics + symbols
    server.createContext(
      "/api/check",
      exchange => {
        readJsonBody(exchange) match {
          case Left(err) => sendJson(exchange, 400, Json.obj("ok" -> Json.Bool(false), "error" -> Json.Str(err)))
          case Right(body) =>
            val fileName = body.field("file").flatMap(_.asString).getOrElse("Playground.samurai")
            val source = body.field("source").flatMap(_.asString).getOrElse("")
            val inspectHolesMode = body.field("collectHoles").flatMap(_.asBool).getOrElse(true)
            val started = System.nanoTime()

            val initEnv = ElabEnv(searchPaths = searchPaths, holeCollectionMode = inspectHolesMode)
            val res = Elaborator.checkSource(fileName, source, initEnv)
            val elapsedMs = (System.nanoTime() - started) / 1_000_000L

            res match {
              case Left(diag) =>
                sendJson(
                  exchange,
                  200,
                  Json.obj(
                    "ok" -> Json.Bool(false),
                    "elapsedMs" -> Json.Num(elapsedMs.toDouble),
                    "diagnostics" -> Json.Arr(List(diag.toJson)),
                    "formattedError" -> Json.Str(diag.formatHuman(Some(source))),
                    "kindHint" -> Json.Str(friendlyErrorExplanation(diag.code))
                  )
                )

              case Right(env) =>
                val kEnv = env.kernelEnv
                val axioms = kEnv.allAxiomsUsed
                val hasHoles = env.holes.nonEmpty
                val holesJson = env.holes.zipWithIndex.map { case (h, idx) =>
                  val goal = ProofGoal(idx, h.name.getOrElse(s"hole_$idx"), h.localCtx, h.expectedType)
                  val sugs = ProofSearch.suggest(env, goal)
                  val relevant = ProofSearch.searchMatchingLemmas(env, goal, limit = 5).map { case (n, t) =>
                    Json.obj("name" -> Json.Str(n), "type" -> Json.Str(t))
                  }
                  Json.obj(
                    "hole" -> h.toJson(kEnv),
                    "goalShape" -> Json.Str(goal.goalShape(kEnv)),
                    "formattedGoal" -> Json.Str(goal.formatHuman(kEnv)),
                    "suggestions" -> Json.Arr(sugs.map(_.toJson)),
                    "relevantLemmas" -> Json.Arr(relevant)
                  )
                }

                val inds = kEnv.inductives.values.toList.sortBy(_.name).map { ind =>
                  Json.obj(
                    "name" -> Json.Str(ind.name),
                    "kind" -> Json.Str("enum"),
                    "sort" -> Json.Str(ind.sort.toString),
                    "type" -> Json.Str(Pretty.show(ind.fullType))
                  )
                }
                val defs = kEnv.defs.values.toList.sortBy(_.name).map { d =>
                  Json.obj(
                    "name" -> Json.Str(d.name),
                    "kind" -> Json.Str(if (d.isTheorem) "theorem" else "def"),
                    "type" -> Json.Str(Pretty.show(d.ty)),
                    "isSimp" -> Json.Bool(env.simpLemmas.contains(d.name)),
                    "isAxiomFree" -> Json.Bool(d.axiomsUsed.isEmpty)
                  )
                }

                sendJson(
                  exchange,
                  200,
                  Json.obj(
                    "ok" -> Json.Bool(!hasHoles),
                    "hasHoles" -> Json.Bool(hasHoles),
                    "elapsedMs" -> Json.Num(elapsedMs.toDouble),
                    "stats" -> Json.obj(
                      "inductives" -> Json.Num(kEnv.inductives.size),
                      "functions" -> Json.Num(kEnv.defs.values.count(!_.isTheorem)),
                      "theorems" -> Json.Num(kEnv.defs.values.count(_.isTheorem))
                    ),
                    "axiomsUsed" -> Json.Arr(axioms.toList.sorted.map(Json.Str(_))),
                    "isAxiomFree" -> Json.Bool(axioms.isEmpty && !hasHoles),
                    "directives" -> Json.Arr(env.directives.map(_.toJson)),
                    "holes" -> Json.Arr(holesJson),
                    "symbols" -> Json.Arr(inds ++ defs)
                  )
                )
            }
        }
      }
    )

    // POST /api/extract — extract verified code to scala3 | ts | js
    server.createContext(
      "/api/extract",
      exchange => {
        readJsonBody(exchange) match {
          case Left(err) => sendJson(exchange, 400, Json.obj("ok" -> Json.Bool(false), "error" -> Json.Str(err)))
          case Right(body) =>
            val source = body.field("source").flatMap(_.asString).getOrElse("")
            val target = body.field("target").flatMap(_.asString).getOrElse("scala3").toLowerCase
            val moduleName = body.field("moduleName").flatMap(_.asString).getOrElse("ExtractedSamurai")
            val strict = body.field("strict").flatMap(_.asBool).getOrElse(false)

            Elaborator.checkSource("Extract.samurai", source, ElabEnv(searchPaths = searchPaths)) match {
              case Left(diag) =>
                sendJson(
                  exchange,
                  200,
                  Json.obj(
                    "ok" -> Json.Bool(false),
                    "error" -> Json.Str(diag.formatHuman(Some(source)))
                  )
                )
              case Right(env) =>
                Erasure.extract(env, Erasure.ExtractionOptions(moduleName, requireAxiomFree = strict)) match {
                  case Left(err) =>
                    sendJson(exchange, 200, Json.obj("ok" -> Json.Bool(false), "error" -> Json.Str(err)))
                  case Right(module) =>
                    val code = target match {
                      case "ts" | "typescript" => TsEmitter.emit(module)
                      case "js" | "javascript" => JsEmitter.emit(module)
                      case "hs" | "haskell"    => HaskellEmitter.emit(module)
                      case "ml" | "ocaml"      => OCamlEmitter.emit(module)
                      case _                   => Scala3Emitter.emit(module)
                    }
                    sendJson(
                      exchange,
                      200,
                      Json.obj(
                        "ok" -> Json.Bool(true),
                        "target" -> Json.Str(target),
                        "code" -> Json.Str(code),
                        "manifest" -> module.manifest.toJson
                      )
                    )
                }
            }
        }
      }
    )

    // POST /api/proof — interactive branching proof session proxy (reuses ProofSession!)
    server.createContext(
      "/api/proof",
      exchange => {
        readJsonBody(exchange) match {
          case Left(err) => sendJson(exchange, 400, Json.obj("ok" -> Json.Bool(false), "error" -> Json.Str(err)))
          case Right(body) =>
            val sessionIdOpt = body.field("sessionId").flatMap(_.asString)
            val (sessionId, session) = getOrCreateSession(sessionIdOpt)
            val method = body.field("method").flatMap(_.asString).getOrElse("")
            val params = body.field("params").getOrElse(Json.obj())

            val response = session.synchronized {
              // Ensure Prelude + Nat + List are loaded for brand-new interactive prover sessions on startProof
              if (method == "startProof" && session.environment.kernelEnv.inductives.isEmpty) {
                session.handleRequest(
                  Json.obj(
                    "id" -> Json.Num(0),
                    "method" -> Json.Str("loadSource"),
                    "params" -> Json.obj("source" -> Json.Str("import Prelude.*\nimport Nat.*\nimport List.*"))
                  )
                )
              }
              session.handleRequest(
                Json.obj("id" -> Json.Num(1), "method" -> Json.Str(method), "params" -> params)
              )
            }
            sendJson(exchange, 200, Json.obj("sessionId" -> Json.Str(sessionId), "rpc" -> response))
        }
      }
    )

    // GET /api/docs?lang=en|ja — serve markdown docs from docs/ or docs/ja/
    server.createContext(
      "/api/docs",
      exchange => {
        val query = Option(exchange.getRequestURI.getQuery).getOrElse("")
        val isJapanese = query.split("&").exists(param => param == "lang=ja")
        val docFiles =
          if (isJapanese) {
            List(
              ("getting-started", "01 はじめに", "docs/ja/GETTING_STARTED.md"),
              ("proofs-for-programmers", "02 証明・タクティクと通常コードの関係", "docs/ja/PROOFS_FOR_PROGRAMMERS.md"),
              ("language", "03 言語リファレンス", "docs/ja/LANGUAGE.md"),
              ("tactics", "04 タクティク・クックブック", "docs/ja/TACTICS_COOKBOOK.md"),
              ("extraction", "05 検証済みコード抽出", "docs/ja/EXTRACTION.md"),
              ("troubleshooting", "06 カーネル・型エラー解決ガイド", "docs/ja/TROUBLESHOOTING.md"),
              ("kernel", "07 信頼カーネルのアーキテクチャ", "docs/ja/KERNEL.md"),
              ("ai-guide", "08 AI エージェント連携ガイド", "docs/ja/AI_AGENT_GUIDE.md"),
              ("ai-protocol", "09 JSON-RPC プロトコル仕様", "docs/ja/AI_PROTOCOL.md")
            )
          } else {
            List(
              ("getting-started", "01 Getting Started", "docs/GETTING_STARTED.md"),
              ("proofs-for-programmers", "02 Proofs, Tactics & Ordinary Code", "docs/PROOFS_FOR_PROGRAMMERS.md"),
              ("language", "03 Language Reference", "docs/LANGUAGE.md"),
              ("tactics", "04 Tactic Cookbook", "docs/TACTICS_COOKBOOK.md"),
              ("extraction", "05 Verified Code Extraction", "docs/EXTRACTION.md"),
              ("troubleshooting", "06 Kernel & Type Error Guide", "docs/TROUBLESHOOTING.md"),
              ("kernel", "07 Trusted Kernel Architecture", "docs/KERNEL.md"),
              ("ai-guide", "08 AI Agent Guide", "docs/AI_AGENT_GUIDE.md"),
              ("ai-protocol", "09 JSON-RPC Protocol Reference", "docs/AI_PROTOCOL.md")
            )
          }
        val loaded = docFiles.flatMap { case (id, title, relPath) =>
          val p = Paths.get(relPath)
          if (Files.exists(p)) {
            Some(
              Json.obj(
                "id" -> Json.Str(id),
                "title" -> Json.Str(title),
                "path" -> Json.Str(relPath),
                "markdown" -> Json.Str(Files.readString(p))
              )
            )
          } else None
        }
        sendJson(
          exchange,
          200,
          Json.obj(
            "ok" -> Json.Bool(true),
            "lang" -> Json.Str(if (isJapanese) "ja" else "en"),
            "docs" -> Json.Arr(loaded)
          )
        )
      }
    )

    server.setExecutor(Executors.newCachedThreadPool())
    server.start()
    new StudioServer(server, actualPort)
  }

  private def discoverCuratedFiles(): List[CuratedItem] = {
    val candidates = List(
      CuratedItem("showcase", "Showcase: calc, arith, Queue & Sort", "Examples", "Tour of list literals, calc blocks, one-word arith, and verified Queue.", Paths.get("examples/Showcase.samurai")),
      CuratedItem("practical-proving", "Practical Proving: omega, cc, tauto & <;>", "Examples", "Linear arithmetic (omega), congruence closure (cc), intuitionistic tauto, and combinators.", Paths.get("examples/PracticalProving.samurai")),
      CuratedItem("advanced-recursion", "Mutual, Well-Founded (div/gcd/quickSort) & partial def", "Examples", "Mutual structural recursion, fuel-free termination_by, and sound isolated partial def.", Paths.get("examples/AdvancedRecursion.samurai")),
      CuratedItem("hello", "Hello Proof (Gentle Intro)", "Examples", "Your first inductive proofs, automation, and #eval.", Paths.get("examples/HelloProof.samurai")),
      CuratedItem("verified-sort", "Verified Insertion Sort", "Examples", "Running insertion sort with full sortedness & permutation proofs.", Paths.get("examples/VerifiedSort.samurai")),
      CuratedItem("safe-vec", "Safe Length-Indexed Vectors", "Examples", "Total vecHead without Option or null — unreachable Nil discharged.", Paths.get("examples/SafeVec.samurai")),
      CuratedItem("stdlib-wellfounded", "stdlib/WellFounded.samurai", "Stdlib", "0-axiom Acc, natWf, strong induction, divNat, modNat, gcd, and quickSort.", Paths.get("stdlib/WellFounded.samurai")),
      CuratedItem("stdlib-sorting", "stdlib/Sorting.samurai", "Stdlib", "Full insertion sort correctness (Sorted + count permutation + length).", Paths.get("stdlib/Sorting.samurai")),
      CuratedItem("stdlib-queue", "stdlib/Queue.samurai", "Stdlib", "Verified amortized two-stack functional Queue.", Paths.get("stdlib/Queue.samurai")),
      CuratedItem("stdlib-tree", "stdlib/Tree.samurai", "Stdlib", "Verified binary trees with dual induction hypotheses.", Paths.get("stdlib/Tree.samurai")),
      CuratedItem("stdlib-nat", "stdlib/Nat.samurai", "Stdlib", "Natural numbers, arithmetic semiring laws, and ordering.", Paths.get("stdlib/Nat.samurai")),
      CuratedItem("stdlib-list", "stdlib/List.samurai", "Stdlib", "Polymorphic lists, reverseReverse, mapFusion, and length laws.", Paths.get("stdlib/List.samurai")),
      CuratedItem("stdlib-option", "stdlib/Option.samurai", "Stdlib", "Verified Option functor and monad laws.", Paths.get("stdlib/Option.samurai")),
      CuratedItem("stdlib-vec", "stdlib/Vec.samurai", "Stdlib", "Length-indexed dependent vectors.", Paths.get("stdlib/Vec.samurai")),
      CuratedItem("stdlib-prelude", "stdlib/Prelude.samurai", "Stdlib", "Core logic (Prop, Eq, And, Or, Exists, Subset, Pair, Bool).", Paths.get("stdlib/Prelude.samurai"))
    )
    candidates.filter(c => Files.exists(c.path))
  }

  private def friendlyErrorExplanation(code: String): String = code match {
    case "K005" => "Universe safety: a Type0 data type cannot store Type0 types inside itself. Try declaring the enum as `: Type1`."
    case "K006" => "Positivity safety: an inductive type cannot appear to the left of `=>` in its own constructor (this prevents Curry's paradox)."
    case "K020" => "Termination safety: recursive functions must pass a strictly smaller pattern-matched subterm on each recursive call (e.g. `pred` from `case Nat.Succ(pred)`)."
    case "K025" => "Proof erasure safety: `Prop` types with multiple constructors (`Or`, `Exists`) cannot produce computational `Type` values. Use `Subset` or `Either` for computational witnesses."
    case "K026" | "E071" => "Exhaustiveness safety: every constructor of the matched enum must be handled (or add a `case _ => ...` fallback)."
    case "K030" => "Partial soundness: `partial def` cannot return a `Prop` type and theorems cannot be marked `partial`."
    case "K031" => "Total/partial isolation: total definitions and theorems cannot call `partial def` functions. Use `termination_by { ... }` for kernel-verified well-founded recursion."
    case "E042" | "K011" => "Type mismatch: check the expected vs found types above. For equalities, try `simp`, `arith`, or `rewrite(...)`."
    case "T010" => "Reflexivity (`refl`) only closes goals that are already equal by computation. Try `simp`, `arith`, or `rewrite(...)` first."
    case "T015" => "Rewrite pattern not found in the goal: check whether `simp` needs to unfold a definition first, or try `rewriteRev(...)` for the opposite direction."
    case "E020" => "Some proof goals remain open — inspect the remaining goal(s) or place `?todo` to see tailored tactic suggestions."
    case _ => "Tip: You can replace an unfinished proof step with `?help` to inspect the exact hypotheses, goal type, and suggested tactics."
  }

  private def readJsonBody(exchange: HttpExchange): Either[String, Json] = {
    val raw = new String(exchange.getRequestBody.readAllBytes(), StandardCharsets.UTF_8)
    if (raw.trim.isEmpty) Right(Json.obj())
    else Json.parse(raw)
  }

  private def sendJson(exchange: HttpExchange, status: Int, json: Json): Unit =
    sendText(exchange, status, "application/json; charset=utf-8", json.compact)

  private def sendText(exchange: HttpExchange, status: Int, contentType: String, text: String): Unit =
    sendBytes(exchange, status, contentType, text.getBytes(StandardCharsets.UTF_8))

  private def sendBytes(exchange: HttpExchange, status: Int, contentType: String, bytes: Array[Byte]): Unit = {
    exchange.getResponseHeaders.set("Content-Type", contentType)
    exchange.getResponseHeaders.set("Cache-Control", "no-store")
    exchange.sendResponseHeaders(status, bytes.length.toLong)
    val out = exchange.getResponseBody
    try out.write(bytes)
    finally out.close()
  }
}
