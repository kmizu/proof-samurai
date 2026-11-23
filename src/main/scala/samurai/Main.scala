package samurai

import java.nio.file.{Files, Path, Paths}
import samurai.ai.{ProofSessionServer, Repl}
import samurai.elab.{ElabEnv, Elaborator}
import samurai.extract.{Erasure, JsEmitter, Scala3Emitter, TsEmitter}
import samurai.kernel.Pretty
import samurai.tactic.{ProofGoal, ProofSearch}
import samurai.ui.StudioServer
import samurai.util.Json

/**
 * CLI entrypoint for Proof Samurai (`samurai`).
 *
 * Usage:
 *   samurai check <file> [--strict] [--json]
 *   samurai extract <file> [--target scala3|ts] [--module Name] [--out <path>] [--strict] [--json]
 *   samurai serve
 *   samurai repl
 */
object Main {

  private val DefaultSearchPaths: List[Path] = List(Paths.get("."), Paths.get("stdlib"))

  def main(args: Array[String]): Unit = {
    if (args.isEmpty) {
      printUsage()
      return
    }

    args(0) match {
      case "check"          => runCheck(args.drop(1))
      case "goals"          => runGoals(args.drop(1))
      case "verify-project" => runVerifyProject(args.drop(1))
      case "extract"        => runExtract(args.drop(1))
      case "search"         => runSearch(args.drop(1))
      case "studio" | "ui"  => runStudio(args.drop(1))
      case "serve"          => ProofSessionServer.runStdio(DefaultSearchPaths)
      case "repl"           => Repl.run(DefaultSearchPaths)
      case "--help" | "-h" | "help" => printUsage()
      case other =>
        System.err.println(s"Unknown command '$other'")
        printUsage()
        sys.exit(1)
    }
  }

  private def printUsage(): Unit = {
    println(
      """Proof Samurai v0.1.0 — Pragmatic, Readable, AI-Friendly Dependently-Typed Proof Assistant
        |
        |Usage:
        |  samurai studio [--port 8080]   Launch Proof Samurai Studio (Interactive Web IDE & Docs Hub)
        |  samurai check <file.samurai> [--strict] [--json]
        |  samurai goals <file.samurai> [--json]
        |  samurai verify-project [dir] [--strict] [--json]
        |  samurai extract <file.samurai> [--target scala3|ts|js] [--module Name] [--out <path>] [--strict] [--json]
        |  samurai search <file.samurai> <query> [--json]
        |  samurai serve                  Start AI-native NDJSON interactive proof server (stdin/stdout)
        |  samurai repl                   Start interactive multi-line human REPL
        |""".stripMargin
    )
  }

  private def runStudio(args: Array[String]): Unit = {
    val port = {
      val idx = args.indexOf("--port")
      if (idx >= 0 && idx + 1 < args.length) args(idx + 1).toIntOption.getOrElse(8080)
      else 8080
    }
    val server = StudioServer.start(port, DefaultSearchPaths)
    println("==================================================================")
    println(s"  Proof Samurai Studio is running at: ${server.url}")
    println("  Features: Live Kernel Infoview | Interactive Proof Tree | Code Extractor | Kindful Docs")
    println("  Press Ctrl+C to stop.")
    println("==================================================================")
    Runtime.getRuntime.addShutdownHook(new Thread(() => server.stop()))
    Thread.currentThread().join()
  }

  private def runCheck(args: Array[String]): Unit = {
    val jsonMode = args.contains("--json")
    val strictMode = args.contains("--strict")
    val fileOpt = args.find(a => !a.startsWith("--"))

    val filePath = fileOpt match {
      case Some(f) => Paths.get(f)
      case None =>
        System.err.println("Error: 'check' requires a source file path")
        sys.exit(1)
    }

    val sourceOpt = if (Files.exists(filePath)) Some(Files.readString(filePath)) else None
    val initialEnv = ElabEnv(searchPaths = DefaultSearchPaths)

    Elaborator.checkFile(filePath, initialEnv) match {
      case Left(diag) =>
        if (jsonMode) {
          println(Json.obj("ok" -> Json.Bool(false), "diagnostics" -> Json.Arr(List(diag.toJson))).pretty)
        } else {
          System.err.print(diag.formatHuman(sourceOpt))
        }
        sys.exit(1)

      case Right(env) =>
        val axioms = env.kernelEnv.allAxiomsUsed
        val strictFailed = strictMode && axioms.nonEmpty
        val theoremsCount = env.kernelEnv.defs.values.count(_.isTheorem)
        val defsCount = env.kernelEnv.defs.values.count(!_.isTheorem)
        val indsCount = env.kernelEnv.inductives.size

        if (jsonMode) {
          val out = Json.obj(
            "ok" -> Json.Bool(!strictFailed),
            "file" -> Json.Str(filePath.toString),
            "inductives" -> Json.Num(indsCount),
            "functions" -> Json.Num(defsCount),
            "theorems" -> Json.Num(theoremsCount),
            "axiomsUsed" -> Json.Arr(axioms.toList.sorted.map(Json.Str(_))),
            "isAxiomFree" -> Json.Bool(axioms.isEmpty),
            "directives" -> Json.Arr(env.directives.map(_.toJson)),
            "holes" -> Json.Arr(env.holes.map(_.toJson(env.kernelEnv)))
          )
          println(out.pretty)
        } else {
          env.directives.foreach(d => println(s"[#${d.directive}] ${d.output}"))
          if (strictFailed) {
            System.err.println(
              s"STRICT CHECK FAILED: '${filePath}' uses axiom(s): ${axioms.toList.sorted.mkString(", ")}"
            )
          } else {
            val trustMsg =
              if (axioms.isEmpty) "100% axiom-free"
              else s"uses axiom(s): ${axioms.toList.sorted.mkString(", ")}"
            println(
              s"OK: Verified '$filePath' ($indsCount types, $defsCount functions, $theoremsCount theorems; $trustMsg)"
            )
          }
        }
        if (strictFailed) sys.exit(1)
    }
  }

  private def runExtract(args: Array[String]): Unit = {
    val jsonMode = args.contains("--json")
    val strictMode = args.contains("--strict")

    def flagValue(flag: String): Option[String] = {
      val idx = args.indexOf(flag)
      if (idx >= 0 && idx + 1 < args.length) Some(args(idx + 1)) else None
    }

    val target = flagValue("--target").getOrElse("scala3").toLowerCase
    val moduleName = flagValue("--module").getOrElse("ExtractedSamurai")
    val outPathOpt = flagValue("--out").map(Paths.get(_))

    // Positional file argument (skip flag values)
    val flagValIndices = Set("--target", "--module", "--out").flatMap { fl =>
      val idx = args.indexOf(fl)
      if (idx >= 0) Set(idx, idx + 1) else Set.empty[Int]
    }
    val fileOpt = args.zipWithIndex.collectFirst {
      case (arg, i) if !arg.startsWith("--") && !flagValIndices.contains(i) => arg
    }

    val filePath = fileOpt match {
      case Some(f) => Paths.get(f)
      case None =>
        System.err.println("Error: 'extract' requires a source file path")
        sys.exit(1)
    }

    val sourceOpt = if (Files.exists(filePath)) Some(Files.readString(filePath)) else None
    val initialEnv = ElabEnv(searchPaths = DefaultSearchPaths)

    Elaborator.checkFile(filePath, initialEnv) match {
      case Left(diag) =>
        if (jsonMode) {
          println(Json.obj("ok" -> Json.Bool(false), "diagnostics" -> Json.Arr(List(diag.toJson))).pretty)
        } else {
          System.err.print(diag.formatHuman(sourceOpt))
        }
        sys.exit(1)

      case Right(env) =>
        Erasure.extract(env, Erasure.ExtractionOptions(moduleName, requireAxiomFree = strictMode)) match {
          case Left(err) =>
            if (jsonMode) {
              println(Json.obj("ok" -> Json.Bool(false), "error" -> Json.Str(err)).pretty)
            } else {
              System.err.println(s"Extraction error: $err")
            }
            sys.exit(1)

          case Right(module) =>
            val code = target match {
              case "ts" | "typescript" => TsEmitter.emit(module)
              case "js" | "javascript" => JsEmitter.emit(module)
              case _                   => Scala3Emitter.emit(module)
            }
            outPathOpt match {
              case Some(outPath) =>
                Option(outPath.toAbsolutePath.getParent).foreach(Files.createDirectories(_))
                Files.writeString(outPath, code)
                if (jsonMode) {
                  println(Json.obj("ok" -> Json.Bool(true), "outputPath" -> Json.Str(outPath.toString), "manifest" -> module.manifest.toJson).pretty)
                } else {
                  println(s"Extracted verified $target code to '$outPath' (axiom-free: ${module.manifest.isAxiomFree})")
                }
              case None =>
                if (jsonMode) {
                  println(Json.obj("ok" -> Json.Bool(true), "target" -> Json.Str(target), "code" -> Json.Str(code), "manifest" -> module.manifest.toJson).pretty)
                } else {
                  print(code)
                }
            }
        }
    }
  }

  private def runSearch(args: Array[String]): Unit = {
    val jsonMode = args.contains("--json")
    val positional = args.filterNot(_.startsWith("--"))
    if (positional.length < 2) {
      System.err.println("Error: 'search' requires <file.samurai> and <query>")
      sys.exit(1)
    }
    val filePath = Paths.get(positional(0))
    val query = positional(1).toLowerCase
    val initialEnv = ElabEnv(searchPaths = DefaultSearchPaths)

    Elaborator.checkFile(filePath, initialEnv) match {
      case Left(diag) =>
        System.err.print(diag.formatHuman())
        sys.exit(1)
      case Right(env) =>
        val matches = env.kernelEnv.defs.toList.collect {
          case (name, entry)
              if name.toLowerCase.contains(query) || Pretty.show(entry.ty).toLowerCase.contains(query) =>
            (name, if (entry.isTheorem) "theorem" else "def", Pretty.show(entry.ty))
        }.sortBy(_._1)

        if (jsonMode) {
          val items = matches.map { case (n, kind, ty) =>
            Json.obj("name" -> Json.Str(n), "kind" -> Json.Str(kind), "type" -> Json.Str(ty))
          }
          println(Json.obj("ok" -> Json.Bool(true), "query" -> Json.Str(positional(1)), "matches" -> Json.Arr(items)).pretty)
        } else {
          for ((name, kind, ty) <- matches) {
            println(s"$kind $name : $ty")
          }
        }
    }
  }

  private def runGoals(args: Array[String]): Unit = {
    val jsonMode = args.contains("--json")
    val fileOpt = args.find(a => !a.startsWith("--"))
    val filePath = fileOpt match {
      case Some(f) => Paths.get(f)
      case None =>
        System.err.println("Error: 'goals' requires a source file path")
        sys.exit(1)
    }
    val sourceOpt = if (Files.exists(filePath)) Some(Files.readString(filePath)) else None
    val initialEnv = ElabEnv(searchPaths = DefaultSearchPaths, holeCollectionMode = true)

    Elaborator.checkFile(filePath, initialEnv) match {
      case Left(diag) =>
        if (jsonMode) {
          println(Json.obj("ok" -> Json.Bool(false), "diagnostics" -> Json.Arr(List(diag.toJson))).pretty)
        } else {
          System.err.print(diag.formatHuman(sourceOpt))
        }
        sys.exit(1)
      case Right(env) =>
        val holeReports = env.holes.zipWithIndex.map { case (h, idx) =>
          val goal = ProofGoal(idx, h.name.getOrElse(s"hole_$idx"), h.localCtx, h.expectedType)
          val suggestions = ProofSearch.suggest(env, goal)
          (h, goal, suggestions)
        }
        if (jsonMode) {
          val jsonHoles = holeReports.map { case (h, goal, sugs) =>
            Json.obj(
              "hole" -> h.toJson(env.kernelEnv),
              "goalShape" -> Json.Str(goal.goalShape(env.kernelEnv)),
              "suggestions" -> Json.Arr(sugs.map(_.toJson))
            )
          }
          println(Json.obj("ok" -> Json.Bool(true), "holeCount" -> Json.Num(jsonHoles.length), "holes" -> Json.Arr(jsonHoles)).pretty)
        } else {
          if (holeReports.isEmpty) {
            println(s"No open proof holes in '$filePath'.")
          } else {
            println(s"Found ${holeReports.length} open proof hole(s) in '$filePath':\n")
            for ((h, goal, sugs) <- holeReports) {
              println(s"At ${h.span}:")
              print(goal.formatHuman(env.kernelEnv))
              val topSugs = sugs.take(4).map(s => s"${s.tactic} (${(s.confidence * 100).toInt}%)").mkString(", ")
              println(s"  suggestions: $topSugs\n")
            }
          }
        }
    }
  }

  private def runVerifyProject(args: Array[String]): Unit = {
    val jsonMode = args.contains("--json")
    val strictMode = args.contains("--strict")
    val dirPath = args.find(a => !a.startsWith("--")).map(Paths.get(_)).getOrElse(Paths.get("."))

    val files =
      if (Files.exists(dirPath)) {
        Files
          .walk(dirPath)
          .toArray
          .map(_.asInstanceOf[Path])
          .filter(p => Files.isRegularFile(p) && p.toString.endsWith(".samurai") && !p.toString.contains("target"))
          .sortBy(_.toString)
          .toList
      } else Nil

    val reports = List.newBuilder[Json]
    var allPassed = true
    var totalTheorems = 0

    for (file <- files) {
      val started = System.nanoTime()
      val res = Elaborator.checkFile(file, ElabEnv(searchPaths = DefaultSearchPaths))
      val elapsedMs = (System.nanoTime() - started) / 1_000_000L
      res match {
        case Right(env) =>
          val axioms = env.kernelEnv.allAxiomsUsed
          val ok = !(strictMode && axioms.nonEmpty)
          if (!ok) allPassed = false
          val thmCount = env.kernelEnv.defs.values.count(_.isTheorem)
          totalTheorems += thmCount
          reports += Json.obj(
            "file" -> Json.Str(file.toString),
            "ok" -> Json.Bool(ok),
            "theorems" -> Json.Num(thmCount),
            "isAxiomFree" -> Json.Bool(axioms.isEmpty),
            "elapsedMs" -> Json.Num(elapsedMs.toDouble)
          )
          if (!jsonMode) {
            val tag = if (ok) "PASS" else "FAIL(axioms)"
            println(f"  [$tag%-12s] ${file.toString}%-35s  theorems=$thmCount%2d  axiomFree=${axioms.isEmpty}%-5s  (${elapsedMs}ms)")
          }
        case Left(diag) =>
          allPassed = false
          reports += Json.obj(
            "file" -> Json.Str(file.toString),
            "ok" -> Json.Bool(false),
            "error" -> Json.Str(diag.message),
            "elapsedMs" -> Json.Num(elapsedMs.toDouble)
          )
          if (!jsonMode) {
            println(f"  [FAIL        ] ${file.toString}%-35s  ${diag.code}: ${diag.message}")
          }
      }
    }

    if (jsonMode) {
      println(
        Json.obj(
          "ok" -> Json.Bool(allPassed),
          "fileCount" -> Json.Num(files.length),
          "files" -> Json.Arr(reports.result())
        ).pretty
      )
    } else {
      println(s"\nVerified ${files.length} file(s); status: ${if (allPassed) "ALL PASSED" else "FAILED"}")
    }
    if (!allPassed) sys.exit(1)
  }
}
