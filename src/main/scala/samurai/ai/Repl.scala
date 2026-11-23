package samurai.ai

import java.io.{BufferedReader, InputStreamReader}
import java.nio.file.{Path, Paths}
import samurai.elab.{ElabEnv, Elaborator}
import samurai.extract.{Erasure, JsEmitter, Scala3Emitter, TsEmitter}

/**
 * Interactive multi-line brace-aware REPL for human exploration of Proof Samurai programs and proofs.
 */
object Repl {
  def run(searchPaths: List[Path]): Unit = {
    println("Proof Samurai v0.1.0 — Sound Dependently-Typed Proof Assistant (Scala 3 brace syntax)")
    println("Type declarations (multi-line { ... } supported), #check, #eval, :load <file>, :extract scala3|ts|js, :env, :help, or :quit")

    var env = ElabEnv(searchPaths = searchPaths)
    val reader = new BufferedReader(new InputStreamReader(System.in))
    var running = true

    while (running) {
      print("samurai> ")
      Console.out.flush()
      val firstLine = reader.readLine()
      if (firstLine == null) {
        running = false
      } else {
        val trimmedFirst = firstLine.trim
        if (trimmedFirst.isEmpty) {
          ()
        } else if (trimmedFirst.startsWith(":")) {
          if (trimmedFirst == ":quit" || trimmedFirst == ":q") {
            running = false
          } else {
            env = handleCommand(trimmedFirst, env, searchPaths)
          }
        } else {
          // Accumulate multi-line input until braces/parens/brackets are balanced!
          val buffer = new StringBuilder(firstLine)
          var depth = delimiterBalance(firstLine)
          while (depth > 0) {
            print("     ... ")
            Console.out.flush()
            val nextLine = reader.readLine()
            if (nextLine == null) {
              depth = 0
            } else {
              buffer.append('\n').append(nextLine)
              depth += delimiterBalance(nextLine)
            }
          }
          val input = buffer.toString
          Elaborator.checkSource("<repl>", input, env) match {
            case Left(diag) => println(diag.formatHuman(Some(input)))
            case Right(nextEnv) =>
              val newDirs = nextEnv.directives.drop(env.directives.length)
              val newDecls = nextEnv.kernelEnv.declOrder.drop(env.kernelEnv.declOrder.length)
              env = nextEnv
              newDecls.foreach(name => println(s"Verified: $name"))
              newDirs.foreach(d => println(s"[#${d.directive}] ${d.output}"))
          }
        }
      }
    }
  }

  private def delimiterBalance(line: String): Int = {
    var balance = 0
    var idx = 0
    while (idx < line.length) {
      val ch = line.charAt(idx)
      if (ch == '/' && idx + 1 < line.length && line.charAt(idx + 1) == '/') {
        return balance
      }
      if (ch == '{' || ch == '(' || ch == '[') balance += 1
      else if (ch == '}' || ch == ')' || ch == ']') balance -= 1
      idx += 1
    }
    balance
  }

  private def handleCommand(cmd: String, env: ElabEnv, searchPaths: List[Path]): ElabEnv = {
    if (cmd == ":help" || cmd == ":h") {
      println(
        """Commands:
          |  :load <file.samurai>       Load and verify a Proof Samurai source file
          |  :extract [scala3|ts|js]    Extract verified code to Scala 3, TypeScript, or JavaScript
          |  :env                       List verified inductives, definitions, theorems, and axioms
          |  :reset                     Reset the environment
          |  #check <expr>              Infer and display the type of an expression
          |  #eval <expr>               Normalize and evaluate an expression via NbE
          |  #print <name>              Print a declaration's type and body
          |  #axioms <name>             Check whether a theorem is 100% axiom-free
          |  :quit                      Exit the REPL
          |""".stripMargin
      )
      env
    } else if (cmd == ":reset") {
      println("Environment reset.")
      ElabEnv(searchPaths = searchPaths)
    } else if (cmd == ":env") {
      val k = env.kernelEnv
      println(s"Inductives (${k.inductives.size}): ${k.inductives.keys.toList.sorted.mkString(", ")}")
      val fns = k.defs.values.filterNot(_.isTheorem).map(_.name).toList.sorted
      val thms = k.defs.values.filter(_.isTheorem).map(_.name).toList.sorted
      println(s"Functions  (${fns.size}): ${fns.mkString(", ")}")
      println(s"Theorems   (${thms.size}): ${thms.mkString(", ")}")
      if (k.allAxiomsUsed.isEmpty) println("Trust:     100% axiom-free!")
      else println(s"Axioms:    ${k.allAxiomsUsed.toList.sorted.mkString(", ")}")
      env
    } else if (cmd.startsWith(":load ")) {
      val path = Paths.get(cmd.stripPrefix(":load ").trim)
      Elaborator.checkFile(path, env) match {
        case Left(diag) =>
          println(diag.formatHuman())
          env
        case Right(nextEnv) =>
          val newDirs = nextEnv.directives.drop(env.directives.length)
          println(s"Loaded and kernel-verified '$path' (${nextEnv.kernelEnv.declOrder.size} total declarations).")
          newDirs.foreach(d => println(s"[#${d.directive}] ${d.output}"))
          nextEnv
      }
    } else if (cmd.startsWith(":extract")) {
      val target = cmd.stripPrefix(":extract").trim.toLowerCase match {
        case "ts" | "typescript" => "ts"
        case "js" | "javascript" => "js"
        case _                   => "scala3"
      }
      Erasure.extract(env) match {
        case Left(err) => println(s"Extraction error: $err")
        case Right(mod) =>
          val code = target match {
            case "ts" => TsEmitter.emit(mod)
            case "js" => JsEmitter.emit(mod)
            case _    => Scala3Emitter.emit(mod)
          }
          println(code)
      }
      env
    } else {
      println(s"Unknown REPL command '$cmd'. Type :help for available commands.")
      env
    }
  }
}
