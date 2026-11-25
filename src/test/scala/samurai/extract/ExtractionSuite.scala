package samurai.extract

import java.nio.file.{Files, Paths}
import munit.FunSuite
import samurai.elab.{ElabEnv, Elaborator}

class ExtractionSuite extends FunSuite {

  private val searchPaths = List(Paths.get("."), Paths.get("stdlib"))

  test("extracts verified Sorting.samurai to Scala 3 and TypeScript with complete Prop erasure") {
    val env = Elaborator
      .checkFile(Paths.get("stdlib", "Sorting.samurai"), ElabEnv(searchPaths = searchPaths))
      .fold(d => fail(d.formatHuman()), identity)

    val extracted = Erasure
      .extract(env, Erasure.ExtractionOptions(moduleName = "VerifiedSorting", requireAxiomFree = true))
      .fold(err => fail(err), identity)

    assert(extracted.manifest.isAxiomFree)
    assert(extracted.manifest.erasedPropositions.contains("Eq"))
    assert(extracted.manifest.erasedPropositions.contains("Le"))
    assert(extracted.manifest.erasedPropositions.contains("False"))
    assert(extracted.manifest.verifiedTheorems.contains("lengthInsertionSort"))
    assert(extracted.manifest.extractedFunctions.contains("insertionSort"))
    assert(extracted.manifest.extractedFunctions.contains("sortWithLengthProof"))

    val scalaCode = Scala3Emitter.emit(extracted)
    // Verify Prop types and theorems do NOT appear in extracted Scala 3 code
    assert(!scalaCode.contains("enum Eq"), "Eq must be erased")
    assert(!scalaCode.contains("enum Le"), "Le must be erased")
    assert(!scalaCode.contains("def lengthInsertionSort"), "Theorems must be erased")
    assert(scalaCode.contains("def insertionSort"))
    assert(scalaCode.contains("enum Nat"))
    assert(scalaCode.contains("enum List"))

    val tsCode = TsEmitter.emit(extracted)
    assert(tsCode.contains("export function insertionSort"))
    assert(!tsCode.contains("lengthInsertionSort"))

    val jsCode = JsEmitter.emit(extracted)
    assert(jsCode.contains("export function insertionSort"))
    assert(jsCode.contains("export function sortVerified"))
    assert(!jsCode.contains("insertionSortIsSorted"))
  }

  test("end-to-end: compiles extracted Vec, Tree, and verified Sorting to Scala 3 and executes on JVM") {
    val combinedSource =
      """
        |import Prelude.*
        |import Nat.*
        |import List.*
        |import Vec.*
        |import Tree.*
        |import Sorting.*
      """.stripMargin

    val env = Elaborator
      .checkSource("CombinedApp.samurai", combinedSource, ElabEnv(searchPaths = searchPaths))
      .fold(d => fail(d.formatHuman()), identity)

    val extracted = Erasure
      .extract(env, Erasure.ExtractionOptions(moduleName = "VerifiedSuite", requireAxiomFree = true))
      .fold(err => fail(err), identity)

    val scalaCode = Scala3Emitter.emit(extracted)

    // Append a verification driver running extracted add, mul, vecHead, tree mirror/flatten, and sortVerified!
    val driverCode =
      s"""$scalaCode
         |
         |object ExtractionRunner {
         |  import VerifiedSuite.*
         |
         |  def toNat(n: Int): Nat = if (n <= 0) Nat.Zero else Nat.Succ(toNat(n - 1))
         |  def fromNat(n: Nat): Int = n match {
         |    case Nat.Zero => 0
         |    case Nat.Succ(p) => 1 + fromNat(p)
         |  }
         |  def toList(xs: scala.List[Int]): List[Nat] =
         |    xs.foldRight[List[Nat]](List.Nil[Nat]())((x, acc) => List.Cons[Nat](toNat(x), acc))
         |  def fromList(xs: List[Nat]): scala.List[Int] = xs match {
         |    case List.Nil() => scala.Nil
         |    case List.Cons(h, t) => fromNat(h) :: fromList(t)
         |  }
         |
         |  def main(args: Array[String]): scala.Unit = {
         |    val sum = fromNat(add(toNat(7), toNat(5)))
         |    val prod = fromNat(mul(toNat(4), toNat(6)))
         |    val sorted = fromList(insertionSort(toList(scala.List(4, 1, 3, 0, 2))))
         |    val verifiedRes = sortVerified(toList(scala.List(5, 2, 4, 1, 3))) match {
         |      case Subset.Mk(v) => fromList(v)
         |    }
         |    val vec = Vec.Cons[Nat](toNat(1), toNat(42), Vec.Cons[Nat](toNat(0), toNat(99), Vec.Nil[Nat]()))
         |    val vHead = fromNat(vecHead[Nat](toNat(1), vec))
         |    val tree = Tree.Node[Nat](Tree.Node[Nat](Tree.Leaf[Nat](), toNat(1), Tree.Leaf[Nat]()), toNat(2), Tree.Node[Nat](Tree.Leaf[Nat](), toNat(3), Tree.Leaf[Nat]()))
         |    val mirroredFlat = fromList(flatten[Nat](mirror[Nat](tree)))
         |    println(s"sum=$$sum;prod=$$prod;sorted=$${sorted.mkString(",")};verified=$${verifiedRes.mkString(",")};vHead=$$vHead;tree=$${mirroredFlat.mkString(",")}")
         |  }
         |}
         |""".stripMargin

    val tempDir = Files.createTempDirectory("samurai-extract-test")
    val srcFile = tempDir.resolve("VerifiedSuite.scala")
    val outClasses = tempDir.resolve("classes")
    Files.createDirectories(outClasses)
    Files.writeString(srcFile, driverCode)

    val testClasspath = System.getProperty("java.class.path")
    val compileProc = new ProcessBuilder(
      "java", "-cp", testClasspath, "dotty.tools.dotc.Main",
      "-classpath", testClasspath,
      "-d", outClasses.toString,
      srcFile.toString
    ).redirectErrorStream(true).start()
    val compileOut = new String(compileProc.getInputStream.readAllBytes())
    val compileCode = compileProc.waitFor()
    assertEquals(compileCode, 0, s"Extracted Scala 3 code failed to compile!\nCode:\n$driverCode\nCompiler output:\n$compileOut")

    val runCp = s"${outClasses.toString}${java.io.File.pathSeparator}$testClasspath"
    val runProc = new ProcessBuilder("java", "-cp", runCp, "ExtractionRunner")
      .redirectErrorStream(true)
      .start()
    val runOut = new String(runProc.getInputStream.readAllBytes()).trim
    val runCode = runProc.waitFor()
    assertEquals(runCode, 0, s"Extracted JVM execution failed:\n$runOut")
    assert(
      runOut.contains("sum=12;prod=24;sorted=0,1,2,3,4;verified=1,2,3,4,5;vHead=42;tree=3,2,1"),
      s"Unexpected runtime output: $runOut"
    )
  }

  test("end-to-end: extracts mutual recursion, well-founded divNat/gcd/quickSort (Acc erased), and partial collatzSteps to Scala 3 and executes on JVM") {
    val env = Elaborator
      .checkFile(Paths.get("examples", "AdvancedRecursion.samurai"), ElabEnv(searchPaths = searchPaths))
      .fold(d => fail(d.formatHuman()), identity)

    // requireTotal=true rejects files with partial defs
    val totalRejected = Erasure.extract(env, Erasure.ExtractionOptions("StrictTotal", requireAxiomFree = true, requireTotal = true))
    assert(totalRejected.isLeft, "requireTotal must reject partial functions")

    // requireAxiomFree=true extracts cleanly while transparently reporting partialFunctions in manifest
    val extracted = Erasure
      .extract(env, Erasure.ExtractionOptions("ExtractedAdvanced", requireAxiomFree = true))
      .fold(err => fail(err), identity)

    assert(extracted.manifest.isAxiomFree)
    assertEquals(extracted.manifest.partialFunctions, List("collatzSteps"))
    assert(!extracted.manifest.isTotal)
    assert(extracted.manifest.erasedPropositions.contains("Acc"))

    val scalaCode = Scala3Emitter.emit(extracted)
    assert(!scalaCode.contains("enum Acc"), "Acc must be completely erased")
    assert(!scalaCode.contains("def natWf"), "natWf must be completely erased")
    assert(!scalaCode.contains("_wfCurMeasure"), "Dead Acc index let-bindings must be eliminated")
    assert(scalaCode.contains("def quickSort"))
    assert(scalaCode.contains("def gcd"))
    assert(scalaCode.contains("def isEven"))
    assert(scalaCode.contains("def collatzSteps"))

    val tsCode = TsEmitter.emit(extracted)
    assert(tsCode.contains("export function quickSort"))
    assert(tsCode.contains("export function gcd"))
    assert(tsCode.contains("export function collatzSteps"))

    val driverCode =
      s"""$scalaCode
         |
         |object AdvancedRunner {
         |  import ExtractedAdvanced.*
         |
         |  def toNat(n: Int): Nat = if (n <= 0) Nat.Zero else Nat.Succ(toNat(n - 1))
         |  def fromNat(n: Nat): Int = n match {
         |    case Nat.Zero => 0
         |    case Nat.Succ(p) => 1 + fromNat(p)
         |  }
         |  def fromBool(b: Bool): Boolean = b match {
         |    case Bool.True => true
         |    case Bool.False => false
         |  }
         |  def toList(xs: scala.List[Int]): List[Nat] =
         |    xs.foldRight[List[Nat]](List.Nil[Nat]())((x, acc) => List.Cons[Nat](toNat(x), acc))
         |  def fromList(xs: List[Nat]): scala.List[Int] = xs match {
         |    case List.Nil() => scala.Nil
         |    case List.Cons(h, t) => fromNat(h) :: fromList(t)
         |  }
         |
         |  def main(args: Array[String]): scala.Unit = {
         |    val ev = fromBool(isEven(toNat(10)))
         |    val od = fromBool(isOdd(toNat(11)))
         |    val d = fromNat(divNat(toNat(17), toNat(5)))
         |    val m = fromNat(modNat(toNat(17), toNat(5)))
         |    val g = fromNat(gcd(toNat(48), toNat(18)))
         |    val qs = fromList(quickSort(toList(scala.List(5, 1, 4, 2, 3))))
         |    val lg = fromNat(log2Floor(toNat(16)))
         |    val col = fromNat(collatzSteps(toNat(6)))
         |    println(s"ev=$$ev;od=$$od;d=$$d;m=$$m;g=$$g;qs=$${qs.mkString(",")};lg=$$lg;col=$$col")
         |  }
         |}
         |""".stripMargin

    val tempDir = Files.createTempDirectory("samurai-advanced-extract")
    val srcFile = tempDir.resolve("ExtractedAdvanced.scala")
    val outClasses = tempDir.resolve("classes")
    Files.createDirectories(outClasses)
    Files.writeString(srcFile, driverCode)

    val testClasspath = System.getProperty("java.class.path")
    val compileProc = new ProcessBuilder(
      "java", "-cp", testClasspath, "dotty.tools.dotc.Main",
      "-classpath", testClasspath,
      "-d", outClasses.toString,
      srcFile.toString
    ).redirectErrorStream(true).start()
    val compileOut = new String(compileProc.getInputStream.readAllBytes())
    val compileCode = compileProc.waitFor()
    assertEquals(compileCode, 0, s"Extracted Advanced Scala 3 failed to compile!\nCode:\n$driverCode\nOutput:\n$compileOut")

    val runCp = s"${outClasses.toString}${java.io.File.pathSeparator}$testClasspath"
    val runProc = new ProcessBuilder("java", "-cp", runCp, "AdvancedRunner")
      .redirectErrorStream(true)
      .start()
    val runOut = new String(runProc.getInputStream.readAllBytes()).trim
    val runCode = runProc.waitFor()
    assertEquals(runCode, 0, s"Extracted Advanced JVM execution failed:\n$runOut")
    assert(
      runOut.contains("ev=true;od=true;d=3;m=2;g=6;qs=1,2,3,4,5;lg=4;col=8"),
      s"Unexpected runtime output: $runOut"
    )
  }

  private def hasBalancedParens(code: String): Boolean = {
    var depth = 0
    var inStr = false
    var escaped = false
    var i = 0
    while (i < code.length) {
      val ch = code.charAt(i)
      if (inStr) {
        if (escaped) escaped = false
        else if (ch == '\\') escaped = true
        else if (ch == '"') inStr = false
      } else {
        if (ch == '"') inStr = true
        else if (ch == '(') depth += 1
        else if (ch == ')') {
          depth -= 1
          if (depth < 0) return false
        }
      }
      i += 1
    }
    depth == 0 && !inStr
  }

  test("extracts verified Sorting, Vec, mutual recursion, and well-founded algorithms to clean Haskell and OCaml") {
    val combinedSource =
      """
        |import Prelude.*
        |import Nat.*
        |import List.*
        |import Vec.*
        |import Tree.*
        |import Sorting.*
        |import WellFounded.*
        |
        |enum FnBox: Type {
        |  case Mk(callback: Nat => Nat)
        |}
        |
        |mutual {
        |  def isEvenCheck(n: Nat): Bool = {
        |    n match {
        |      case Nat.Zero => true
        |      case Nat.Succ(p) => isOddCheck(p)
        |    }
        |  }
        |  def isOddCheck(n: Nat): Bool = {
        |    n match {
        |      case Nat.Zero => false
        |      case Nat.Succ(p) => isEvenCheck(p)
        |    }
        |  }
        |}
        |
        |def keywordSafe(data: Nat, where: Nat, mod: Nat, fun: Nat): Nat = {
        |  add(add(data, where), add(mod, fun))
        |}
      """.stripMargin

    val env = Elaborator
      .checkSource("FunctionalTargets.samurai", combinedSource, ElabEnv(searchPaths = searchPaths))
      .fold(d => fail(d.formatHuman()), identity)

    val extracted = Erasure
      .extract(env, Erasure.ExtractionOptions(moduleName = "VerifiedFunctional", requireAxiomFree = true, requireTotal = true))
      .fold(err => fail(err), identity)

    // --- Haskell assertions ---
    val hsCode = HaskellEmitter.emit(extracted)
    assert(hasBalancedParens(hsCode), s"Unbalanced parens in Haskell output:\n$hsCode")
    assert(hsCode.contains("{-# LANGUAGE NoImplicitPrelude #-}"))
    assert(hsCode.contains("module VerifiedFunctional where"))
    assert(hsCode.contains("import qualified Prelude as P"))
    assert(hsCode.contains("data Nat\n  = Nat_Zero\n  | Nat_Succ Nat\n  deriving (P.Eq, P.Show)"))
    assert(hsCode.contains("List_Nil") && hsCode.contains("Vec_Nil"), "List and Vec constructors must be clash-free")
    assert(hsCode.contains("Pair_Mk") && hsCode.contains("Subset_Mk"), "Pair and Subset constructors must be clash-free")
    // Higher-order ADT must omit deriving (P.Eq, P.Show)
    assert(hsCode.contains("data FnBox\n  = FnBox_Mk (Nat -> Nat)\n\n"), s"FnBox must omit deriving:\n$hsCode")
    assert(hsCode.contains("insertionSort :: List Nat -> List Nat"))
    assert(hsCode.contains("quickSort :: List Nat -> List Nat"))
    assert(hsCode.contains("gcd :: Nat -> Nat -> Nat"))
    assert(hsCode.contains("vecHead :: Nat -> Vec element -> element"))
    assert(hsCode.contains("P.error \"Proof Samurai unreachable:"))
    assert(hsCode.contains("keywordSafe data_ where_ mod fun ="))
    // Complete Prop erasure
    assert(!hsCode.contains("data Eq\n") && !hsCode.contains("data Acc"))
    assert(!hsCode.contains("insertionSortIsSorted"))
    assert(!hsCode.contains("natWf"))

    // --- OCaml assertions ---
    val mlCode = OCamlEmitter.emit(extracted)
    assert(hasBalancedParens(mlCode), s"Unbalanced parens in OCaml output:\n$mlCode")
    assert(mlCode.contains("type nat =\n  | Nat_Zero\n  | Nat_Succ of nat"))
    assert(mlCode.contains("type ('first, 'second) pair =\n  | Pair_Mk of 'first * 'second"))
    assert(mlCode.contains("type 'element vec =\n  | Vec_Nil\n  | Vec_Cons of nat * 'element * 'element vec"))
    assert(mlCode.contains("type fnBox =\n  | FnBox_Mk of (nat -> nat)"))
    // Mutual recursion grouped as `let rec ... and ...`
    assert(mlCode.contains("let rec isEvenCheck (n : nat) : bool ="), s"Missing mutual let rec:\n$mlCode")
    assert(mlCode.contains("and isOddCheck (n : nat) : bool ="), s"Missing mutual `and`:\n$mlCode")
    // Zero-arg unreachable `absurd` is thunked over Stdlib.unit so module load never crashes
    assert(mlCode.contains("let absurd (() : Stdlib.unit) : 'result ="), s"absurd must be thunked in OCaml:\n$mlCode")
    assert(mlCode.contains("let rec insertionSort (items : nat list) : nat list ="))
    assert(mlCode.contains("let rec quickSort_wf (items : nat list) : nat list ="))
    assert(mlCode.contains("let quickSort (items : nat list) : nat list ="))
    assert(mlCode.contains("let rec gcd_wf (left : nat) (right : nat) : nat ="))
    assert(mlCode.contains("let gcd (left : nat) (right : nat) : nat ="))
    assert(mlCode.contains("failwith \"Proof Samurai unreachable:"))
    assert(mlCode.contains("let keywordSafe (data : nat) (where : nat) (mod_ : nat) (fun_ : nat) : nat ="))
    // Complete Prop erasure
    assert(!mlCode.contains("type acc") && !mlCode.contains("type eq"))
    assert(!mlCode.contains("insertionSortIsSorted"))
    assert(!mlCode.contains("natWf"))
  }

  test("extracts VerifiedIO to all 5 targets and executes real-runtime IO interpreter on JVM") {
    val env = Elaborator
      .checkFile(Paths.get("examples/VerifiedIO.samurai"), ElabEnv(searchPaths = searchPaths))
      .fold(d => fail(d.formatHuman()), identity)

    val extracted = Erasure
      .extract(
        env,
        Erasure.ExtractionOptions(moduleName = "ExtractedVerifiedIO", requireAxiomFree = true, requireTotal = true)
      )
      .fold(err => fail(err), identity)

    assert(extracted.manifest.isAxiomFree)
    assert(extracted.manifest.isTotal)
    assert(extracted.manifest.erasedPropositions.contains("Le"))
    assert(extracted.manifest.verifiedTheorems.contains("depositWithCapPreservesInvariant"))
    assert(extracted.manifest.verifiedTheorems.contains("readSortAndPrintOutputIsVerified"))
    assert(extracted.manifest.verifiedTheorems.contains("withdrawSafeSuccessSpec"))

    val scalaCode = Scala3Emitter.emit(extracted)
    val tsCode = TsEmitter.emit(extracted)
    val jsCode = JsEmitter.emit(extracted)
    val hsCode = HaskellEmitter.emit(extracted)
    val mlCode = OCamlEmitter.emit(extracted)

    // Complete erasure of all IO proof specifications (HoareIO, IOEquiv, Sorted, theorems) across all 5 targets
    for ((lang, code) <- scala.List("Scala 3" -> scalaCode, "TS" -> tsCode, "JS" -> jsCode, "Haskell" -> hsCode, "OCaml" -> mlCode)) {
      assert(!code.contains("HoareIO"), s"$lang must erase HoareIO")
      assert(!code.contains("IOEquiv"), s"$lang must erase IOEquiv")
      assert(!code.contains("def Sorted") && !code.contains("function Sorted") && !code.contains("Sorted ::"), s"$lang must erase Sorted")
      assert(!code.contains("depositWithCapPreservesInvariant"), s"$lang must erase Hoare invariant theorem")
      assert(!code.contains("readSortAndPrintOutputIsVerified"), s"$lang must erase IO sorting theorem")
      assert(!code.contains("withdrawSafeSuccessSpec"), s"$lang must erase withdraw spec theorem")
    }

    assert(scalaCode.contains("enum IO[Result]"))
    assert(scalaCode.contains("enum Eff[Req, Resp, Result]"))
    assert(tsCode.contains("export function readSortAndPrint"))
    assert(jsCode.contains("export function withdrawSafe"))
    assert(hasBalancedParens(hsCode), s"Unbalanced parens in Haskell VerifiedIO output:\n$hsCode")
    assert(hsCode.contains("data IO result\n  = IO_Pure result"), s"Missing Haskell IO ADT:\n$hsCode")
    assert(hasBalancedParens(mlCode), s"Unbalanced parens in OCaml VerifiedIO output:\n$mlCode")
    assert(mlCode.contains("let rec bind"), s"Missing OCaml bind:\n$mlCode")

    // Compile extracted Scala 3 code + a tiny real-world IO runtime interpreter and run on JVM!
    val driverCode =
      s"""$scalaCode
         |
         |object RealIORunner {
         |  import ExtractedVerifiedIO.*
         |
         |  def toNat(n: Int): Nat = if (n <= 0) Nat.Zero else Nat.Succ(toNat(n - 1))
         |  def fromNat(n: Nat): Int = n match {
         |    case Nat.Zero => 0
         |    case Nat.Succ(p) => 1 + fromNat(p)
         |  }
         |  def fromBool(b: Bool): Boolean = b match {
         |    case Bool.True => true
         |    case Bool.False => false
         |  }
         |  def fromList(xs: List[Nat]): scala.List[Int] = xs match {
         |    case List.Nil() => scala.Nil
         |    case List.Cons(h, t) => fromNat(h) :: fromList(t)
         |  }
         |
         |  /**
         |   * Real-world imperative runtime interpreter for Proof Samurai's verified `IO[A]` effect tree.
         |   * Connects pure verified programs to real input streams, output sinks, and mutable state.
         |   */
         |  def runRealIO[A](
         |    prog: IO[A],
         |    stdin: Iterator[Int],
         |    stdout: scala.collection.mutable.ListBuffer[Int],
         |    getStore: () => Int,
         |    putStore: Int => scala.Unit
         |  ): A = {
         |    var cur: IO[A] = prog
         |    while (true) {
         |      cur match {
         |        case IO.Pure(v) => return v
         |        case IO.PrintNat(v, next) =>
         |          stdout += fromNat(v)
         |          cur = next
         |        case IO.ReadNat(k) =>
         |          val nextIn = if (stdin.hasNext) stdin.next() else 0
         |          cur = k(toNat(nextIn))
         |        case IO.GetState(k) =>
         |          cur = k(toNat(getStore()))
         |        case IO.PutState(s, next) =>
         |          putStore(fromNat(s))
         |          cur = next
         |      }
         |    }
         |    throw new AssertionError("unreachable")
         |  }
         |
         |  def main(args: Array[String]): scala.Unit = {
         |    // 1. Interactive adder
         |    val out1 = scala.collection.mutable.ListBuffer.empty[Int]
         |    var st1 = 5
         |    val sumRes = fromNat(runRealIO(readAndPrintSum, Iterator(10, 32, 99), out1, () => st1, s => st1 = s))
         |
         |    // 2. Bank account safe withdraw (success + rejection)
         |    val out2 = scala.collection.mutable.ListBuffer.empty[Int]
         |    var balance = 50
         |    val w1 = fromBool(runRealIO(withdrawSafe(toNat(18)), Iterator.empty, out2, () => balance, s => balance = s))
         |    val w2 = fromBool(runRealIO(withdrawSafe(toNat(40)), Iterator.empty, out2, () => balance, s => balance = s))
         |
         |    // 3. Capped deposit (accepted + rejected at cap=50)
         |    val out3 = scala.collection.mutable.ListBuffer.empty[Int]
         |    val d1 = fromBool(runRealIO(depositWithCap(toNat(50)), Iterator(10), out3, () => balance, s => balance = s))
         |    val d2 = fromBool(runRealIO(depositWithCap(toNat(50)), Iterator(20), out3, () => balance, s => balance = s))
         |
         |    // 4. Verified IO sorting pipeline
         |    val out4 = scala.collection.mutable.ListBuffer.empty[Int]
         |    var st4 = 0
         |    val sortedRes = fromList(runRealIO(readSortAndPrint(toNat(5)), Iterator(4, 1, 5, 2, 3), out4, () => st4, s => st4 = s))
         |
         |    println(
         |      s"sum=$$sumRes/out1=$${out1.mkString(",")};w=$$w1,$$w2/out2=$${out2.mkString(",")};d=$$d1,$$d2/bal=$$balance/out3=$${out3.mkString(",")};sort=$${sortedRes.mkString(",")}/out4=$${out4.mkString(",")}"
         |    )
         |  }
         |}
         |""".stripMargin

    val tempDir = Files.createTempDirectory("samurai-verified-io")
    val srcFile = tempDir.resolve("ExtractedVerifiedIO.scala")
    val outClasses = tempDir.resolve("classes")
    Files.createDirectories(outClasses)
    Files.writeString(srcFile, driverCode)

    val testClasspath = System.getProperty("java.class.path")
    val compileProc = new ProcessBuilder(
      "java", "-cp", testClasspath, "dotty.tools.dotc.Main",
      "-classpath", testClasspath,
      "-d", outClasses.toString,
      srcFile.toString
    ).redirectErrorStream(true).start()
    val compileOut = new String(compileProc.getInputStream.readAllBytes())
    val compileCode = compileProc.waitFor()
    assertEquals(compileCode, 0, s"Extracted VerifiedIO Scala 3 failed to compile!\nCode:\n$driverCode\nOutput:\n$compileOut")

    val runCp = s"${outClasses.toString}${java.io.File.pathSeparator}$testClasspath"
    val runProc = new ProcessBuilder("java", "-cp", runCp, "RealIORunner")
      .redirectErrorStream(true)
      .start()
    val runOut = new String(runProc.getInputStream.readAllBytes()).trim
    val runCode = runProc.waitFor()
    assertEquals(runCode, 0, s"Extracted VerifiedIO JVM execution failed:\n$runOut")
    assert(
      runOut.contains("sum=42/out1=42;w=true,false/out2=1,0;d=true,false/bal=42/out3=42,42;sort=1,2,3,4,5/out4=1,2,3,4,5"),
      s"Unexpected real-IO runtime output: $runOut"
    )
  }
}
