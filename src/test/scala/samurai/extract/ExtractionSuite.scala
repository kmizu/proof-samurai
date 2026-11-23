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
}
