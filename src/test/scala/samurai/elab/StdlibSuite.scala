package samurai.elab

import java.nio.file.Paths
import munit.FunSuite

class StdlibSuite extends FunSuite {

  private val searchPaths = List(Paths.get("."), Paths.get("stdlib"))

  private def checkStdlibFile(fileName: String): ElabEnv = {
    val path = Paths.get("stdlib", fileName)
    val source = java.nio.file.Files.readString(path)
    Elaborator.checkFile(path, ElabEnv(searchPaths = searchPaths)) match {
      case Left(diag) =>
        fail(s"Stdlib file '$fileName' failed verification:\n${diag.formatHuman(Some(source))}")
      case Right(env) =>
        assertEquals(env.kernelEnv.allAxiomsUsed, Set.empty[String], s"'$fileName' must be 100% axiom-free")
        env
    }
  }

  test("Prelude.samurai verifies 100% axiom-free") {
    val env = checkStdlibFile("Prelude.samurai")
    assert(env.kernelEnv.defs.contains("andComm"))
    assert(env.kernelEnv.defs.contains("orComm"))
    assert(env.kernelEnv.defs.contains("trueIsNotFalse"))
  }

  test("Nat.samurai verifies all arithmetic theorems 100% axiom-free") {
    val env = checkStdlibFile("Nat.samurai")
    for (thm <- List("addZeroRight", "addComm", "addAssoc", "mulZeroRight", "mulComm", "mulAssoc", "bleTotal", "zeroNotSucc", "succInjective")) {
      assert(env.kernelEnv.defs.contains(thm), s"Missing theorem $thm")
      assertEquals(env.kernelEnv.defs(thm).axiomsUsed, Set.empty[String])
    }
  }

  test("List.samurai verifies all list theorems 100% axiom-free") {
    val env = checkStdlibFile("List.samurai")
    for (thm <- List("appendNilRight", "appendAssoc", "lengthAppend", "lengthReverse", "reverseAppend", "reverseReverse", "mapFusion")) {
      assert(env.kernelEnv.defs.contains(thm), s"Missing theorem $thm")
      assertEquals(env.kernelEnv.defs(thm).axiomsUsed, Set.empty[String])
    }
  }

  test("Vec.samurai verifies length-indexed vectors and safe total vecHead 100% axiom-free") {
    val env = checkStdlibFile("Vec.samurai")
    assert(env.kernelEnv.defs.contains("vecHead"))
    assert(env.kernelEnv.defs.contains("vecAppend"))
    assert(env.kernelEnv.defs.contains("vecMap"))
  }

  test("Sorting.samurai verifies full insertion sort correctness (Sorted + count permutation + length) 100% axiom-free") {
    val env = checkStdlibFile("Sorting.samurai")
    for (thm <- List("lengthInsert", "lengthInsertionSort", "countInsert", "countInsertionSort", "insertPreservesSorted", "insertionSortIsSorted", "sortVerified")) {
      assert(env.kernelEnv.defs.contains(thm), s"Missing declaration $thm")
      assertEquals(env.kernelEnv.defs(thm).axiomsUsed, Set.empty[String])
    }
  }

  test("Tree.samurai verifies binary tree mirror, size, and flatten theorems 100% axiom-free") {
    val env = checkStdlibFile("Tree.samurai")
    for (thm <- List("mirrorMirror", "sizeMirror", "lengthFlatten", "flattenMirror")) {
      assert(env.kernelEnv.defs.contains(thm), s"Missing theorem $thm")
      assertEquals(env.kernelEnv.defs(thm).axiomsUsed, Set.empty[String])
    }
  }

  test("Option.samurai verifies functor and monad laws 100% axiom-free") {
    val env = checkStdlibFile("Option.samurai")
    for (thm <- List("optionMapId", "optionMapCompose", "optionFlatMapLeftId", "optionFlatMapRightId", "optionFlatMapAssoc")) {
      assert(env.kernelEnv.defs.contains(thm), s"Missing theorem $thm")
      assertEquals(env.kernelEnv.defs(thm).axiomsUsed, Set.empty[String])
    }
  }

  test("Queue.samurai verifies amortized two-stack functional queue 100% axiom-free") {
    val env = checkStdlibFile("Queue.samurai")
    for (thm <- List("toListEmpty", "toListEnqueue", "queueSizeEnqueue", "dequeueEmpty")) {
      assert(env.kernelEnv.defs.contains(thm), s"Missing theorem $thm")
      assertEquals(env.kernelEnv.defs(thm).axiomsUsed, Set.empty[String])
    }
  }

  test("WellFounded.samurai verifies 0-axiom Acc, natWf, divNat, modNat, gcd, and quickSort totally") {
    val env = checkStdlibFile("WellFounded.samurai")
    assertEquals(env.kernelEnv.allPartialDefs, Set.empty[String], "WellFounded.samurai must be 100% total")
    assert(env.kernelEnv.inductives("Acc").isSubsingleton, "Acc must be recognized as a CIC subsingleton")
    for (sym <- List("natWf", "natStrongInd", "subLtSelf", "halfLtSelf", "lengthFilterLe", "divNat", "modNat", "gcd", "quickSort")) {
      assert(env.kernelEnv.defs.contains(sym), s"Missing well-founded symbol $sym")
      assertEquals(env.kernelEnv.defs(sym).axiomsUsed, Set.empty[String])
    }
  }

  test("IO.samurai verifies 0-axiom Free Monad IO, higher-order induction, monad laws, and HoareIO") {
    val env = checkStdlibFile("IO.samurai")
    assertEquals(env.kernelEnv.allPartialDefs, Set.empty[String], "IO.samurai must be 100% total")
    for (sym <- List("runIOBind", "ioLeftId", "ioRightId", "ioAssoc", "runIOPrintList", "runIOReadN", "hoarePure", "hoareBind", "hoareConseq")) {
      assert(env.kernelEnv.defs.contains(sym), s"Missing IO theorem $sym")
      assertEquals(env.kernelEnv.defs(sym).axiomsUsed, Set.empty[String])
    }
  }

  test("all examples/*.samurai verify 100% axiom-free") {
    for (example <- List("HelloProof.samurai", "VerifiedSort.samurai", "SafeVec.samurai", "Showcase.samurai", "AdvancedRecursion.samurai", "PracticalProving.samurai", "TacticGallery.samurai", "VerifiedIO.samurai")) {
      val path = Paths.get("examples", example)
      val source = java.nio.file.Files.readString(path)
      Elaborator.checkFile(path, ElabEnv(searchPaths = searchPaths)) match {
        case Left(diag) =>
          fail(s"Example '$example' failed verification:\n${diag.formatHuman(Some(source))}")
        case Right(env) =>
          assertEquals(env.kernelEnv.allAxiomsUsed, Set.empty[String], s"Example '$example' must be 100% axiom-free")
      }
    }
  }
}
