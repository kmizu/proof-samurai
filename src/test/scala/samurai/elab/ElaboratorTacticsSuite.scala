package samurai.elab

import java.nio.file.Paths
import munit.FunSuite

class ElaboratorTacticsSuite extends FunSuite {

  private val baseEnv = ElabEnv(searchPaths = List(Paths.get("."), Paths.get("stdlib")))

  private def checkOk(source: String): ElabEnv = {
    Elaborator.checkSource("test.samurai", source, baseEnv) match {
      case Left(diag) => fail(s"Expected success, got error:\n${diag.formatHuman(Some(source))}")
      case Right(env) => env
    }
  }

  test("programmer-friendly features: case class, dot projection, UFCS, operators, blocks, and #eval") {
    val source =
      """
        |import Prelude.*
        |import Nat.*
        |import List.*
        |
        |def swap[A, B](pair: Pair[A, B]): Pair[B, A] = {
        |  Pair(pair.second, pair.first)
        |}
        |
        |def doubleLength[A](items: List[A]): Nat = {
        |  val len = items.length
        |  len + len
        |}
        |
        |theorem swapSwap[A, B](pair: Pair[A, B]): swap(swap(pair)) === pair = by {
        |  cases(pair) {
        |    case Mk(first, second) => { refl }
        |  }
        |}
        |
        |theorem concreteArithmetic: (2 + 3) * 4 === 20 = by {
        |  decide
        |}
        |
        |theorem concreteOrder: Le(2, 5) = by {
        |  decide
        |}
        |
        |#eval doubleLength(1 :: 2 :: 3 :: List.Nil[Nat])
        |#axioms swapSwap
      """.stripMargin

    val env = checkOk(source)
    assertEquals(env.kernelEnv.allAxiomsUsed, Set.empty[String])
    assert(env.directives.exists(d => d.directive == "eval" && d.output == "6"), s"Expected readable eval output '6', got ${env.directives}")
    assert(env.directives.exists(d => d.directive == "axioms" && d.output.contains("100% axiom-free")))
  }

  test("tactics: have, trans, congr, exists, auto, and sorry tracking") {
    val source =
      """
        |import Prelude.*
        |import Nat.*
        |
        |theorem existsWitness: exists (x: Nat) => x + 2 === 5 = by {
        |  exists(3)
        |  refl
        |}
        |
        |theorem haveAndCongr(left: Nat, right: Nat, eqProof: left === right): (left + 1) === (right + 1) = by {
        |  have(step: Nat.Succ(left) === Nat.Succ(right)) {
        |    congr
        |    exact(eqProof)
        |  }
        |  rewrite(eqProof)
        |  refl
        |}
        |
        |theorem autoLogic(first: Prop, second: Prop, third: Prop):
        |  (first => second) => (second => third) => (first /\ second) => third = by {
        |  auto
        |}
      """.stripMargin

    val env = checkOk(source)
    assertEquals(env.kernelEnv.allAxiomsUsed, Set.empty[String])
  }

  test("surface soundness: rejects non-terminating def, negative enum, non-exhaustive match, and Prop->Type leak") {
    val nonTerminating =
      """
        |import Prelude.*
        |import Nat.*
        |def infiniteLoop(value: Nat): False = { infiniteLoop(value) }
      """.stripMargin
    assert(Elaborator.checkSource("bad1.samurai", nonTerminating, baseEnv).isLeft)

    val nonPositive =
      """
        |import Prelude.*
        |enum BadLoop: Type {
        |  case Mk(callback: BadLoop => False)
        |}
      """.stripMargin
    assert(Elaborator.checkSource("bad2.samurai", nonPositive, baseEnv).isLeft)

    val nonExhaustive =
      """
        |import Prelude.*
        |import Nat.*
        |def partialPred(value: Nat): Nat = {
        |  value match {
        |    case Nat.Succ(pred) => pred
        |  }
        |}
      """.stripMargin
    assert(Elaborator.checkSource("bad3.samurai", nonExhaustive, baseEnv).isLeft)

    val propToTypeLeak =
      """
        |import Prelude.*
        |import Nat.*
        |def leakOr(disjunction: Or[True, True]): Nat = {
        |  disjunction match {
        |    case Or.Inl(_) => 0
        |    case Or.Inr(_) => 1
        |  }
        |}
      """.stripMargin
    assert(Elaborator.checkSource("bad4.samurai", propToTypeLeak, baseEnv).isLeft)
  }

  test("sorry is explicitly tracked as an axiom and rejected by strict extraction") {
    val withSorry =
      """
        |import Prelude.*
        |theorem unproven: False = by {
        |  sorry
        |}
      """.stripMargin
    val env = checkOk(withSorry)
    assert(env.kernelEnv.allAxiomsUsed.nonEmpty, "sorry must be tracked in axiomsUsed")
    val strictExt = samurai.extract.Erasure.extract(env, samurai.extract.Erasure.ExtractionOptions(requireAxiomFree = true))
    assert(strictExt.isLeft, "strict extraction must reject files using sorry")
  }

  test("multi-clause nested patterns, qualified module access, revert, exfalso, subst, and specialize") {
    val source =
      """
        |import Prelude.*
        |import Nat.*
        |import List.*
        |
        |def classifySmall(number: Nat): Nat = {
        |  number match {
        |    case 0 => 10
        |    case 1 => 20
        |    case 2 => 30
        |    case _ => 99
        |  }
        |}
        |
        |def qualifiedSum(left: Nat, right: Nat): Nat = {
        |  Nat.add(left, right)
        |}
        |
        |theorem classifyChecks:
        |  (classifySmall(0) === 10) /\ (classifySmall(1) === 20) /\ (classifySmall(2) === 30) /\ (classifySmall(5) === 99) = by {
        |  decide
        |}
        |
        |theorem revertDemo(left: Nat, right: Nat): (ble(left, right) === true) \/ (ble(right, left) === true) = by {
        |  revert(right)
        |  exact(bleTotal(left))
        |}
        |
        |theorem exfalsoAndSpecialize(pred: Nat => Prop, witness: forall (n: Nat) => pred(n) => False, proofZero: pred(0)): 1 === 2 = by {
        |  exfalso
        |  specialize(witness, 0, proofZero)
        |  exact(witness)
        |}
        |
        |theorem substDemo(left: Nat, right: Nat, eqProof: left === right): left + 1 === right + 1 = by {
        |  subst(eqProof)
        |  refl
        |}
      """.stripMargin

    val env = checkOk(source)
    assertEquals(env.kernelEnv.allAxiomsUsed, Set.empty[String])
  }

  test("pragmatic readable features: list literals, calc blocks, arith semiring solver, multi-rewrite, and simp(*)") {
    val source =
      """
        |import Prelude.*
        |import Nat.*
        |import List.*
        |
        |def sampleList: List[Nat] = [1, 2, 3]
        |
        |theorem listLitPattern(xs: List[Nat]): Bool = {
        |  xs match {
        |    case [] => false
        |    case [_, _] => true
        |    case _ => false
        |  }
        |}
        |
        |theorem arithLinear(a: Nat, b: Nat, c: Nat): (a + b) + Nat.Succ(c) === Nat.Succ(c + a) + b = by {
        |  arith
        |}
        |
        |theorem arithSemiring(a: Nat, b: Nat, c: Nat, d: Nat):
        |  (a + b) * (c + d) === (d * b + a * c) + (b * c + d * a) = by {
        |  arith
        |}
        |
        |theorem calcProof(a: Nat, b: Nat): (a + b) + 0 === b + a = {
        |  calc {
        |    (a + b) + 0
        |    === a + b by { simp }
        |    === b + a by { arith }
        |  }
        |}
        |
        |theorem multiRewriteAndSimpStar(a: Nat, b: Nat, c: Nat, h1: a === b, h2: b === c): a + 1 === c + 1 = by {
        |  rewrite(h1, h2)
        |  refl
        |}
        |
        |theorem simpStarDemo(a: Nat, b: Nat, eqAB: a === b): a + 0 === b = by {
        |  simp(*)
        |}
        |
        |#eval sampleList
      """.stripMargin

    val env = checkOk(source)
    assertEquals(env.kernelEnv.allAxiomsUsed, Set.empty[String])
    assert(env.directives.exists(d => d.directive == "eval" && d.output == "[1, 2, 3]"), s"Got ${env.directives}")
  }
}
