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

  test("mutual recursion, well-founded termination_by / decreasing_by, and sound isolated partial def") {
    val validSource =
      """
        |import Prelude.*
        |import Nat.*
        |import List.*
        |import WellFounded.*
        |
        |mutual {
        |  def evenCheck(n: Nat): Bool = {
        |    n match {
        |      case Nat.Zero => true
        |      case Nat.Succ(p) => oddCheck(p)
        |    }
        |  }
        |  def oddCheck(n: Nat): Bool = {
        |    n match {
        |      case Nat.Zero => false
        |      case Nat.Succ(p) => evenCheck(p)
        |    }
        |  }
        |}
        |
        |theorem even4: evenCheck(4) === true = by { refl }
        |theorem odd5: oddCheck(5) === true = by { refl }
        |
        |def countDownStep(n: Nat): Nat = {
        |  n match {
        |    case Nat.Zero => 0
        |    case Nat.Succ(p) => 1 + countDownStep(p)
        |  }
        |} termination_by {
        |  n
        |} decreasing_by {
        |  rewrite(_wf_eq_6)
        |  apply(ltSelfSucc)
        |}
        |
        |theorem countDown3: countDownStep(3) === 3 = by { refl }
        |
        |mutual {
        |  partial def ping(n: Nat): Nat = {
        |    if (n == 0) { 0 } else { pong(n - 1) }
        |  }
        |  partial def pong(n: Nat): Nat = {
        |    if (n == 0) { 1 } else { ping(n - 1) }
        |  }
        |}
        |
        |#eval ping(5)
      """.stripMargin

    val env = checkOk(validSource)
    assertEquals(env.kernelEnv.allAxiomsUsed, Set.empty[String])
    assertEquals(env.kernelEnv.allPartialDefs, Set("ping", "pong"))
    assert(env.directives.exists(d => d.directive == "eval" && d.output == "1"), s"Got ${env.directives}")

    // Non-decreasing mutual recursion rejected (K020)
    val badMutual = Elaborator.checkSource(
      "badMutual.samurai",
      """
        |import Prelude.*
        |import Nat.*
        |mutual {
        |  def a(n: Nat): False = { b(n) }
        |  def b(n: Nat): False = { a(n) }
        |}
      """.stripMargin,
      baseEnv
    )
    assert(badMutual.isLeft && badMutual.left.toOption.get.code == "K020", s"Expected K020, got $badMutual")

    // Non-decreasing termination_by rejected (K020)
    val badWf = Elaborator.checkSource(
      "badWf.samurai",
      """
        |import Prelude.*
        |import Nat.*
        |import WellFounded.*
        |def badLoop(n: Nat): Nat = { badLoop(n) } termination_by { n }
      """.stripMargin,
      baseEnv
    )
    assert(badWf.isLeft && badWf.left.toOption.get.code == "K020", s"Expected K020, got $badWf")

    // partial def returning Prop rejected (K030)
    val badPartialProp = Elaborator.checkSource(
      "badPartialProp.samurai",
      """
        |import Prelude.*
        |import Nat.*
        |partial def fakeProof(n: Nat): False = { fakeProof(n) }
      """.stripMargin,
      baseEnv
    )
    assert(badPartialProp.isLeft && badPartialProp.left.toOption.get.code == "K030", s"Expected K030, got $badPartialProp")

    // Total function calling partial def rejected (K031)
    val badPartialLeak = Elaborator.checkSource(
      "badPartialLeak.samurai",
      """
        |import Prelude.*
        |import Nat.*
        |partial def diverge(n: Nat): Nat = { diverge(n) }
        |def totalWrapper(n: Nat): Nat = { diverge(n) }
      """.stripMargin,
      baseEnv
    )
    assert(badPartialLeak.isLeft && badPartialLeak.left.toOption.get.code == "K031", s"Expected K031, got $badPartialLeak")
  }

  test("documentation examples: Proofs for Programmers side-by-side function vs tactic proofs") {
    val source =
      """
        |import Prelude.*
        |import Nat.*
        |
        |def andCommAsFunction(left: Prop, right: Prop, both: left /\ right): right /\ left = {
        |  both match {
        |    case And.Intro(leftProof, rightProof) => And.Intro[right, left](rightProof, leftProof)
        |  }
        |}
        |
        |theorem andCommWithTactics(left: Prop, right: Prop, both: left /\ right): right /\ left = by {
        |  cases(both) {
        |    case Intro(leftProof, rightProof) => {
        |      split
        |      exact(rightProof)
        |      exact(leftProof)
        |    }
        |  }
        |}
        |
        |def addZeroRightAsFunction(value: Nat): value + 0 === value = {
        |  value match returning (n: Nat) => n + 0 === n {
        |    case Nat.Zero => Eq.Refl[Nat, 0]
        |    case Nat.Succ(pred) =>
        |      congrArg[Nat, Nat](
        |        (k: Nat) => Nat.Succ(k),
        |        pred + 0,
        |        pred,
        |        addZeroRightAsFunction(pred)
        |      )
        |  }
        |}
        |
        |theorem addZeroRightWithTactics(value: Nat): value + 0 === value = by {
        |  induction(value) {
        |    case Zero => { refl }
        |    case Succ(pred, ih) => {
        |      rewrite(ih)
        |      refl
        |    }
        |  }
        |}
      """.stripMargin

    val env = checkOk(source)
    assertEquals(env.kernelEnv.allAxiomsUsed, Set.empty[String])
  }

  test("practical theorem proving: omega, cc, tauto, combinators (<;>, all, try, repeat, first), in-hyp rewrite/simp, obtain, by_cases, rename") {
    val source =
      """
        |import Prelude.*
        |import Nat.*
        |import List.*
        |import WellFounded.*
        |
        |theorem omegaSuite(a: Nat, b: Nat, c: Nat, h1: Le(a, b), h2: Lt(b, c)):
        |  Le(a + 1, c) /\ (ble(a, c) === true) /\ (blt(c, a) === false) = by {
        |  omega
        |}
        |
        |theorem omegaNeqStrict(a: Nat, b: Nat, hLe: Le(a, b), hNeq: a !== b): Lt(a, b) = by {
        |  omega
        |}
        |
        |theorem ccSuite[A](f: A => A, g: A => A, x: A, y: A, z: A, h1: x === y, h2: f(y) === z):
        |  g(f(x)) === g(z) = by {
        |  cc
        |}
        |
        |theorem ccInjectDisjoint(f: Nat => Nat, a: Nat, b: Nat, h: Nat.Succ(a) === Nat.Succ(b)):
        |  f(a) === f(b) = by {
        |  cc
        |}
        |
        |theorem tautoSuite(p: Prop, q: Prop, r: Prop):
        |  ((p => q) /\ (q => r)) => (p \/ q) => r = by {
        |  tauto
        |}
        |
        |theorem rewriteInStarAndRename(a: Nat, b: Nat, c: Nat, hEq: a === b, hLe: Le(a, c)):
        |  Le(b, c) = by {
        |  rename(hLe, bound)
        |  rewrite(hEq) in *
        |  exact(bound)
        |}
        |
        |theorem simpInStarDemo(a: Nat, b: Nat, h: (a + 0) === (b + 0)): a === b = by {
        |  simp in *
        |  exact(h)
        |}
        |
        |theorem repeatTryAllDemo(a: Nat, b: Nat): (a === b) \/ (a !== b) => (a + 0 === b) \/ (a !== b) = by {
        |  intro(h)
        |  cases(h)
        |  all {
        |    try { left; simp; assumption }
        |    try { right; assumption }
        |  }
        |}
        |
        |theorem seqAllObtainDemo(p: Nat => Prop, q: Nat => Prop, h: exists (x: Nat) => p(x) /\ q(x)):
        |  exists (x: Nat) => q(x) /\ p(x) = by {
        |  obtain(w, hp, hq) = h
        |  exists(w)
        |  split <;> assumption
        |}
        |
        |theorem byCasesFirstDemo(a: Nat, b: Nat): (ble(a, b) === true) \/ (ble(b, a) === true) = by {
        |  by_cases(ble(a, b), cmp) <;> first { { left; omega } | { right; omega } }
        |}
        |
        |theorem repeatSplitDemo: (1 + 1 === 2) /\ (2 + 2 === 4) /\ (3 + 3 === 6) = by {
        |  repeat { split }
        |  all { refl }
        |}
        |
        |theorem decideRefuteLe: ~Le(7, 3) = by {
        |  decide
        |}
      """.stripMargin

    val env = checkOk(source)
    assertEquals(env.kernelEnv.allAxiomsUsed, Set.empty[String])
  }
}
