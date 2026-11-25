package samurai.kernel

import java.nio.file.Paths
import munit.FunSuite
import samurai.elab.{ElabEnv, Elaborator}
import samurai.extract.{Erasure, HaskellEmitter, JsEmitter, OCamlEmitter, Scala3Emitter, TsEmitter}

/**
 * Red-team / adversarial soundness, boundary, and non-divergence test suite.
 *
 * Systematically attempts to break the Trusted Kernel, tactic solvers (`omega`, `cc`, `tauto`),
 * combinators (`repeat`, `try`, `obtain`, `in hyp`), `#eval` partial evaluation, and all 5 code
 * extraction backends.
 */
class AdversarialSoundnessSuite extends FunSuite {

  private val baseEnv = ElabEnv(searchPaths = List(Paths.get("."), Paths.get("stdlib")))

  private def assertRejected(source: String, expectedCodeOpt: Option[String] = None, label: String = ""): Unit = {
    Elaborator.checkSource("attack.samurai", source, baseEnv) match {
      case Right(_) =>
        fail(s"SECURITY / SOUNDNESS FAILURE [$label]: Expected rejection, but code was accepted!\n$source")
      case Left(diag) =>
        expectedCodeOpt.foreach { code =>
          assertEquals(
            diag.code,
            code,
            s"[$label] Expected error code '$code', got '${diag.code}': ${diag.message}"
          )
        }
    }
  }

  private def checkOkAxiomFree(source: String): ElabEnv = {
    Elaborator.checkSource("edge.samurai", source, baseEnv) match {
      case Left(diag) => fail(s"Expected success, got error:\n${diag.formatHuman(Some(source))}")
      case Right(env) =>
        assertEquals(env.kernelEnv.allAxiomsUsed, Set.empty[String])
        env
    }
  }

  // =========================================================================
  // 1. Trusted Kernel Soundness & Paradox Attacks
  // =========================================================================

  test("attack: fake index-forced subsingleton Prop with unforced computational field is rejected (K025)") {
    val attack =
      """
        |import Prelude.*
        |import Nat.*
        |
        |enum FakeSub(idx: Nat): Prop {
        |  case Mk(forced: Nat, hiddenSecret: Nat): FakeSub(forced)
        |}
        |
        |def leakSecret(n: Nat, pf: FakeSub(n)): Nat = {
        |  pf match {
        |    case FakeSub.Mk(forced, secret) => secret
        |  }
        |}
      """.stripMargin
    assertRejected(attack, Some("K025"), "fake-subsingleton-unforced-field")
  }

  test("attack: nested non-strictly-positive inductive via container Box[Bad] is rejected (K006)") {
    val attack =
      """
        |import Prelude.*
        |
        |enum Box[A: Type]: Type {
        |  case Mk(callback: A => False)
        |}
        |
        |enum BadNested: Type {
        |  case Mk(boxed: Box[BadNested])
        |}
      """.stripMargin
    assertRejected(attack, Some("K006"), "nested-non-positive-box")
  }

  test("attack: partial def cannot sneak into Prop, Type, enum, axiom, theorem type, mixed mutual, or termination_by") {
    // 1. Curried partial def returning Prop (`Nat => False`)
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |partial def sneakProp(n: Nat): Nat => False = { sneakProp(n) }
      """.stripMargin,
      Some("K030"),
      "partial-curried-prop"
    )

    // 2. Type-level partial def returning Type
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |partial def sneakType(n: Nat): Type = { sneakType(n) }
      """.stripMargin,
      Some("K030"),
      "partial-type-level"
    )

    // 3. Partial def leaked into a theorem's type (not just body!)
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |partial def diverge(n: Nat): Nat = { diverge(n) }
        |theorem leakInType: diverge(0) === diverge(0) = by { refl }
      """.stripMargin,
      Some("K031"),
      "partial-in-theorem-type"
    )

    // 4. Partial def leaked into an inductive type field
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |partial def diverge(n: Nat): Nat = { diverge(n) }
        |enum SneakyInd: Prop {
        |  case Mk(eq: diverge(0) === 0)
        |}
      """.stripMargin,
      Some("K031"),
      "partial-in-inductive"
    )

    // 5. Partial def leaked into an axiom type
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |partial def diverge(n: Nat): Nat = { diverge(n) }
        |axiom sneakyAx: diverge(0) === 0
      """.stripMargin,
      Some("K031"),
      "partial-in-axiom"
    )

    // 6. Mutual block mixing total `def` and `partial def`
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |mutual {
        |  def totalSide(n: Nat): Nat = { partialSide(n) }
        |  partial def partialSide(n: Nat): Nat = { totalSide(n) }
        |}
      """.stripMargin,
      None,
      "mixed-total-partial-mutual"
    )

    // 7. Partial def used as termination_by measure
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |import WellFounded.*
        |partial def badMeasure(n: Nat): Nat = { badMeasure(n) }
        |def sneakyWf(n: Nat): Nat = { sneakyWf(n) } termination_by { badMeasure(n) }
      """.stripMargin,
      None,
      "partial-in-termination-measure"
    )
  }

  test("attack: #eval on non-terminating partial def fails cleanly with E033 (no JVM StackOverflowError)") {
    val infiniteEval =
      """
        |import Prelude.*
        |import Nat.*
        |partial def infiniteLoop(n: Nat): Nat = { infiniteLoop(n) }
        |#eval infiniteLoop(0)
      """.stripMargin
    assertRejected(infiniteEval, Some("E033"), "eval-infinite-partial-loop")
  }

  test("attack: subtle mutual/structural termination bypass attempts are all rejected (K020)") {
    // 1. 3-cycle where one edge fails to decrease
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |mutual {
        |  def fA(n: Nat): Nat = {
        |    n match {
        |      case Nat.Zero => 0
        |      case Nat.Succ(p) => fB(p)
        |    }
        |  }
        |  def fB(n: Nat): Nat = {
        |    n match {
        |      case Nat.Zero => 0
        |      case Nat.Succ(p) => fC(p)
        |    }
        |  }
        |  def fC(n: Nat): Nat = { fA(n) }
        |}
      """.stripMargin,
      Some("K020"),
      "mutual-3-cycle-one-nondecreasing"
    )

    // 2. Argument-swapping mutual infinite loop
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |mutual {
        |  def swapF(x: Nat, y: Nat): Nat = { swapG(y, x) }
        |  def swapG(x: Nat, y: Nat): Nat = { swapF(y, x) }
        |}
      """.stripMargin,
      Some("K020"),
      "mutual-arg-swap-loop"
    )

    // 3. Higher-order unapplied recursive self-reference
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |def applyNat(fn: Nat => Nat, x: Nat): Nat = { fn(x) }
        |def sneakyHoLoop(n: Nat): Nat = { applyNat(sneakyHoLoop, n) }
      """.stripMargin,
      Some("K020"),
      "unapplied-ho-recursion"
    )

    // 4. termination_by with increasing measure
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |import WellFounded.*
        |def badMeasureInc(n: Nat): Nat = {
        |  n match {
        |    case Nat.Zero => 0
        |    case Nat.Succ(p) => badMeasureInc(Nat.Succ(Nat.Succ(p)))
        |  }
        |} termination_by { n }
      """.stripMargin,
      Some("K020"),
      "termination-by-increasing"
    )
  }

  test("kernel proof irrelevance never conflates Eq.Refl[Nat, 0] with Eq.Refl[Nat, 1]") {
    val env = checkOkAxiomFree("import Prelude.*\nimport Nat.*").kernelEnv
    val refl0 = Term.apps(Term.Ctor("Eq", "Refl"), List(Term.Ind("Nat"), Term.Ctor("Nat", "Zero")))
    val refl1 = Term.apps(
      Term.Ctor("Eq", "Refl"),
      List(Term.Ind("Nat"), Term.App(Term.Ctor("Nat", "Succ"), Term.Ctor("Nat", "Zero")))
    )
    val v0 = NbE.evaluate(env, Nil, refl0)
    val v1 = NbE.evaluate(env, Nil, refl1)
    assert(!NbE.areConvertible(env, 0, v0, v1), "Eq.Refl[Nat, 0] must NOT be convertible to Eq.Refl[Nat, 1]")
  }

  // =========================================================================
  // 2. `omega` Adversarial Soundness & Edge Cases
  // =========================================================================

  test("omega rejects false arithmetic/inequality claims (including truncated Nat subtraction!)") {
    val falseTheorems = List(
      "omega-reverse-le" -> "theorem t(a: Nat, b: Nat, h: Le(a, b)): Le(b, a) = by { omega }",
      "omega-le-to-lt" -> "theorem t(a: Nat, b: Nat, h: Le(a, b)): Lt(a, b) = by { omega }",
      "omega-slack-drop" -> "theorem t(a: Nat, b: Nat, h: Le(a, b + 1)): Le(a, b) = by { omega }",
      "omega-neq0-to-ge2" -> "theorem t(a: Nat, h: a !== 0): Le(2, a) = by { omega }",
      "omega-sum-eq-split" -> "theorem t(a: Nat, b: Nat, c: Nat, d: Nat, h: a + b === c + d): a === c = by { omega }",
      "omega-truncated-sub" -> "theorem t(a: Nat, b: Nat): (a - b) + b === a = by { omega }",
      "omega-consistent-to-false" -> "theorem t(a: Nat, b: Nat, h: Le(a, b)): False = by { omega }"
    )
    for ((label, thm) <- falseTheorems) {
      assertRejected(
        s"import Prelude.*\nimport Nat.*\nimport WellFounded.*\n$thm",
        None,
        label
      )
    }
  }

  test("omega safely handles opaque sub/mul atoms, nested And hyps, 0*x, and shadowed hyps") {
    val validEdgeCases =
      """
        |import Prelude.*
        |import Nat.*
        |import WellFounded.*
        |
        |theorem opaqueSubChain(a: Nat, b: Nat, c: Nat, d: Nat, h1: Le(a - b, c), h2: Le(c, d)):
        |  Le(a - b, d) = by {
        |  omega
        |}
        |
        |theorem nonlinearAtomChain(a: Nat, b: Nat, c: Nat, d: Nat, h1: Le(a * b, c), h2: Le(c, d)):
        |  Le(a * b, d) = by {
        |  omega
        |}
        |
        |theorem zeroMulBound(a: Nat, b: Nat): Le(0 * a, b) = by {
        |  omega
        |}
        |
        |theorem nestedAndHyps(a: Nat, b: Nat, c: Nat, d: Nat, h: Le(a, b) /\ (Le(b, c) /\ Lt(c, d))):
        |  Lt(a, d) = by {
        |  omega
        |}
        |
        |theorem shadowedHypOmega(a: Nat, b: Nat, c: Nat, hEq: a === b, h: Le(a + 1, c)):
        |  Le(b, c) = by {
        |  rewrite(hEq) in h
        |  omega
        |}
      """.stripMargin
    checkOkAxiomFree(validEdgeCases)
  }

  // =========================================================================
  // 3. `cc` Adversarial Soundness & Dependent-Type Safety
  // =========================================================================

  test("cc rejects false equalities (non-injective functions) and safely handles cycles & dependent Vec functions") {
    // Arbitrary function is NOT injective!
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |theorem fakeInj(f: Nat => Nat, a: Nat, b: Nat, h: f(a) === f(b)): a === b = by { cc }
      """.stripMargin,
      Some("T075"),
      "cc-non-injective-fn"
    )

    // Unrelated equalities cannot bridge
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |theorem unrelated(a: Nat, b: Nat, c: Nat, d: Nat, h1: a === b, h2: c === d): a === c = by { cc }
      """.stripMargin,
      Some("T075"),
      "cc-unrelated"
    )

    // Cyclic equalities + dependent Vec function in scope must NOT loop or crash!
    val trickyValid =
      """
        |import Prelude.*
        |import Nat.*
        |import Vec.*
        |
        |theorem ccCycle(a: Nat, b: Nat, c: Nat, h1: a === b, h2: b === c, h3: c === a): c === b = by {
        |  cc
        |}
        |
        |theorem ccWithDependentVecInScope(
        |  n: Nat,
        |  v1: Vec[Nat](n),
        |  v2: Vec[Nat](n),
        |  f: Vec[Nat](n) => Nat,
        |  h: v1 === v2
        |): f(v1) === f(v2) = by {
        |  cc
        |}
      """.stripMargin
    checkOkAxiomFree(trickyValid)
  }

  // =========================================================================
  // 4. `tauto` Intuitionistic Soundness & Non-Divergence
  // =========================================================================

  test("tauto rejects classical-only tautologies and terminates quickly on cyclic implications") {
    val classicalOnly = List(
      "tauto-lem" -> "theorem t(p: Prop): p \\/ ~p = by { tauto }",
      "tauto-dne" -> "theorem t(p: Prop): ~~p => p = by { tauto }",
      "tauto-peirce" -> "theorem t(p: Prop, q: Prop): ((p => q) => p) => p = by { tauto }",
      "tauto-rev-demorgan" -> "theorem t(p: Prop, q: Prop): ~(p /\\ q) => (~p \\/ ~q) = by { tauto }",
      "tauto-cyclic-unprovable" -> "theorem t(p: Prop, q: Prop, r: Prop, h1: p => q, h2: q => p): r = by { tauto }"
    )
    for ((label, thm) <- classicalOnly) {
      assertRejected(s"import Prelude.*\n$thm", Some("T076"), label)
    }
  }

  // =========================================================================
  // 5. Combinators & Ergonomic Tactics Edge Cases
  // =========================================================================

  test("combinators: repeat+try never diverges, invalid obtain/rename/in-hyp fail cleanly") {
    // `repeat { try { refl } }` makes no progress on `a === b` -> must terminate and fail cleanly on incomplete goal (not hang!)
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |theorem noHang(a: Nat, b: Nat): a === b = by {
        |  repeat { try { refl } }
        |}
      """.stripMargin,
      None,
      "repeat-try-no-hang"
    )

    // `obtain` on multi-constructor type (`Or`) must fail with T072
    assertRejected(
      """
        |import Prelude.*
        |theorem badObtain(p: Prop, q: Prop, h: p \/ q): p = by {
        |  obtain(x) = h
        |  exact(x)
        |}
      """.stripMargin,
      Some("T072"),
      "obtain-on-or"
    )

    // `rename` on missing hypothesis must fail with T073
    assertRejected(
      """
        |import Prelude.*
        |theorem badRename(p: Prop, h: p): p = by {
        |  rename(missingHyp, renamed)
        |  exact(h)
        |}
      """.stripMargin,
      Some("T073"),
      "rename-missing"
    )

    // `rewrite(...) in missing` must fail with T015
    assertRejected(
      """
        |import Prelude.*
        |import Nat.*
        |theorem badRewriteIn(a: Nat, b: Nat, hEq: a === b): a === a = by {
        |  rewrite(hEq) in missingHyp
        |  refl
        |}
      """.stripMargin,
      Some("T015"),
      "rewrite-in-missing"
    )
  }

  // =========================================================================
  // 6. All-5-Target Code Extraction Edge Cases (Empty Enum, 3-Way Mutual, Keywords)
  // =========================================================================

  test("extraction edge cases: empty Type enum, 3-way mutual recursion, keyword identifiers across all 5 targets") {
    val trickyExtract =
      """
        |import Prelude.*
        |import Nat.*
        |
        |enum EmptyData: Type {
        |}
        |
        |def elimEmpty[A](e: EmptyData): A = {
        |  e match {
        |  }
        |}
        |
        |mutual {
        |  def mod3Zero(n: Nat): Bool = {
        |    n match {
        |      case Nat.Zero => true
        |      case Nat.Succ(p) => mod3Two(p)
        |    }
        |  }
        |  def mod3One(n: Nat): Bool = {
        |    n match {
        |      case Nat.Zero => false
        |      case Nat.Succ(p) => mod3Zero(p)
        |    }
        |  }
        |  def mod3Two(n: Nat): Bool = {
        |    n match {
        |      case Nat.Zero => false
        |      case Nat.Succ(p) => mod3One(p)
        |    }
        |  }
        |}
        |
        |def trickyKeywords(typeArg: Nat, data: Nat, where: Nat, mod: Nat, fun: Nat, rec: Nat, end: Nat): Nat = {
        |  add(add(typeArg, data), add(add(where, mod), add(fun, add(rec, end))))
        |}
      """.stripMargin

    val env = checkOkAxiomFree(trickyExtract)
    val extracted = Erasure
      .extract(env, Erasure.ExtractionOptions("EdgeExtract", requireAxiomFree = true, requireTotal = true))
      .fold(err => fail(err), identity)

    val scalaCode = Scala3Emitter.emit(extracted)
    val tsCode = TsEmitter.emit(extracted)
    val jsCode = JsEmitter.emit(extracted)
    val hsCode = HaskellEmitter.emit(extracted)
    val mlCode = OCamlEmitter.emit(extracted)

    assert(scalaCode.contains("def mod3Zero") && scalaCode.contains("def mod3Two"))
    assert(tsCode.contains("export function mod3Zero"))
    assert(jsCode.contains("export function mod3Zero"))
    assert(hsCode.contains("data EmptyData") && hsCode.contains("mod3Zero :: Nat -> Bool"))
    assert(hsCode.contains("trickyKeywords typeArg data_ where_ mod fun rec_ end ="))
    assert(mlCode.contains("type emptyData = |"))
    assert(mlCode.contains("let rec mod3Zero (n : nat) : bool ="))
    assert(mlCode.contains("and mod3One (n : nat) : bool ="))
    assert(mlCode.contains("and mod3Two (n : nat) : bool ="))
    assert(mlCode.contains("let trickyKeywords (typeArg : nat) (data : nat) (where : nat) (mod_ : nat) (fun_ : nat) (rec_ : nat) (end_ : nat) : nat ="))
  }
}
