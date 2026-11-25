# Complete Guide to CoC & CIC: From Curry-Howard to the Trusted Kernel

From the outside, a proof assistant (Coq / Rocq, Lean, Agda, Proof Samurai) can feel like a black box — some mysterious engine that "knows math." Once you trace its foundation step by step through the **Curry-Howard Isomorphism**, the **Calculus of Constructions (CoC)**, and the **Calculus of Inductive Constructions (CIC)**, the mystery disappears completely: **there is no magic — the heart of a theorem prover is simply a tiny static type checker.**

This guide is written so that any programmer with **zero background in type theory** can read it from start to finish and walk away with a complete understanding of how proof checking works, why every soundness rule exists, and what actually happens behind a tactic script. Every single example corresponds directly to runnable Proof Samurai code and the real kernel in `src/main/scala/samurai/kernel/`.

---

## Part 0: The Big Picture — Why a Theorem Prover Is Not a Black Box

Modern proof assistants follow a single architectural principle called the **de Bruijn criterion**:

```text
  [Untrusted Frontend (Human / Tactics / AI)]
    Surface syntax / Tactics (omega, cc, tauto, simp, auto) / Elaborator
                          |
                          |  Searches, normalizes, and synthesizes
                          |  one concrete proof term (Core CIC Term)
                          v
  [Trusted Kernel (Trusted Computing Base = samurai.kernel)]
    Term (only 12 AST nodes) + TypeChecker + NbE + Positivity + Termination
                          |
                          |  Checks one question: "Does term t really have type T?"
                          v
                Accepted (KernelEnv) / Rejected (Error)
```

- **Tactics (`omega`, `simp`, `induction`, `auto`) and AI agents are never trusted.** They are just helper programs that assemble a candidate proof term.
- **Only the small kernel certifies truth.** Even if a tactic or elaborator contained a bug, any invalid proof term it produced would be rejected by the kernel's type checker before entering `KernelEnv`.

Understanding a theorem prover completely therefore comes down to four clear steps:

1. **The Curry-Howard Isomorphism**: propositions are types, proofs are terminating programs.
2. **CoC (Calculus of Constructions)**: unifying functions, generics, type constructors, and dependent types into one `Pi` construct.
3. **CIC (Calculus of Inductive Constructions)**: inductive types, dependent pattern matching (`motive`), equality `Eq`, and structural recursion (`Fix`).
4. **Conversion (NbE) & the Four Soundness Guards**: computation inside types and the four paradoxes blocked by the kernel.

Let us build all four from scratch.

---

## Part 1: The Curry-Howard Isomorphism — Propositions Are Types, Proofs Are Programs

In everyday programming, a type `A` describes a shape of data (`Int`, `String`), and a value `x : A` is an instance of that data. Now stretch that idea just slightly:

> **Treat a logical proposition `P` as a type. Then `P` is true (provable) if and only if you can write a terminating expression `pf : P` of that type.**

This is the **Curry-Howard isomorphism**. It is not a loose metaphor — the rules of logic and the typing rules of functional programming are **one and the same structure**.

### 1.1 Implication `P => Q` Is a Function

What does it mean to prove "if `P`, then `Q`" (`P => Q`)? It means writing **a function that takes any proof of `P` as input and returns a proof of `Q` as output**.

All four of these logical laws can be proved as plain functions with zero tactics:

```scala
import Prelude.*

// 1. Reflexivity: P => P is literally the identity function
def propId[P: Prop](p: P): P = { p }

// 2. Modus Ponens: from P and P => Q we get Q — literally function application!
def modusPonensTerm[P: Prop, Q: Prop](p: P, f: P => Q): Q = { f(p) }

// 3. Transitivity: (P => Q) and (Q => R) gives (P => R) — literally function composition!
def implTrans[P: Prop, Q: Prop, R: Prop](f: P => Q, g: Q => R): P => R = {
  (p: P) => g(f(p))
}

// 4. Weakening (K combinator): P => (Q => P) — ignore the second argument
def weaken[P: Prop, Q: Prop](p: P): Q => P = {
  (_: Q) => p
}
```

Notice the exact correspondence:
- **Assuming `P` to prove `Q` (Implication Introduction)** = **Lambda abstraction `(p: P) => ...`**
- **Modus Ponens (using `P => Q` on `P`)** = **Function application `f(p)`**

### 1.2 Conjunction `P /\ Q` Is a Pair (Product Type)

To prove "`P` and `Q`" (`P /\ Q`), you must supply **both** a proof of `P` and a proof of `Q`. That is simply a **2-element pair (tuple)**.

```scala
// Actual definition in stdlib/Prelude.samurai
enum And[Left: Prop, Right: Prop]: Prop {
  case Intro(leftProof: Left, rightProof: Right)
}

// Proof of (P /\ Q) => (Q /\ P) = swapping the two components of a pair!
def andCommTerm[P: Prop, Q: Prop](h: P /\ Q): Q /\ P = {
  h match {
    case And.Intro(hp, hq) => And.Intro[Q, P](hq, hp)
  }
}
```

- **Building `P /\ Q` (Introduction)** = calling constructor `And.Intro(hp, hq)`
- **Using `P /\ Q` (Elimination)** = pattern matching to extract `hp` and `hq`

### 1.3 Disjunction `P \/ Q` Is a Tagged Union (`Either` / Sum Type)

To prove "`P` or `Q`" (`P \/ Q`), you provide **either** a proof of `P` tagged `Inl`, **or** a proof of `Q` tagged `Inr`. Conversely, to *use* an assumption `h : P \/ Q`, your `match` must handle **both** cases. That is identical to `Either` in Scala/Haskell/Rust.

```scala
// Actual definition in stdlib/Prelude.samurai
enum Or[Left: Prop, Right: Prop]: Prop {
  case Inl(leftProof: Left)
  case Inr(rightProof: Right)
}

// Proof of (P \/ Q) => (Q \/ P) = flipping the tag!
def orCommTerm[P: Prop, Q: Prop](h: P \/ Q): Q \/ P = {
  h match {
    case Or.Inl(hp) => Or.Inr[Q, P](hp)
    case Or.Inr(hq) => Or.Inl[Q, P](hq)
  }
}
```

### 1.4 Truth `True` Is `Unit`, Falsehood `False` Is the Empty Type (0 Constructors)

This is one of the cleanest ideas in all of computer science:

```scala
// Actual definitions in stdlib/Prelude.samurai
enum True: Prop {
  case Intro      // 1 constructor with no arguments: always constructible (always true)
}

enum False: Prop {
  // 0 constructors! No terminating expression can ever produce a value of False.
}
```

What happens when you `match` on a value of an empty type `False`? **Zero branches are already exhaustive!**

```scala
// Principle of Explosion (Ex Falso Quodlibet): from False, any proposition P follows
def exFalsoTerm[P: Prop](absurd: False): P = {
  absurd match {}   // 0 constructors => 0 branches covers every possible case!
}
```

### 1.5 Negation `~P` Is `P => False`

Negation needs no special primitive at all. Saying "`P` is false" means: **"give me any proof of `P`, and I will hand you back the impossible (`False`)."**

```scala
// stdlib/Prelude.samurai
def Not(P: Prop): Prop = { P => False }

// Contrapositive: (P => Q) => (~Q => ~P) is just function composition!
def contrapositiveTerm[P: Prop, Q: Prop](f: P => Q): (~Q) => (~P) = {
  (notQ: Q => False) => (p: P) => notQ(f(p))
}

// Double negation introduction: P => ~~P
def doubleNegIntroTerm[P: Prop](p: P): ~(~P) = {
  (notP: P => False) => notP(p)
}
```

### 1.6 Constructive (Intuitionistic) Logic vs. Classical Logic

Beginners often ask: why can we prove `P => ~~P` in one line, while **Double Negation Elimination (`~~P => P`)** and the **Law of Excluded Middle (`P \/ ~P`)** cannot be proved without an extra axiom?

Read them as programs and the answer is immediate:

- A proof of `forall (P: Prop) => P \/ ~P` would have to be a **computable function** that, for *every* proposition `P` (even "does Turing machine `M` halt?"), decides whether to return `Or.Inl(proofOfP)` or `Or.Inr(refutationOfP)`. No such algorithm exists.
- Likewise, `~~P` only says "assuming `P => False` leads to a contradiction"; it does not hand you a concrete witness of `P`.

A logic where every proof must construct concrete evidence is called **constructive (intuitionistic) logic**. Its payoff is huge: **proofs carry genuine computational content and can be extracted to runnable code.** (Of course, for decidable properties like `Nat` equality or ordering, `n === m \/ n !== m` IS provable with 0 axioms!)

### 1.7 Why "Isomorphism" (Not Just Correspondence): Proof Normalization = Execution

Curry-Howard is an *isomorphism* because it matches not only **propositions ↔ types** and **proofs ↔ programs**, but also **eliminating detours in a proof ↔ evaluating a program (`β`/`ι`-reduction)**.

Constructing a pair and immediately unpacking its left component:

```scala
(And.Intro[P, Q](hp, hq)) match {
  case And.Intro(x, _) => x
}
```

reduces directly to `hp`. Applying a helper lemma `((p: P) => body)(hp)` reduces to `body[p := hp]`. **Running a program literally simplifies the corresponding proof.**

### Part 1 Summary Table

| Logic | Type Theory / Code | Introduction (Build) | Elimination (Use) |
|---|---|---|---|
| Proposition `P` | Type `P : Prop` | Type definition | Type checking |
| Proof `pf` | Value `pf : P` | Expression | Evaluation |
| Implication `P => Q` | Function type `P => Q` | Lambda `(p: P) => ...` | Application `f(p)` |
| Conjunction `P /\ Q` | Pair `And[P, Q]` | `And.Intro(hp, hq)` | `match` |
| Disjunction `P \/ Q` | Tagged union `Or[P, Q]` | `Or.Inl` / `Or.Inr` | Exhaustive `match` |
| Truth `True` | Unit `True` | `True.Intro` | (no info) |
| Falsehood `False` | Empty `False` | (impossible) | Empty `match {}` |
| Negation `~P` | `P => False` | `(p: P) => ... : False` | `notP(p) : False` |

---

## Part 2: The Lambda Cube & CoC — Unifying Four Worlds into One `Pi`

Part 1 covered **propositional logic** (treating `P` and `Q` as atomic). Real programs and mathematics need **predicate logic** ("for every natural number `n`, `n + 0 === n`") and types that depend on values.

Henk Barendregt organized how type systems grow along the four axes of the **Lambda Cube**:

### 2.1 The Four Axes of Abstraction

Any function in a typed language takes an input (a **term** or a **type**) and returns an output (a **term** or a **type**). There are exactly four combinations:

| Axis | Input → Output | Concrete Programming Example | Classic System / Languages |
|---|---|---|---|
| 1 | **Term → Term** | `(n: Nat) => n + 1` (ordinary function) | Simply Typed Lambda Calculus (`λ→`) |
| 2 | **Type → Term** | `[A: Type](x: A) => x` (generics / polymorphism) | System F (`λ2`) / ML, Rust, Java |
| 3 | **Type → Type** | `List : Type => Type` (type constructor / HKT) | System `F_ω` (`λω`) / Haskell, Scala |
| 4 | **Term → Type** | `Vec[A](n)` or `n + 0 === n` (**dependent types**) | `λP` (LF) / Dependent type systems |

Plotting axes 2, 3, and 4 as the three dimensions of a cube gives the **Lambda Cube**:

```text
               λω (Type→Type) ------------ λC = CoC (All 4 axes unified!)
              /|                          /|
             / |                         / |
            /  |                        /  |
          λ2 (Type→Term) ------------ λP2  |
          |    |                      |    |
          |   λ_ω (Type→Type only) ---|--- λPω
          |   /                       |   /
          |  /                        |  /
          | /                         | /
          λ→ (Term→Term only) ------- λP (Term→Type: Dependent types)
```

The top-back corner **`λC`** is the **Calculus of Constructions (CoC)**, invented by Thierry Coquand and Gérard Huet (1988).

### 2.2 What Is a Dependent Type?

In an ordinary function `Nat => List[Nat]`, the return type `List[Nat]` is fixed whether you pass `3` or `100`.
In a **dependent function**, **the return type can mention the argument value `n` itself**:

- Length-indexed vectors: `zeros(n: Nat): Vec[Nat](n)`
  - `zeros(3)` has type `Vec[Nat](3)`
  - `zeros(5)` has type `Vec[Nat](5)`
- Universal quantification: `addZeroRight(n: Nat): n + 0 === n`
  - `addZeroRight(3)` has type `3 + 0 === 3`
  - `addZeroRight(5)` has type `5 + 0 === 5`

This type — a function whose return type `B(x)` may depend on the input value `x: A` — is called the **Dependent Product Type**, written `Π(x: A). B(x)` in math and **`forall (x: A) => B(x)`** in Proof Samurai.

### 2.3 CoC's Grand Unification: One `Term.Pi` Replaces Six Features

CoC removes the syntactic wall between terms and types so that all four axes of the Lambda Cube collapse into **one single AST node: `Term.Pi(name, domain, codomain)`**:

| Concept | Exact `Term.Pi` Representation | Key Property |
|---|---|---|
| Ordinary function `Nat => Bool` | `Pi("_", Nat, Bool)` | `codomain` does not mention the parameter |
| Logical implication `P => Q` | `Pi("_", P, Q)` | Both `domain` and `codomain` are in `Prop` |
| Polymorphic function `[A](x: A) => x` | `Pi("A", Type0, Pi("x", A, A))` | `domain` is `Type0` |
| Type constructor `List` | `Pi("_", Type0, Type0)` | Maps `Type0` to `Type0` |
| Predicate `IsEven` | `Pi("_", Nat, Prop)` | Maps a runtime value `Nat` to a proposition `Prop` |
| Universal quantifier `∀n:Nat. n + 0 = n` | `Pi("n", Nat, Eq(add(n, 0), n))` | `codomain` depends on value `n` |

Six seemingly separate language features are literally the **same single construct** inside the kernel.

### 2.4 Existentials & Certified Data: Dependent Pairs (`Σ` / `Exists` / `Subset`)

While universal quantification `∀` is a dependent function (`Π`), existential quantification `∃x:A. P(x)` is a **dependent pair (`Σ`)**: a value `w: A` paired with a proof `proof: P(w)` about that specific `w`.

Proof Samurai provides both a logical (`Prop`) and a computational (`Type`) version in `stdlib/Prelude.samurai`:

```scala
// 1. Logical existential (Prop): used inside proofs; completely erased (0 bytes) on extraction
enum Exists[Domain: Type, Predicate: Domain => Prop]: Prop {
  case Intro(witness: Domain, proof: Predicate(witness))
}

// 2. Certified runtime value (Type): value stays at runtime; proof field is erased!
enum Subset[Domain: Type, Predicate: Domain => Prop]: Type {
  case Mk(value: Domain, proof: Predicate(value))
}
```

### 2.5 Pure Type Systems & the Three-Line `piSort` Rule

Which universe (`Prop`, `Type0`, `Type1`, ...) does `Pi(x: A, B)` itself live in? Given `A : s1` and `B : s2`, [Term.scala](https://github.com/kmizu/proof-samurai/blob/main/src/main/scala/samurai/kernel/Term.scala) decides it in literally **three lines**:

```scala
def piSort(codSort: Sort): Sort = (this, codSort) match {
  case (_, Sort.Prop)              => Sort.Prop                 // Impredicative Prop
  case (Sort.Prop, Sort.Type(j))   => Sort.Type(j)              // Function from proof to data
  case (Sort.Type(i), Sort.Type(j))=> Sort.Type(math.max(i, j)) // Predicative Type hierarchy
}
```

Whenever `B` is a `Prop`, quantifying over *anything* (`Nat`, `Type0`, or `Prop`) stays inside `Prop` (**impredicativity of `Prop`**). Whenever `B` is in `Type(j)`, the result lives in `Type(max(i, j))`.

---

## Part 3: Why CoC Alone Isn't Enough → CIC (Inductives, `motive`, `Eq`, Induction)

Pure CoC is breathtakingly minimal, yet it hits a wall in practice.

### 3.1 The Limit of Pure CoC (Church Encodings)

In pure CoC you can encode natural numbers as `ChurchNat = forall (X: Type) => (X => X) => X => X`, and write `+` and `*`. However:

1. **You cannot even prove `0 !== 1`** (Peano's fourth axiom) without adding extra axioms.
2. **You cannot derive mathematical induction** for `ChurchNat` inside pure CoC.

**CIC (Calculus of Inductive Constructions)** solves this permanently by making **Inductive Types (`enum`)**, **dependent pattern matching (`Match`)**, and **structural recursion (`Fix`)** first-class primitives. Every logical connective (`False`, `True`, `And`, `Or`, `Eq`, `Exists`, `Acc`) and every data structure (`Nat`, `List`, `Vec`, `Tree`, `IO`) is defined with the exact same mechanism — **zero built-in axioms**.

### 3.2 Parameters vs. Indices

An `enum` in CIC can take two kinds of arguments:

- **Parameters (`[...]`)**: fixed and identical across every constructor.
- **Indices (`(...)`)**: may vary from constructor to constructor, forming an **Inductive Family**.

```scala
// Parameters only: Element is identical for Nil and Cons
enum List[Element: Type]: Type {
  case Nil
  case Cons(head: Element, tail: List[Element])
}

// Parameter Element + Index size: Nat (Nil has size 0; Cons has size Succ(tailSize))
enum Vec[Element: Type](size: Nat): Type {
  case Nil: Vec[Element](Nat.Zero)
  case Cons(tailSize: Nat, head: Element, tail: Vec[Element](tailSize)): Vec[Element](Nat.Succ(tailSize))
}

// Parameters A, left + Index right: A (Refl forces right to equal left!)
enum Eq[A: Type, left: A](right: A): Prop {
  case Refl: Eq[A, left](left)
}
```

### 3.3 Understanding Dependent `Match` and the `motive`

The `motive` is the #1 concept that makes CIC click.

In ordinary languages, every branch of a `match` must return the **same** type `R`.
In CIC, `Match` takes a **motive function `M`** that computes **a potentially different expected return type for each branch** from the matched constructor and indices:

- Non-dependent `match`: `motive = (_: Nat) => Bool` (every branch returns `Bool`).
- Dependent `match`: `motive = (k: Nat) => k + 0 === k`:
  - `case Nat.Zero` must return `motive(Nat.Zero)` = `0 + 0 === 0`.
  - `case Nat.Succ(pred)` must return `motive(Nat.Succ(pred))` = `Nat.Succ(pred) + 0 === Nat.Succ(pred)`.

#### Live Demo: Proving `0 !== 1` (`discriminate`) from Scratch with 0 Axioms

How does CIC prove `0 !== 1` without a single axiom? By combining **large elimination** (a function from `Nat` into `Prop`) with **dependent `Match` on `Eq`**:

```scala
import Prelude.*
import Nat.*

// Step 1: Map Zero -> True and Succ(_) -> False
def isZeroProp(n: Nat): Prop = {
  n match {
    case Nat.Zero    => True
    case Nat.Succ(_) => False
  }
}

// Step 2: Specify the motive via `returning (...)` and transport True.Intro : isZeroProp(0)
//         along h : 0 === 1 to obtain isZeroProp(1) = False!
def zeroNeqOneFromScratch(h: 0 === 1): False = {
  // Motive: (y: Nat, _: Eq[Nat, 0](y)) => isZeroProp(y)
  //   - In case Eq.Refl, expected type is isZeroProp(0) = True  -> satisfied by True.Intro!
  //   - Whole match has type isZeroProp(1) = False!
  h match returning ((y: Nat, _: Eq[Nat, 0](y)) => isZeroProp(y)) {
    case Eq.Refl => True.Intro
  }
}
```

There is no magic behind `discriminate` or `vecHead`'s unreachable `Vec.Nil` branch — the elaborator simply generates this exact `Match` + motive and hands it to the kernel!

### 3.4 Equality `Eq` (Paulin-Mohring Identity Type) and `rewrite`

From the 1-constructor definition `enum Eq[A: Type, left: A](right: A): Prop { case Refl: Eq[A, left](left) }`, **every law of equality follows with 0 axioms**:

```scala
// Core substitution / Leibniz transport (literally a dependent Match on Eq)
def eqSubst[A: Type](P: A => Prop, x: A, y: A, eqProof: Eq[A, x](y), px: P(x)): P(y) = {
  eqProof match returning ((z: A, _: Eq[A, x](z)) => P(z)) {
    case Eq.Refl => px   // In the Refl branch z = x, so P(x) IS P(z)!
  }
}

// Symmetry (x === y => y === x)
def eqSymTerm[A: Type](x: A, y: A, h: x === y): y === x = {
  eqSubst[A]((z: A) => z === x, x, y, h, Eq.Refl[A, x])
}

// Transitivity (x === y => y === z => x === z)
def eqTransTerm[A: Type](x: A, y: A, z: A, h1: x === y, h2: y === z): x === z = {
  eqSubst[A]((w: A) => x === w, y, z, h2, h1)
}

// Congruence (x === y => f(x) === f(y))
def eqCongrTerm[A: Type, B: Type](f: A => B, x: A, y: A, h: x === y): f(x) === f(y) = {
  eqSubst[A]((w: A) => f(x) === f(w), x, y, h, Eq.Refl[B, f(x)])
}
```

`symmetry`, `trans`, `congr`, and `rewrite` tactics simply build calls to this `Match` on `Eq`.

### 3.5 Mathematical Induction = Structural Recursion (`Fix`) + Dependent `Match`

Mathematical induction is not an extra axiom either — **an inductive proof is literally a structurally recursive function calling itself on smaller subterms**:

```scala
// Proof of n + 0 === n written directly as a recursive function (no tactics!)
def addZeroRightDirect(n: Nat): n + 0 === n = {
  n match returning ((k: Nat) => k + 0 === k) {
    case Nat.Zero =>
      Eq.Refl[Nat, Nat.Zero]
    case Nat.Succ(pred) => {
      // The induction hypothesis (IH) is literally the recursive call on pred!
      val ih: pred + 0 === pred = addZeroRightDirect(pred)
      eqCongrTerm[Nat, Nat]((k: Nat) => Nat.Succ(k), pred + 0, pred, ih)
    }
  }
}
```

Proof Samurai's CIC also supports **higher-order inductives** — constructors with function-valued recursive fields such as `Acc.Intro` (for 0-axiom well-founded recursion) and `IO.ReadNat(cont: Nat => IO[Result])` (for 0-axiom verified IO).

---

## Part 4: Computation Inside Types — Definitional vs. Propositional Equality & NbE

Every newcomer encounters this puzzle on Day 1:

- `theorem leftZero(n: Nat): 0 + n === n = by { refl }` succeeds with **`refl` alone**.
- `theorem rightZero(n: Nat): n + 0 === n = by { refl }` **fails** and requires `induction(n)`!

Understanding *why* makes theorem proving effortless.

### 4.1 Definitional Equality (`≡`) vs. Propositional Equality (`===`)

Look at how `add` is defined in `stdlib/Nat.samurai`:

```scala
def add(left: Nat, right: Nat): Nat = {
  left match {
    case Nat.Zero       => right
    case Nat.Succ(pred) => Nat.Succ(add(pred, right))
  }
}
```

`add` pattern-matches on its **first** argument `left`:

1. **`add(0, n)`**: `left` is the concrete constructor `Nat.Zero`, so the kernel immediately computes `add(0, n) -> n`. Thus `0 + n` and `n` are **definitionally equal (`0 + n ≡ n`)**, and `Eq.Refl` closes `0 + n === n` automatically.
2. **`add(n, 0)`**: `left` is an abstract variable `n`, so the `match` is **stuck (neutral)** — the kernel cannot tell whether `n` is `Zero` or `Succ`. Therefore `n + 0` and `n` are NOT definitionally equal; you must prove **propositional equality (`n + 0 === n`)** by splitting on `n` with `induction(n)`.

| Kind | Notation | Verified By | Examples |
|---|---|---|---|
| **Definitional equality** | `A ≡ B` | Automatically by kernel computation (NbE) | `2 + 2 ≡ 4`, `0 + n ≡ n`, `((x) => x)(3) ≡ 3` |
| **Propositional equality** | `a === b` (`Eq`) | Explicit proof term (`Eq`) built by user/tactics | `n + 0 === n`, `a + b === b + a`, `reverse(reverse(xs)) === xs` |

### 4.2 The Conversion Rule (`[Conv]`)

```text
  Γ ⊢ t : A      A ≡ B (equal via NbE, or cumulativity A ⪯ B)
  -----------------------------------------------------------  [Conv]
                            Γ ⊢ t : B
```

Because of `[Conv]`, a term of type `Vec[Nat](2 + 2)` seamlessly type-checks where `Vec[Nat](4)` is expected.

### 4.3 How NbE (`NbE.scala`) Computes `A ≡ B`

Rather than slow, error-prone syntactic substitution, [NbE.scala](https://github.com/kmizu/proof-samurai/blob/main/src/main/scala/samurai/kernel/NbE.scala) uses **Normalization by Evaluation**:

1. **Evaluate (`Term -> Value`)**: evaluate de Bruijn terms into semantic values using Scala closures and an environment (`EvalEnv`), keeping stuck expressions as `VNeutral(head, spine)`.
2. **Read back / Compare (`quote` / `isDefEq`)**: compare values structurally (comparing functions by applying both to a fresh variable `NVar(level)`).

`NbE.scala` applies exactly six reductions:

| Reduction | Symbol | Behavior |
|---|---|---|
| Beta | `β` | Evaluate `((x) => body)(arg)` by extending the environment with `x -> arg` |
| Zeta | `ζ` | Unfold `Let(x, ty, v, body)` with `x -> eval(v)` |
| Delta | `δ` | Unfold transparent `def` bodies (`partial def` and `axiom` are never unfolded) |
| Iota | `ι` | Reduce `Match` when scrutinee evaluates to a constructor `VCtor` |
| Fixpoint | `fix` | Unfold `Fix` / `MutualFix` **only when the decreasing argument is a constructor `VCtor`** |
| Proof Irrelevance | `PI` | Treat any two proofs `pf1, pf2 : P` of the same `P : Prop` as equal |

Guarding `fix` unfolding on `VCtor` guarantees that normalization during type checking always terminates.

---

## Part 5: The Entire Kernel — All 12 `Term` Nodes & Typing Rules

Every surface feature (`do { ... }`, `calc { ... }`, `case class`, `if`, nested matches, `termination_by`, and all tactics) compiles down to just **12 AST constructors** in [Term.scala](https://github.com/kmizu/proof-samurai/blob/main/src/main/scala/samurai/kernel/Term.scala):

```scala
enum Term {
  // --- CoC core (7 nodes) ---
  case USort(sort: Sort)                                   // Prop, Type0, Type1, ...
  case Var(idx: Int)                                       // De Bruijn index variable
  case Const(name: String)                                 // Checked def / theorem / axiom
  case Pi(name: String, domain: Term, codomain: Term)      // Dependent product forall (x: A) => B
  case Lam(name: String, domain: Term, body: Term)         // Lambda abstraction (x: A) => body
  case App(fn: Term, arg: Term)                            // Function application fn(arg)
  case Let(name: String, ty: Term, value: Term, body: Term)// Local let binding

  // --- CIC inductive extension (5 nodes) ---
  case Ind(name: String)                                   // Inductive type (Nat, List, Eq, Acc, IO, ...)
  case Ctor(indName: String, ctorName: String)             // Constructor (Nat.Succ, Eq.Refl, ...)
  case Match(indName: String, params: List[Term], motive: Term, scrutinee: Term, branches: List[MatchBranch])
  case Fix(name: String, recArgIdx: Int, ty: Term, body: Term)     // Structural recursion
  case MutualFix(defs: List[MutualFixDef], selectedIndex: Int)     // Mutual structural recursion
}
```

### 5.1 De Bruijn Indices by Example

Variables are stored as 0-based distances `Var(idx)` to their enclosing binder:

- `(x: Nat) => x` becomes `Lam("x", Nat, Var(0))`
- `(x: Nat) => (y: Nat) => x` becomes `Lam("x", Nat, Lam("y", Nat, Var(1)))`
- `(a: Nat) => (b: Nat) => a` becomes `Lam("a", Nat, Lam("b", Nat, Var(1)))`

Display names are ignored by `Term.alphaEq`, so variable capture is impossible and alpha-equivalence is simple structural equality.

### 5.2 How to Read Typing Rules (`Γ ⊢ t : A`)

You only need three symbols to read any inference rule in type theory:

- **`Γ` (context)**: the list of local variables and hypotheses currently in scope (e.g. `n : Nat, h : n === 0`).
- **`Γ ⊢ t : A` (judgment)**: "under context `Γ`, term `t` has type `A`."
- **Horizontal bar**: "if everything **above** the line holds, then the conclusion **below** the line holds."

### 5.3 Core Typing Rules (`TypeChecker.scala`)

```text
  [Sort]   ----------------------           ----------------------------
             Γ ⊢ Prop : Type(0)               Γ ⊢ Type(i) : Type(i + 1)

  [Var]       (x : A) ∈ Γ
           -----------------
              Γ ⊢ x : A

  [Pi]     Γ ⊢ A : s1        Γ, x:A ⊢ B : s2
           ----------------------------------
              Γ ⊢ Π(x: A). B : piSort(s1, s2)

  [Lam]    Γ ⊢ A : s         Γ, x:A ⊢ b : B
           ----------------------------------
              Γ ⊢ (x: A) => b : Π(x: A). B

  [App]    Γ ⊢ f : Π(x: A). B      Γ ⊢ a : A
           ----------------------------------
                 Γ ⊢ f(a) : B[x := a]

  [Let]    Γ ⊢ A : s    Γ ⊢ v : A    Γ, x:A := v ⊢ b : B
           ----------------------------------------------
             Γ ⊢ (val x: A = v; b) : B[x := v]

  [Conv]   Γ ⊢ t : A        A ⪯ B  (NbE equivalence or Type(i) <= Type(j))
           ----------------------------------------------------------------
                                      Γ ⊢ t : B
```

Plus the two CIC inductive rules:

- **`[Match]`**: checks exhaustiveness (`K026`), subsingleton safety for `Prop -> Type` (`K025`), and each branch against `motive(ctorIndices, Ctor(fields))`, typing the whole expression as `motive(indices, scrutinee)`.
- **`[Fix]` / `[MutualFix]`**: checks well-typedness of the signature and body plus the structural decreasing guard in `Termination.scala` (`K020`).

That is the entire trusted kernel — zero hidden heuristics.

---

## Part 6: Why the Four Soundness Guards Exist (Concrete Paradoxes)

Every strict kernel error (`K005`, `K006`, `K020`, `K025`, `K030`, `K031`) blocks a concrete way to forge a proof of `False`.

### Guard 1: Universe Stratification (`K005` — Blocks Girard's Paradox)

Allowing `Type : Type` lets you reproduce Russell's paradox inside type theory (**Girard's paradox, 1972**) and inhabit `False`.

CIC stratifies universes as `Prop : Type0 : Type1 : Type2 : ...` with cumulativity (`Type(i) <= Type(j)` for `i <= j`) and predicativity for `Type(k)` inductives (storing a `Type0` field inside a `Type0` inductive is rejected with `K005`; raise the enum to `: Type1` instead).

### Guard 2: Strict Positivity (`K006` — Blocks Curry's Paradox)

If an inductive type `Bad` is allowed to appear to the left of `=>` (a **negative / contravariant position**) in its own constructor, you can prove `False` **without using recursion (`Fix`) at all**:

```scala
// Negative inductive type — rejected by Positivity.scala with K006
enum Bad: Prop {
  case Mk(selfApply: Bad => False)
}

// If allowed, self-application loops forever and inhabits False:
def unroll(b: Bad): False = {
  b match {
    case Bad.Mk(f) => f(b)
  }
}

def paradox: False = {
  unroll(Bad.Mk(unroll))
}
```

Compare safe vs. unsafe positions:
- **Strictly positive (Safe)**: `IO.ReadNat(cont: Nat => IO[Result])` and `Acc.Intro(cur, step: forall y => Rel(y, cur) => Acc(y))` — the inductive only appears on the **right** of `=>`.
- **Negative (Unsafe, `K006`)**: `Bad => False` or `(Bad => False) => False` — `Positivity.scala` expands transparent aliases like `Not(Bad)` via NbE first so hidden negative occurrences are caught too.

### Guard 3: Termination Checking (`K020`), Well-Founded `Acc`, and `partial def` (`K030`/`K031`)

Unrestricted recursion immediately proves every false statement:

```scala
// Non-terminating fake proof — rejected by Termination.scala with K020
def loop(n: Nat): False = { loop(n) }
```

Curry-Howard requires every proof to terminate in finitely many steps. Proof Samurai supports three cleanly separated layers:

1. **Structural & mutual structural recursion (`Fix` / `MutualFix`)**: recursive calls must pass a strictly smaller pattern-matched subterm (`pred`, `tail`, `k(n)`).
2. **Well-founded recursion (`termination_by` + `Acc`, `stdlib/WellFounded.samurai`)**: algorithms like `quickSort`, `gcd`, and `divNat` desugar to structural recursion on the 0-axiom accessibility predicate `Acc[A, R](x)`. Unpacking `Acc.Intro(x, step)` yields `step(y, hSmaller)`, which is structurally smaller than the input `Acc`, so the kernel checks general well-founded recursion with 0 axioms — and erases `Acc` completely on extraction.
3. **Isolated `partial def`**: computational functions without a termination proof (like `collatzSteps`) can be marked `partial def`, but cannot return `Prop` (`K030`), are never unfolded by NbE, and cannot be referenced by any total `def` or `theorem` (`K031`).

### Guard 4: `Prop` vs. `Type` and Subsingleton Elimination (`K025`)

Separating `Prop` from `Type` gives us three properties simultaneously: **0-byte proof erasure**, **proof irrelevance**, and **impredicativity**.

If matching on a 2-constructor `Prop` (like `Or[True, True]`) could produce a `Bool : Type`:

```scala
// Rejected by Proof Samurai with K025
def leak(h: True \/ True): Bool = {
  h match {
    case Or.Inl(_) => true
    case Or.Inr(_) => false
  }
}
// By proof irrelevance, Or.Inl(True.Intro) ≡ Or.Inr(True.Intro),
// which would yield true === false! And erasing `h` would break runtime execution!
```

Therefore `Prop -> Type` elimination is allowed **only for subsingletons**:

| `Prop` Inductive | Constructors | `Prop -> Type` Allowed? | Reason |
|---|---|---|---|
| `False` | 0 | **Yes** | Unreachable at runtime |
| `True` | 1 (no fields) | **Yes** | Always one branch |
| `Eq` | 1 (`Refl`) | **Yes** | Always one branch; enables indexed transport |
| `Acc` | 1 (`Intro`, all fields `Prop` or index-forced) | **Yes** | Zero computational content; erases cleanly |
| `Or`, `Exists` | 2, or holds a `Type` witness | **No (`K025`)** | Would leak proof choices into runtime data (use `Either` / `Subset` instead) |

---

## Part 7: Inside the Tactic Engine & End-to-End Trace

### 7.1 Tactics Are an LCF-Style Hole Filler

In [Tactics.scala](https://github.com/kmizu/proof-samurai/blob/main/src/main/scala/samurai/tactic/Tactics.scala), `ProofState` holds just two things:

1. `openGoals: List[ProofGoal]` — remaining holes, each with `(localCtx Γ, targetType T)`.
2. `extractProof: Map[GoalId, Term] => Term` — a closure that assembles the complete core CIC `Term` once every hole is solved.

Every tactic simply wraps a piece of core AST around the remaining holes:
- `intro(x)` wraps `Lam("x", dom, ?subgoal)`
- `split` wraps `And.Intro(?left, ?right)`
- `rewrite(h)` wraps `Match("Eq", ..., h, [Refl => ?rewritten])`
- `induction(n)` wraps `Fix(..., Lam(n, Match("Nat", motive, n, [Zero => ?g0, Succ(pred) => ?g1])))`
- `omega` / `arith` / `cc` / `tauto` search automatically and emit a **0-axiom core CIC `Term`**.

### 7.2 End-to-End Trace: `addZeroRight`

#### Step 1: Surface Script

```scala
theorem addZeroRight(n: Nat): n + 0 === n = by {
  induction(n) {
    case Zero => { refl }
    case Succ(pred, ih) => {
      simp
      rewrite(ih)
      refl
    }
  }
}
```

#### Step 2: Goal Progression

1. Start: `n : Nat ⊢ n + 0 === n`
2. After `induction(n)`:
   - Goal #1 (`Zero`): `⊢ 0 + 0 === 0`
   - Goal #2 (`Succ`): `pred : Nat, ih : pred + 0 === pred ⊢ Nat.Succ(pred) + 0 === Nat.Succ(pred)`
3. `refl` closes Goal #1 because `0 + 0 ≡ 0` via NbE.
4. `simp` reduces `Nat.Succ(pred) + 0` to `Nat.Succ(pred + 0)`.
5. `rewrite(ih)` wraps a `Match` on `Eq`, rewriting the goal to `Nat.Succ(pred) === Nat.Succ(pred)`.
6. `refl` closes Goal #2 with `Eq.Refl[Nat, Nat.Succ(pred)]`.

#### Step 3: Final Core CIC Term Sent to the Kernel

```scala
Fix(
  name = "addZeroRight",
  recArgIdx = 0,
  ty = Pi(n: Nat, Eq[Nat, add(n, Nat.Zero)](n)),
  body = Lam(n: Nat,
    Match(
      indName = "Nat",
      motive = Lam(k: Nat, Eq[Nat, add(k, Nat.Zero)](k)),
      scrutinee = n,
      branches = [
        case Zero =>
          Eq.Refl[Nat, Nat.Zero],
        case Succ(pred) =>
          Match(
            indName = "Eq",
            motive = Lam(y: Nat, Lam(_: Eq[Nat, add(pred, Nat.Zero)](y),
                       Eq[Nat, Nat.Succ(add(pred, Nat.Zero))](Nat.Succ(y)))),
            scrutinee = addZeroRight(pred),
            branches = [ case Refl => Eq.Refl[Nat, Nat.Succ(add(pred, Nat.Zero))] ]
          )
      ]
    )
  )
)
```

#### Step 4: Kernel Checks

1. **Type checking (`TypeChecker` + `NbE`)**: verifies every branch against the motive under `[Conv]`.
2. **Exhaustiveness (`K026`)**: confirms `Nat.Zero`, `Nat.Succ`, and `Eq.Refl` are all covered.
3. **Termination (`Termination` / `K020`)**: confirms `pred` is a structurally smaller subterm of `n`.
4. **Axiom tracking (`Env`)**: records 0 axioms and 0 `sorry` in `KernelEnv`.

#### Step 5: Extraction (`Erasure`)

Because `addZeroRight` returns a `Prop`, `Erasure.scala` erases it completely — 0 bytes in extracted Scala 3, TypeScript, JavaScript, Haskell, or OCaml output.

---

## Part 8: Quick Glossary

| Term | One-Line Definition |
|---|---|
| **TCB (Trusted Computing Base)** | The minimal core whose correctness is trusted — in Proof Samurai, only `samurai.kernel`. |
| **de Bruijn Criterion** | Separating untrusted proof search from a small trusted kernel that checks the final proof term. |
| **Curry-Howard Isomorphism** | Propositions = types, proofs = terminating programs, proof simplification = evaluation. |
| **Judgment `Γ ⊢ t : A`** | Under context (hypotheses) `Γ`, term `t` has type `A`. |
| **Dependent Product `Pi` (`Π(x: A). B`)** | Function type whose return type `B` may depend on argument `x`; unifies `=>`, generics, and `forall`. |
| **Dependent Pair `Sigma` (`Σ(x: A). B`)** | A value `x` paired with a property `B(x)` about it (`Exists` in `Prop`, `Subset` in `Type`). |
| **Sort / Universe** | The type of a type (`Prop : Type0 : Type1 : ...`), stratified to prevent paradoxes. |
| **Impredicativity** | Quantifying over all propositions (`forall (P: Prop) => ...`) produces another `Prop`. |
| **Parameter vs. Index** | Inductive arguments fixed across all constructors (parameters) vs. varying per constructor (indices). |
| **Motive** | Function in a dependent `Match` computing each branch's expected return type from its constructor/indices. |
| **Definitional (`≡`) vs. Propositional (`===`)** | Equal by computation alone (`refl`) vs. requiring an explicit `Eq` proof term. |
| **NbE (Normalization by Evaluation)** | Evaluating terms into semantic closures and reading back / comparing them for fast conversion checking. |
| **De Bruijn Index** | Representing variables as 0-based binder distances to prevent capture and trivialize alpha-equivalence. |
| **Strict Positivity** | Forbidding an inductive type from appearing to the left of `=>` in its own constructor (blocks Curry's paradox). |
| **Subsingleton Elimination** | Allowing `Prop -> Type` matching only for `Prop` inductives with no runtime branching (`False`, `True`, `Eq`, `Acc`). |

---

## Further Reading

- Exact kernel specification and soundness checklist: [KERNEL.md](KERNEL.md)
- Side-by-side comparison of tactics and ordinary code: [PROOFS_FOR_PROGRAMMERS.md](PROOFS_FOR_PROGRAMMERS.md)
- Concrete examples and fixes for `K005` / `K006` / `K020` / `K025` / `K030` / `K031`: [TROUBLESHOOTING.md](TROUBLESHOOTING.md)
- Zero-axiom IO verification (practical higher-order inductives `IO` and `Eff`): [IO_VERIFICATION.md](IO_VERIFICATION.md)
