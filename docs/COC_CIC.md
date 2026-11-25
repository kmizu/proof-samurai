# CoC & CIC: Inside the Theorem Prover

From the outside, a proof assistant (Coq / Rocq, Lean, Agda, Proof Samurai) can feel like a black box — some mysterious engine that "knows math." Once you understand its foundation, the **Calculus of Constructions (CoC)** and the **Calculus of Inductive Constructions (CIC)**, the mystery disappears completely: **there is no magic — the heart of a theorem prover is simply a tiny static type checker.**

This chapter opens the black box by explaining how CoC and CIC work, why each soundness guard exists (with concrete paradoxes), and how every theoretical idea maps directly onto Proof Samurai's kernel (`src/main/scala/samurai/kernel/`).

---

## 1. The Big Picture: A Tiny Type Checker Under the Hood

Proof Samurai is structured around the **de Bruijn criterion**:

```text
  [Untrusted Frontend (Human / Tactics / AI)]
    Surface syntax / Tactics (omega, cc, tauto, simp, auto) / Elaborator
                          |
                          |  Elaborates & searches to synthesize
                          |  a concrete proof term (Core CIC Term)
                          v
  [Trusted Kernel (Trusted Computing Base = samurai.kernel)]
    Term (only 12 AST nodes) + TypeChecker + NbE + Positivity + Termination
                          |
                          |  Checks one question: "Does term t really have type T?"
                          v
                Accepted (KernelEnv) / Rejected (Error)
```

Two consequences follow immediately:

- **Tactics (`omega`, `simp`, `induction`, `auto`) and AI agents are never trusted.** They are merely programs that assemble a candidate proof term.
- **Only the small kernel certifies truth.** Even if a tactic contained a bug, any invalid proof term it produced would be rejected by the kernel's type checker before entering `KernelEnv`.

Understanding a theorem prover therefore means understanding **the tiny core language (CIC) and its handful of typing rules**.

---

## 2. Curry-Howard Correspondence: Propositions Are Types, Proofs Are Programs

The foundation of CoC / CIC is the **Curry-Howard correspondence**. Logical concepts and programming language types are not merely analogous — they are the **exact same objects**:

| Logic | Type Theory / Programming | Proof Samurai Syntax |
|---|---|---|
| Proposition `P` | Type `P : Prop` | `a + b === b + a` |
| Proof `pf` of `P` | Value (term) `pf : P` | `theorem ... = by { ... }` |
| Implication `P => Q` | Function type `P => Q` | `(h: P) => ...` |
| Universal quantification `∀x:A. P(x)` | **Dependent function type `Π(x: A). P(x)`** | `forall (n: Nat) => n + 0 === n` |
| Conjunction `P /\ Q` | Pair (product) type `And[P, Q]` | `And.Intro(hp, hq)` |
| Disjunction `P \/ Q` | Tagged union (sum) type `Or[P, Q]` | `Or.Left(hp)` / `Or.Right(hq)` |
| Existential `∃x:A. P(x)` | Dependent pair type `Exists[A, P]` | `Exists.Intro(w, pw)` |
| Contradiction `False` | Empty type `False` (0 constructors) | `enum False: Prop {}` |
| Negation `~P` | Function returning `False`: `P => False` | `def Not(P: Prop): Prop = P => False` |

Saying "the logic is consistent (`False` cannot be proved)" is literally identical to saying "no terminating pure program can construct a value of the empty type `False`."

---

## 3. CoC (Calculus of Constructions): Unifying Everything into `Pi`

In mainstream languages, functions, generics, type constructors, and specifications are separate features. Type theory organizes them along the four axes of the **Lambda Cube**:

1. **Terms depending on terms** (Simply Typed Lambda Calculus): `(x: Nat) => x + 1`
2. **Terms depending on types** (Polymorphism / Generics / System F): `[A: Type](x: A) => x`
3. **Types depending on types** (Type constructors / Higher-kinded types / F-omega): `List : Type => Type`
4. **Types depending on terms** (**Dependent types** / lambda-P): `Vec : Type => Nat => Type`, `Eq : [A] => A => A => Prop`

The breakthrough of **CoC (Thierry Coquand & Gérard Huet, 1988)** is unifying all four axes into **a single construct: the dependent product type `Pi(x: A, B)` (written `Π(x: A). B`)**:

- When `x` does not occur in `B`: `Pi(_, A, B)` is an ordinary function type `A => B` (and logical implication).
- When `A` is `Type`: `Pi(A, Type, A => A)` is parametric polymorphism (generics).
- When `B` is `Type`: `Pi(_, Type, Type)` is a type constructor like `List`.
- When `x` occurs inside `B`: `Pi(n, Nat, Eq(add(n, 0), n))` is universal quantification `∀n:Nat. n + 0 = n` or an indexed family like `Vec[A](n)`.

In CoC there is no syntactic wall between the "term level" and the "type level": `Nat`, `Type`, `add(n, 0)`, and `n + 0 === n` are all represented by the exact same `Term` datatype.

---

## 4. From CoC to CIC (Calculus of Inductive Constructions)

Pure CoC can Church-encode natural numbers as `forall [X: Type] => (X => X) => X => X`, yet it has two critical limitations:

- **Even Peano's axiom `0 !== 1` is unprovable** in pure CoC without adding extra axioms.
- **Mathematical induction** and constant-time pattern matching (`pred`, `head`, etc.) cannot be expressed directly.

**CIC (Calculus of Inductive Constructions)** extends CoC by making **Inductive Types**, **dependent pattern matching (`Match`)**, and **structural recursion (`Fix`)** first-class primitives.

With CIC, **logic, equality, and data structures are all built from the exact same `enum` mechanism — with zero built-in axioms**:

```scala
// Logical connectives are just inductive types (stdlib/Prelude.samurai)
enum False: Prop {}
enum True: Prop { case Intro }
enum And[Left: Prop, Right: Prop]: Prop { case Intro(left: Left, right: Right) }
enum Or[Left: Prop, Right: Prop]: Prop { case Left(value: Left); case Right(value: Right) }
enum Eq[T: Type](lhs: T): T => Prop { case Refl }

// Data structures use the exact same mechanism (stdlib/Nat.samurai, stdlib/Vec.samurai)
enum Nat: Type { case Zero; case Succ(pred: Nat) }
enum Vec[A: Type]: Nat => Type {
  case Nil: Vec[A](Nat.Zero)
  case Cons(n: Nat, head: A, tail: Vec[A](n)): Vec[A](Nat.Succ(n))
}
```

### Equality `Eq` and `rewrite` Demystified

Even equality (`===` / `Eq`) is not a built-in axiom. It is an indexed inductive type with a single constructor `Eq.Refl` (`x === x`).

When you write `rewrite(h)` using `h : a === b` to turn a goal `P(a)` into `P(b)`, the elaborator simply constructs a **dependent `Match` on `h`**:

- Matching on `h : Eq[T](a, b)` has only one possible branch: `Eq.Refl`, where `b` is identical to `a`.
- Therefore, any proof of `P(a)` automatically transports to a proof of `P(b)` (Leibniz's substitution property).

### Dependent Pattern Matching and the `motive`

In ordinary languages, every branch of a `match` must return the same type. In CIC, `Match` carries a **motive** function `M`, allowing **each branch's required return type to depend on the constructor matched**.

When proving `n + 0 === n` by cases on `n: Nat`, the motive is `M = (k: Nat) => k + 0 === k`:

- The `case Nat.Zero` branch must return `M(Nat.Zero)` = `0 + 0 === 0` (reduces to `0 === 0`, solved by `Eq.Refl`).
- The `case Nat.Succ(pred)` branch must return `M(Nat.Succ(pred))` = `Nat.Succ(pred) + 0 === Nat.Succ(pred)` (built from the recursive call `ih : pred + 0 === pred`).

In CIC, **mathematical induction is literally `Fix` (structural recursion) combined with a dependent `Match` (with a motive)**.

---

## 5. Computation Inside Types: Conversion and NbE

The single rule that gives CIC its computational power is the **Conversion Rule**:

```text
  Γ ⊢ t : A      A ≡ B (equal after evaluation)
  ---------------------------------------------  [Conv]
                    Γ ⊢ t : B
```

Because types can contain expressions, `Vec[Nat](2 + 2)` and `Vec[Nat](4)` are the **exact same type**: the kernel evaluates expressions inside types and treats them as **definitionally equal (`≡`)**. That is why `theorem twoPlusTwo: 2 + 2 === 4 = by { refl }` succeeds with a single `Eq.Refl`.

Proof Samurai's kernel decides `A ≡ B` via **Normalization by Evaluation** ([NbE.scala](https://github.com/kmizu/proof-samurai/blob/main/src/main/scala/samurai/kernel/NbE.scala)), performing:

| Reduction | Symbol | Meaning |
|---|---|---|
| Beta | `β` | Function application `((x) => body)(arg)` computes to `body[x := arg]` |
| Zeta | `ζ` | Local binding `val x = v; body` (`Let`) substitutes `v` |
| Delta | `δ` | Transparent `def` unfolds its body (`partial def` is never unfolded) |
| Iota | `ι` | `Match` on a constructor reduces to the matching branch |
| Fixpoint | `fix` | `Fix` / `MutualFix` unfolds **only when its decreasing argument is a constructor (`VCtor`)** |
| Proof Irrelevance | `PI` | Any two proofs `pf1, pf2 : P` of the same proposition `P : Prop` are definitionally equal |

Restricting `Fix` unfolding to constructor values guarantees that type-level normalization always terminates.

---

## 6. The Entire Core Language: All 12 `Term` Constructors

Nothing dispels the black-box illusion faster than seeing the entire core AST of the Trusted Kernel ([Term.scala](https://github.com/kmizu/proof-samurai/blob/main/src/main/scala/samurai/kernel/Term.scala)). Every theorem and program in Proof Samurai reduces to just **12 constructors**:

```scala
enum Term {
  // --- CoC core (7 constructors) ---
  case USort(sort: Sort)                                   // Prop, Type0, Type1, ...
  case Var(idx: Int)                                       // De Bruijn index variable
  case Const(name: String)                                 // Reference to checked def / theorem / axiom
  case Pi(name: String, domain: Term, codomain: Term)      // Dependent product forall (x: A) => B
  case Lam(name: String, domain: Term, body: Term)         // Lambda abstraction (x: A) => body
  case App(fn: Term, arg: Term)                            // Function application fn(arg)
  case Let(name: String, ty: Term, value: Term, body: Term)// Local let binding

  // --- CIC inductive extension (5 constructors) ---
  case Ind(name: String)                                   // Inductive type (Nat, List, Eq, IO, ...)
  case Ctor(indName: String, ctorName: String)             // Constructor (Nat.Succ, Eq.Refl, ...)
  case Match(indName: String, params: List[Term], motive: Term, scrutinee: Term, branches: List[MatchBranch])
  case Fix(name: String, recArgIdx: Int, ty: Term, body: Term)     // Structural recursion
  case MutualFix(defs: List[MutualFixDef], selectedIndex: Int)     // Mutual structural recursion
}
```

### De Bruijn Indices

Instead of storing variable names that could clash under substitution, `Var(idx)` counts how many enclosing binders (`Lam`, `Pi`, `Let`) to walk outward (`Var(0)` is the innermost binder). Variable capture becomes impossible and alpha-equivalence is just structural equality (`Term.alphaEq`).

### Core Typing Rules (`TypeChecker.scala`)

The core of type checking reduces to six rules:

```text
  [Sort]   Γ ⊢ Prop : Type0          Γ ⊢ Type(i) : Type(i+1)

  [Var]    (x : A) ∈ Γ  ==>  Γ ⊢ x : A

  [Pi]     Γ ⊢ A : s1      Γ, x:A ⊢ B : s2
           ----------------------------------
             Γ ⊢ Π(x: A). B : piSort(s1, s2)

  [Lam]    Γ ⊢ A : s       Γ, x:A ⊢ b : B
           ----------------------------------
             Γ ⊢ (x: A) => b : Π(x: A). B

  [App]    Γ ⊢ f : Π(x: A). B      Γ ⊢ a : A
           ----------------------------------
                Γ ⊢ f(a) : B[x := a]

  [Conv]   Γ ⊢ t : A      A ⪯ B (NbE + cumulativity)
           ----------------------------------
                       Γ ⊢ t : B
```

Here `piSort(s1, s2)` is implemented in three lines in `Term.scala`:

- `piSort(_, Prop) = Prop` (impredicativity of `Prop`: quantifying over all propositions `forall (P: Prop) => P => P` stays inside `Prop`)
- `piSort(Prop, Type(j)) = Type(j)`
- `piSort(Type(i), Type(j)) = Type(max(i, j))`

---

## 7. Why Every Soundness Guard Exists (Concrete Paradoxes)

CIC enforces four strict guards that often surprise programmers at first. Each guard blocks a concrete paradox that would otherwise let anyone prove `False` and destroy soundness.

### Guard 1: Universe Stratification (`Type0 : Type1 : Type2 : ...`)

Allowing `Type : Type` triggers **Girard's paradox** (the type-theoretic counterpart of Russell's paradox), making `False` provable.

Proof Samurai stratifies universes as `Prop : Type0 : Type1 : ...` and rejects placing a `Type0` field inside a `Type0` inductive (`K005`).

### Guard 2: Strict Positivity (`Positivity.scala`)

Allowing an inductive type `Bad` to appear to the left of an arrow (`=>`) in its own constructor triggers **Curry's paradox**:

```scala
// Violates strict positivity — rejected by Proof Samurai with K006
enum Bad: Prop {
  case Mk(f: Bad => False)
}
// If allowed, self-application bypasses termination checking and proves False:
// def omega(b: Bad): False = b match { case Bad.Mk(f) => f(b) }
// def paradox: False = omega(Bad.Mk(omega))
```

Notice that `omega` does not even use recursion (`Fix`), yet `omega(Bad.Mk(omega))` loops forever and inhabits `False`. `Positivity.scala` expands transparent aliases like `Not(Bad)` via NbE and blocks all negative occurrences (`K006`).

### Guard 3: Termination Checking (`Termination.scala`) and `partial def` Isolation

Allowing unrestricted recursion in proofs immediately proves every false statement in one line:

```scala
// Non-terminating fake proof — rejected by Proof Samurai with K020
def loop(n: Nat): False = { loop(n) }
```

Therefore, every `Fix` / `MutualFix` must pass a **structurally strictly smaller** subterm extracted by pattern matching (`K020`).

- Algorithms that decrease by a general measure (such as `quickSort`, `gcd`, or `divNat`) use structural recursion over the accessibility predicate `Acc` (`termination_by` / `stdlib/WellFounded.samurai`), achieving **well-founded recursion with 0 axioms**.
- Functions that intentionally opt out of termination proofs can be marked `partial def`, but they cannot return `Prop` (`K030`), are never unfolded by NbE, and cannot be called from any total `def` or `theorem` (`K031`).

### Guard 4: `Prop` vs. `Type` and Subsingleton Elimination

Why does CIC separate logical `Prop` from computational `Type`? For three mutually reinforcing reasons:

1. **Zero-byte proof erasure (Extraction)**: `Prop` values never affect runtime computation, so they vanish completely when extracting to Scala 3, TypeScript, JavaScript, Haskell, or OCaml.
2. **Proof irrelevance**: Any two proofs of the same proposition are interchangeable without breaking dependent types.
3. **Impredicativity**: Quantifying over all propositions `forall (P: Prop) => ...` remains in `Prop`.

To keep all three properties sound together, eliminating a `Prop` value to produce a `Type` value is allowed **only for subsingletons**:

- **Allowed**: `False` (0 constructors — unreachable), `Eq` (1 constructor `Refl`, no computational payload), `Acc` (1 constructor whose fields live in `Prop`).
- **Forbidden (`K025`)**: Pattern matching on `Or[P, Q]` or `Exists[Nat, P]` to produce a `Nat` or `Bool`. If allowed, runtime output would depend on which proof was chosen — breaking both proof irrelevance and proof erasure. (Use `Either` or `Subset` when computational data is needed.)

---

## 8. End-to-End Trace: Watching a Proof Become a CIC Term

Let us trace a familiar theorem from surface syntax all the way through the kernel and extraction.

### Step 1: Surface Code (Untrusted Frontend)

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

### Step 2: Core CIC Term Produced by Tactics

`Tactics.scala` elaborates the script into a single pure CIC term (shown with readable names):

```scala
Fix(
  name = "addZeroRight",
  recArgIdx = 0,
  ty = Pi(n: Nat, Eq[Nat](add(n, Nat.Zero), n)),
  body = Lam(n: Nat,
    Match(
      indName = "Nat",
      motive = Lam(k: Nat, Eq[Nat](add(k, Nat.Zero), k)),
      scrutinee = n,
      branches = [
        case Zero =>
          Eq.Refl[Nat](Nat.Zero),
        case Succ(pred) =>
          // ih = addZeroRight(pred) : Eq[Nat](add(pred, 0), pred)
          // Match on ih (rewrite) transports Eq.Refl(Succ(pred)) to Eq(Succ(add(pred, 0)), Succ(pred))
          Match(
            indName = "Eq",
            motive = Lam(y: Nat, Lam(_: Eq[Nat](add(pred, Nat.Zero), y),
                       Eq[Nat](Nat.Succ(add(pred, Nat.Zero)), Nat.Succ(y)))),
            scrutinee = addZeroRight(pred),
            branches = [ case Refl => Eq.Refl[Nat](Nat.Succ(add(pred, Nat.Zero))) ]
          )
      ]
    )
  )
)
```

### Step 3: What the Trusted Kernel Verifies

1. **Type checking (`TypeChecker` + `NbE`)**:
   - In the `Zero` branch, `add(Nat.Zero, Nat.Zero)` normalizes to `Nat.Zero`, so `Eq.Refl(Nat.Zero)` matches `Eq(add(0, 0), 0)`.
   - In the `Succ(pred)` branch, `add(Nat.Succ(pred), Nat.Zero)` normalizes to `Nat.Succ(add(pred, Nat.Zero))`, matching the `Eq` transport result type.
2. **Exhaustiveness**: Both `Nat.Zero` and `Nat.Succ`, plus `Eq.Refl`, are covered.
3. **Termination (`Termination`)**: The recursive argument `pred` is a structurally strictly smaller subterm of `n`.
4. **Axiom tracking (`Env`)**: Zero axioms or `sorry` appear in the dependency cone.

### Step 4: Extraction

Because `addZeroRight` returns a value in `Prop`, `Erasure.scala` erases it completely — 0 bytes in extracted Scala 3, TypeScript, JavaScript, Haskell, or OCaml output.

---

## Further Reading

- Exact kernel specification and soundness checklist: [KERNEL.md](KERNEL.md)
- Side-by-side comparison of tactics and ordinary code: [PROOFS_FOR_PROGRAMMERS.md](PROOFS_FOR_PROGRAMMERS.md)
- Concrete examples and fixes for `K005` / `K006` / `K020` / `K025` / `K030` / `K031`: [TROUBLESHOOTING.md](TROUBLESHOOTING.md)
