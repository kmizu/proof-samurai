# How Proofs & Tactics Relate to Ordinary Programs

Programmers approaching a proof assistant for the first time usually run into two reasonable questions:

1. **What are tactics (`intro`, `cases`, `induction`, `rewrite`, `split`) actually doing?** Are they a separate mathematical ritual unrelated to normal code?
2. **How do proofs connect to real, runnable programs?**

This guide explains both directly in terms of everyday typed functional programming (Scala, TypeScript, Rust).

---

## 1. A Proof *Is* a Function; a Tactic Builds That Function

In Proof Samurai, there is **no fundamental difference** between a `theorem` and a `def`:

- **Type (proposition)** = a specification that outputs must satisfy
- **Proof** = an ordinary pure function that returns a value of that specification type
- **Tactic block (`by { ... }`)** = an interactive code-builder that constructs that function body (`match`, lambdas, recursive calls, type casts) step by step while the type checker tracks what remains

Seeing the same theorem written both as an ordinary function and as a tactic block makes the relationship concrete.

### Example 1: Swapping a Conjunction (`And` is a 2-field tuple)

`P /\ Q` (`And[P, Q]`) is simply an inductive record with one constructor `Intro(leftProof: P, rightProof: Q)`. The following two definitions produce the **exact same kernel function**:

```scala
import Prelude.*

// Written directly as an ordinary function (no tactics)
def andCommAsFunction(left: Prop, right: Prop, both: left /\ right): right /\ left = {
  both match {
    case And.Intro(leftProof, rightProof) => And.Intro[right, left](rightProof, leftProof)
  }
}

// The exact same function built with `by { ... }` tactics
theorem andCommWithTactics(left: Prop, right: Prop, both: left /\ right): right /\ left = by {
  cases(both) {
    case Intro(leftProof, rightProof) => {
      split
      exact(rightProof)
      exact(leftProof)
    }
  }
}
```

Each tactic corresponds to a concrete piece of code:

- `cases(both)` writes `both match { ... }`
- `split` writes `And.Intro(?, ?)` and opens two subgoals for the arguments
- `exact(rightProof)` fills the first argument with `rightProof`

### Example 2: Structural Induction (`induction` is a recursive function)

Proving `value + 0 === value` for every `Nat` is literally writing a **recursive function over `value`**:

```scala
import Prelude.*
import Nat.*

// Written directly as an ordinary recursive function (no tactics)
def addZeroRightAsFunction(value: Nat): value + 0 === value = {
  value match returning (n: Nat) => n + 0 === n {
    case Nat.Zero => Eq.Refl[Nat, 0]
    case Nat.Succ(pred) =>
      congrArg[Nat, Nat](
        (k: Nat) => Nat.Succ(k),
        pred + 0,
        pred,
        addZeroRightAsFunction(pred)
      )
  }
}

// The same recursive function built with `by { ... }` tactics
theorem addZeroRightWithTactics(value: Nat): value + 0 === value = by {
  induction(value) {
    case Zero => { refl }
    case Succ(pred, ih) => {
      rewrite(ih)
      refl
    }
  }
}
```

Writing dependent proofs directly as `def` requires spelling out dependent return motives (`returning (n: Nat) => ...`) and equality wrappers (`congrArg`) by hand. `by { induction(value) { ... } }` synthesizes the same recursive function and `match` automatically.

Crucially, tactics are **never trusted**: once a `by { ... }` block finishes, the resulting function term is checked from scratch by the Trusted Kernel (`samurai.kernel`) using the exact same type, termination, and exhaustiveness rules as any regular `def`.

---

## 2. Tactic-to-Programming Translation Table

Thinking of each tactic as the ordinary code construct it emits makes proofs predictable:

| Tactic | Ordinary Code Equivalent | What It Constructs |
|---|---|---|
| `intro(x)` / `intros(x, y)` | `(x, y) => ...` | Binds lambda / function parameters |
| `exact(expr)` | `return expr` | Returns `expr` directly as the body |
| `apply(fn)` | `fn(?, ?)` | Calls `fn`, leaving unresolved arguments as remaining subgoals |
| `have(v: T) { ... }` | `val v: T = ...` | Introduces a local variable inside the function |
| `cases(x) { ... }` | `x match { ... }` | Pattern-matches on an `enum` or `Bool` |
| `induction(x) { ... }` | Recursive `def` + `match` | Pattern-matches on `x` and binds recursive call results as `ih` |
| `split` | `And.Intro(?, ?)` | Constructs a 2-element conjunction pair |
| `left` / `right` | `Or.Inl(?)` / `Or.Inr(?)` | Selects a branch of a disjoint union (like `Either.Left` / `Right`) |
| `exists(w)` | `Exists.Intro(w, ?)` | Pairs a witness value `w` with a proof about it |
| `refl` | `Eq.Refl` | Verifies both sides evaluate to the same normal form |
| `rewrite(eq)` | Type-safe cast via equality | Replaces `a` with `b` in the expected type using `eq: a === b` |
| `discriminate(h)` | Unreachable branch (`Nothing`) | Proves a branch with `0 === Succ(n)` or `true === false` is dead code |
| `injection(h, eq)` | Constructor deconstruction | Extracts `a === b` from `Succ(a) === Succ(b)` |
| `simp` / `arith` / `omega` / `cc` / `tauto` / `auto` | Verified boilerplate generators | Synthesizes simplification, semiring, linear-inequality, congruence-closure, or logic terms checked by the kernel |
| `t1 <;> t2` / `rewrite(...) in h` / `obtain(x, h) = e` | Proof-script combinators | Applies `t2` to every subgoal from `t1`, rewrites inside hypothesis `h`, or unpacks tuples/existentials in one line |

---

## 3. Four Ways Proofs Connect Directly to Runnable Programs

Proofs are not detached math exercises. They serve four concrete engineering purposes:

### 3.1 All-Input Guarantees Beyond Unit Tests

Unit tests check a finite list of inputs (e.g. `[3, 1, 2]`). In `stdlib/Sorting.samurai`, `insertionSortIsSorted` and `countInsertionSort` prove for **every possible `List[Nat]`** that `insertionSort` outputs a sorted list with the exact same element multiplicities as the input.

### 3.2 Unlocking Real Algorithms Under Termination Checking (`termination_by`)

Algorithms that do not decrease on a single constructor—such as `quickSort`, Euclidean `gcd`, and integer division `divNat`—need a proof that a `Nat` measure decreases on every recursive call.

In `stdlib/WellFounded.samurai`, proving the lemma `lengthFilterLe` (`length(filter(pred, rest)) <= length(rest)`) with tactics is what lets `quickSort` type-check cleanly with `termination_by { length(items) }` and **no `fuel` parameter**. Tactic lemmas act directly as building blocks that make real `def`s compile.

### 3.3 Eliminating Runtime Checks and Exceptions

In `stdlib/Vec.samurai`, `vecHead` requires a vector of length `Nat.Succ(n)`. Because the empty `Vec.Nil` branch is provably unreachable, callers never unwrap an `Option` or risk an out-of-bounds exception at runtime.

### 3.4 Zero-Overhead Verified Code Extraction (`Subset` and `Prop` Erasure)

In `stdlib/Sorting.samurai`, `sortVerified` bundles the sorted list with a proof of both sortedness and element-count preservation inside `Subset`:

```scala
// Proof Samurai source (carries specification proof in the type)
def sortVerified(items: List[Nat]):
  Subset[List[Nat], (output: List[Nat]) => IsSortedPermutation(items, output)]
```

When extracted to Scala 3, TypeScript, JavaScript, Haskell, or OCaml, every `Prop` type and proof field vanishes completely:

```scala
// Extracted Scala 3 output (proof field erased to 0 bytes)
enum Subset[Domain] {
  case Mk(value: Domain)
}

def sortVerified(items: List[Nat]): Subset[List[Nat]] = {
  Subset.Mk[List[Nat]](insertionSort(items))
}
```

Proofs act as **compile-time verification artifacts that leave zero runtime overhead** in the shipped code.

---

## 4. Choosing the Right Level of Verification

Not every function in an application needs a proof. Proof Samurai separates three levels cleanly:

| Construct | Typical Use | Termination Checked | Callable from Theorems | Extracted Output |
|---|---|---|---|---|
| Total `def` / `mutual` | Core data structures and pure logic | Yes (structural) | Yes | Normal functions |
| `def ... termination_by { ... }` | `divNat`, `gcd`, `quickSort`, custom measures | Yes (`Acc`, erased) | Yes | Normal functions (no `Acc`) |
| `partial def` | Unbounded loops, unknown termination, boundary code | No (type & exhaustiveness checked) | No (`K031` isolation) | Normal functions (listed in manifest) |

A pragmatic architecture verifies core invariants and algorithms with total `def` / `termination_by`, and isolates unbounded or boundary computations in `partial def` or the extracted host language.
