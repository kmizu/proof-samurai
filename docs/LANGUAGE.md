# Proof Samurai Language Guide

Proof Samurai uses a **programmer-friendly Scala 3 brace-delimited syntax** with **zero indentation sensitivity**. Every block, `enum`, `module`, `match`, `if`/`else`, and `by` tactic script uses explicit `{ ... }` braces.

## Declarations

### Inductive Data Types (`enum`)
```scala
enum Nat: Type {
  case Zero
  case Succ(pred: Nat)
}

// Indexed inductive family
enum Vec[Element](size: Nat): Type {
  case Nil: Vec[Element](Nat.Zero)
  case Cons(tailSize: Nat, head: Element, tail: Vec[Element](tailSize)): Vec[Element](Nat.Succ(tailSize))
}

// Propositions live in Prop (completely erased during code extraction!)
enum Le(lower: Nat, upper: Nat): Prop {
  case Refl(value: Nat): Le(value, value)
  case Step(lower: Nat, upper: Nat, prev: Le(lower, upper)): Le(lower, Nat.Succ(upper))
}
```

### Records (`case class`)
```scala
case class Pair[First, Second](first: First, second: Second)

def swap[A, B](pair: Pair[A, B]): Pair[B, A] = {
  Pair(pair.second, pair.first)
}
```

### Recursive Functions (`def`) & Theorems (`theorem` / `lemma`)
- Implicit type parameters `[A, B]` are inferred automatically at call sites.
- Decreasing inductive parameters are detected automatically (or specified with `@decreasing(paramName)`).
- Theorems can be proved either as direct functional proof terms or with `by { ... }` tactic blocks.

```scala
@simp
theorem addZeroRight(value: Nat): value + 0 === value = by {
  induction(value) {
    case Zero => { refl }
    case Succ(pred, ih) => {
      simp
      rewrite(ih)
      refl
    }
  }
}
```

### Mutual Structural Recursion (`mutual { ... }`)
Mutually recursive functions decreasing structurally on a shared inductive type are verified by the kernel via `MutualFix`:

```scala
mutual {
  def isEven(value: Nat): Bool = {
    value match {
      case Nat.Zero => true
      case Nat.Succ(pred) => isOdd(pred)
    }
  }

  def isOdd(value: Nat): Bool = {
    value match {
      case Nat.Zero => false
      case Nat.Succ(pred) => isEven(pred)
    }
  }
}
```

### Well-Founded Recursion (`termination_by` / `decreasing_by`)
Import `WellFounded.*` to write fuel-free general recursive algorithms (such as Euclidean `gcd`, `divNat`, `modNat`, and `quickSort`) backed by 0-axiom constructive `Acc[Nat, Lt]` proofs. All `Acc` and `Lt` proofs live in `Prop` and are completely erased during code extraction:

```scala
import WellFounded.*

def quickSort(items: List[Nat]): List[Nat] = {
  items match {
    case [] => []
    case pivot :: rest => {
      val smaller = filter((elem: Nat) => elem <= pivot, rest)
      val larger = filter((elem: Nat) => pivot < elem, rest)
      quickSort(smaller) ++ (pivot :: quickSort(larger))
    }
  }
} termination_by {
  length(items)
}
```

If an algorithm uses a custom measure decrease, supply an explicit `decreasing_by { ... }` tactic block or annotate a helper lemma with `@wf`.

### Sound Isolated General Recursion (`partial def`)
For computations whose termination is unknown or unbounded (such as Collatz sequences or event loops), mark a function `partial def`. To preserve logical soundness:
- A `partial def` cannot return `Prop` (`K030`), and theorems cannot be marked `partial`.
- Total definitions and theorems cannot reference any `partial def` (`K031`).
- `NbE` never unfolds `partial def` during type checking; `#eval` evaluates it with a bounded step limit, and code extraction emits native recursion while recording it under `partialFunctions` in the extraction manifest (rejected when `--total` is passed).

```scala
partial def collatzSteps(value: Nat): Nat = {
  if (value <= 1) {
    0
  } else {
    if (isEven(value)) { 1 + collatzSteps(half(value)) }
    else { 1 + collatzSteps(3 * value + 1) }
  }
}
```

## Operators & Sugar
| Syntax | Meaning |
|---|---|
| `a === b`, `a !== b` | Propositional equality `Eq` and inequality `Not(Eq)` |
| `P /\ Q`, `P \/ Q`, `~P` | Logical `And`, `Or`, `Not` |
| `forall (x: A) => B` | Dependent function / universal quantification (`Pi`) |
| `exists (x: A) => P` | Existential proposition (`Exists`) |
| `a + b`, `a - b`, `a * b` | `Nat` arithmetic (`add`, `sub`, `mul`) |
| `a == b`, `a != b`, `a <= b`, `a < b` | Boolean comparisons (`beq`, `ble`, `blt`) |
| `a && b`, `a \|\| b`, `!a` | Boolean operations (`andBool`, `orBool`, `notBool`) |
| `h :: t`, `xs ++ ys`, `[1, 2, 3]`, `[]` | `List.Cons`, `append`, and list literals / list patterns |
| `xs.length`, `pair.first` | UFCS method calls and `case class` field projections |
| `0, 1, 2`, `true, false` | `Nat` and `Bool` literals |
| `do { val x <- act; ... }` | Monadic `do`-notation desugared to `bind` (for `stdlib/IO.samurai` or any in-scope `bind`) |

## Monadic `do { ... }` Notation

Inside `do { ... }`, `val x <- action` desugars to `bind(action, x => rest)`, `val x = expr` creates a pure local binding, and a standalone expression statement `action` chains via `bind(action, _ => rest)`. Because `do` is contextual (only active before `{`), identifiers named `do` remain valid everywhere else. See [IO_VERIFICATION.md](IO_VERIFICATION.md) for verified IO programs, `HoareIO` invariants, and real-runtime extraction.

## Equational Reasoning (`calc { ... }`)
```scala
theorem calcExample[Element](first: List[Element], second: List[Element], third: List[Element]):
  length((first ++ second) ++ third) === length(third) + (length(first) + length(second)) = {
  calc {
    length((first ++ second) ++ third)
    === (length(first) + length(second)) + length(third) by { simp }
    === length(third) + (length(first) + length(second)) by { arith }
  }
}
```

## Built-In Tactics (`by { ... }`)
- **Structure**: `intro(x)`, `intros(x, y)`, `revert(x)`, `rename(old, new)`, `exact(term)`, `apply(term)`, `assumption`, `have(name: Type) { ... }`, `specialize(hyp, arg1, ...)`, `obtain(x, h) = expr`
- **Equality**: `refl`, `symmetry`, `trans(mid)`, `rewrite(h1, ...) [in h | in *]`, `rewriteRev(h1, ...) [in h | in *]`, `subst(eq)`, `congr`
- **Inductives**: `induction(x) { case ... => { ... } }`, `cases(expr[, eqHyp]) { case ... => { ... } }`, `by_cases(cond[, h])`, `discriminate`, `injection(h, name)`
- **Logic**: `split`, `left`, `right`, `exists(witness)`, `contradiction`, `exfalso`, `tauto` (complete intuitionistic propositional solver, 0 axioms)
- **Automation**: `unfold(defName)`, `simp[(lem, *)] [in h | in *]`, `arith` / `ring` (Nat commutative semiring solver), `omega` / `lia` (linear Nat arithmetic & inequality solver), `cc` (congruence closure + injectivity/disjointness), `trivial`, `decide`, `auto` (or `samurai`)
- **Combinators**: `t1 <;> t2`, `all { ... }`, `try { ... }`, `repeat { ... }`, `first { t1 | t2 | ... }`
- **Development**: `?holeName`, `sorry` (explicitly tracked in kernel trust reports!)
