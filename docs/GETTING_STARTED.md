# Getting Started

**Proof Samurai** is a dependently-typed proof assistant using whitespace-insensitive **Scala 3 brace syntax**. You write functional programs, prove properties checked by a small **Trusted Kernel**, and extract proof-erased **Scala 3**, **TypeScript**, **JavaScript**, **Haskell**, or **OCaml** code with zero proof overhead at runtime.

Basic familiarity with Scala, TypeScript, Rust, or Haskell is enough to get started.

## 1. Setup and Proof Samurai Studio

Proof Samurai requires a JDK (Java 17 or newer recommended) and `sbt`. Verify your setup with:

```bash
sbt test
```

To explore interactively, start the built-in local Web IDE (Proof Samurai Studio):

```bash
sbt "run studio"
```

Open `http://localhost:8080` in your browser. Studio provides:

- A Scala 3 brace syntax editor with live kernel verification (`Ctrl+Enter`)
- Axiom-usage reporting (zero-axiom strict verification status)
- Proof hole (`?hole`) inspection with goal views and tactic suggestions
- A branching Interactive Proof Tree for stepping and backtracking
- A Code Extraction panel for Scala 3, TypeScript, and JavaScript

## 2. Data Types and Functions

Define `enum` data types and `def` functions using explicit `{ ... }` blocks:

```scala
import Prelude.*
import Nat.*

def doubleValue(number: Nat): Nat = {
  number + number
}

#eval doubleValue(3)
```

`#eval doubleValue(3)` evaluates the expression inside the kernel's normalizer (NbE: Normalization by Evaluation) and prints `6`.

## 3. Proof Styles

In Proof Samurai, a `theorem` is not a separate mathematical language: it is an ordinary pure function whose return type is a specification (`Prop`), and a `by { ... }` tactic block is a helper that builds that function body step by step before the kernel type-checks the result. For side-by-side comparisons of the exact same proof written directly as a `def` vs. with tactics, see **How Proofs & Tactics Relate to Ordinary Programs** (Chapter 02).

Proof Samurai supports several proof styles depending on the theorem.

### Computation and Automation (`refl`, `decide`, `arith`, `auto`)

```scala
import Prelude.*
import Nat.*

theorem twoPlusTwo: 2 + 2 === 4 = by {
  refl
}

theorem rearrange(first: Nat, second: Nat, third: Nat):
  (first + second) + (third + 0) === third + (second + first) = by {
  arith
}
```

### Equational Reasoning (`calc { ... }`)

Use `calc` when you want each intermediate algebraic step to remain explicit and readable:

```scala
import Prelude.*
import Nat.*
import List.*

theorem lengthThreeWay[Element](first: List[Element], second: List[Element], third: List[Element]):
  length((first ++ second) ++ third) === length(third) + (length(first) + length(second)) = {
  calc {
    length((first ++ second) ++ third)
    === (length(first) + length(second)) + length(third) by { simp }
    === length(third) + (length(first) + length(second)) by { arith }
  }
}
```

### Structural Induction (`induction`)

```scala
import Prelude.*
import Nat.*

theorem addZeroRightDemo(value: Nat): value + 0 === value = by {
  induction(value) {
    case Zero => { refl }
    case Succ(pred, ih) => {
      rewrite(ih)
      refl
    }
  }
}
```

## 4. Inspecting Goals with `?hole`

Place a named hole such as `?todo` wherever a proof is incomplete:

```scala
import Prelude.*
import Nat.*

theorem helpMe(left: Nat, right: Nat): left + right === right + left = by {
  ?todo
}
```

Run `sbt "run goals yourfile.samurai"` (or press `Ctrl+Enter` in Studio) to inspect the local hypotheses, normalized goal `⊢ ...`, and candidate tactics.

## 5. Extracting Verified Code

Everything in `Prop` (theorems, `===`, `Sorted`, `Le`, `And`, `Or`) is compile-time evidence and is erased completely during extraction:

```bash
sbt "run extract stdlib/Sorting.samurai --target scala3 --module VerifiedSorting --strict"
```

The `--strict` flag ensures that zero axioms and zero `sorry` placeholders appear anywhere in the dependency chain.

## Next Steps

- Read **How Proofs & Tactics Relate to Ordinary Programs** to see how every tactic maps to ordinary `match`, recursion, and casts, and how proofs connect to runnable code.
- See the **Language Reference** for full syntax, operators, `mutual`, `termination_by`, `partial def`, and tactic listings.
- Use the **Tactic Cookbook** to look up tactics by goal shape.
- Consult the **Error & Troubleshooting Guide** when the kernel rejects a definition or proof.
- Run `sbt "run verify-project . --strict"` to verify all standard library and example files.
