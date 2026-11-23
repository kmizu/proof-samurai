# Getting Started with Proof Samurai

Welcome! **Proof Samurai** lets you write everyday functional programs in familiar **Scala 3 brace syntax** (no indentation-sensitive rules), prove properties about them with a **small, sound Trusted Kernel**, and **extract** them into clean, fast **Scala 3, TypeScript, or JavaScript** with all proofs erased at zero runtime cost.

You do **not** need a PhD in type theory to get started. If you know basic Scala, TypeScript, Rust, or Haskell, you will feel right at home in 10 minutes.

## 1. Launch Proof Samurai Studio (Recommended)

The friendliest way to explore Proof Samurai is the built-in interactive Web IDE:

```bash
sbt "run studio"
```

Open **http://localhost:8080** in your browser. You will get:
- A live Scala 3 brace editor with instant kernel verification (`Ctrl+Enter`)
- A **100% Axiom-Free** green shield badge
- Interactive `?hole` cards with 1-click tactic suggestions
- A visual **Interactive Proof Tree** where you can branch and backtrack
- A 1-click **Code Extraction** panel (Scala 3, TypeScript, JavaScript)

## 2. Your First Data Type & Function

Write ordinary Scala 3 `enum`s and `def`s — always using explicit `{ ... }` braces:

```scala
import Prelude.*
import Nat.*

def doubleValue(number: Nat): Nat = {
  number + number
}

#eval doubleValue(3)
```

Notice `#eval doubleValue(3)` prints `6` directly — Proof Samurai computes with your functions inside its normalizer (NbE).

## 3. Your First Theorem (Three Friendly Styles!)

Proof Samurai never forces one rigid proof style. Pick whichever reads best:

### Style A: One-Word Automation (`refl`, `decide`, `arith`, `auto`)
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

### Style B: Readable Equational Reasoning (`calc { ... }`)
Great for explaining *why* an equation holds to teammates (and AI reviewers!):

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

### Style C: Structural Induction (`induction`)
```scala
import Prelude.*
import Nat.*

theorem addZeroRightDemo(value: Nat): value + 0 === value = by {
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

## 4. Stuck on a Proof? Drop a `?hole`!

Whenever you aren't sure what to write next, just put `?todo` inside your proof:

```scala
import Prelude.*
import Nat.*

theorem helpMe(left: Nat, right: Nat): left + right === right + left = by {
  ?todo
}
```

Then run `sbt "run goals yourfile.samurai"` (or press `Ctrl+Enter` in Studio). Proof Samurai shows your exact hypotheses, the simplified goal `⊢ ...`, and **ranked tactic suggestions**!

## 5. Extract Verified Code

Everything living in **`Prop`** (theorems, `===` equalities, `Sorted`, `Le`, `And`, `Or`) is **compile-time evidence only**. When you extract your code, all `Prop` proofs vanish completely:

```bash
sbt "run extract stdlib/Sorting.samurai --target scala3 --module VerifiedSorting --strict"
```

The `--strict` flag guarantees **zero axioms and zero `sorry`** were used anywhere in the dependency chain.

## Next Steps
- Explore the **Friendly Tactic Cookbook** for recipes organized by goal shape.
- Check the **Kindful Error Guide** whenever the kernel rejects something — every rejection protects soundness!
- Try `sbt "run verify-project . --strict"` to verify all 12 standard library & example files at once.
