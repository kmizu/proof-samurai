# Proof Samurai (`proof-samurai`)

**Proof Samurai** is a complete, sound, dependently-typed proof assistant and verified programming language designed for **both humans and AI agents**, featuring:

- **Programmer-Friendly Scala 3 Brace Syntax (Zero Indentation Sensitivity)**: Familiar `enum`, `case class`, `def`, `val`, `theorem`, `match { case ... => ... }`, `if (...) { ... } else { ... }`, `{ val x = ...; ... }`, generics `[A]`, automatic type inference, dot projections (`pair.first`), UFCS (`list.length`), and `by { ... }` tactic blocks. Every block uses explicit `{ ... }` braces—no Python/Scala-3 indentation-sensitive syntax.
- **Small, Auditable Trusted Kernel (`samurai.kernel`)**:
  - De Bruijn–indexed Martin-Löf Dependent Type Theory / CIC-style core
  - Stratified universe hierarchy (`Prop : Type0 : Type1 : ...`, preventing Girard's paradox)
  - Impredicative `Prop` with **subsingleton elimination** (allows `False` and `Eq` into `Type`, blocks `Or`/`Exists` -> `Type`)
  - **Strict positivity checking** for inductive types (prevents Curry's paradox, even through transparent `def`s)
  - **Structural decreasing termination checking** for recursive `Fix` definitions (prevents `def loop: False = loop`)
  - **Full exhaustiveness checking** for pattern matching (with automatic discriminating motives for unreachable indexed cases like `Vec[A](Succ(n))` omitting `Nil`)
  - **Normalization by Evaluation (NbE)** with η-equality for functions and definitional proof irrelevance for `Prop`
  - **Strict Axiom & `sorry` Tracking**: Every theorem reports whether it is 100% axiom-free.
  - **De Bruijn Criterion**: Elaborator, tactics, `simp`, `decide`, `auto`, and AI search are all untrusted—every synthesized proof term is re-verified from scratch by the independent kernel.
- **Sound Code Extraction (`samurai.extract`)**:
  - Erases all `Prop` types, theorems, and proof arguments/fields (e.g., `Subset` refinement proofs disappear with zero runtime cost), and erases unreachable indexed branches (like `Vec.Nil` in `vecHead`) to `Nothing`/`never`
  - Emits clean, standalone, runnable **Scala 3 (brace syntax)**, **TypeScript**, and **JavaScript (ES module)** code
  - Produces a machine-readable `ExtractionManifest` confirming which theorems were verified and whether extraction is 100% axiom-free
- **AI-Native Proof Interface (`samurai.ai`)**:
  - Stateful NDJSON JSON-RPC proof server (`samurai serve`) with immutable, zero-cost **branching and backtracking** (`stateId` tree search / MCTS friendly), `batchStep`, `autoSolve`, `getProofTrace`, and `inspectHoles`
  - Type-directed lemma search (`searchLemmas`), ranked tactic recommendations (`suggest`), and built-in automated proof search (`auto` / `samurai`)

## Quick Start

### Build & Run Tests
```bash
sbt test
```

### CLI Usage
```bash
# Type-check and verify full insertion sort correctness (100% axiom-free strict mode)
sbt "run check stdlib/Sorting.samurai --strict"

# Search verified definitions and theorems
sbt "run search stdlib/Sorting.samurai sort"

# Extract verified Insertion Sort to standalone Scala 3, TypeScript, or JavaScript
sbt "run extract stdlib/Sorting.samurai --target scala3 --module VerifiedSorting --strict"
sbt "run extract stdlib/Sorting.samurai --target ts --strict"
sbt "run extract stdlib/Sorting.samurai --target js --strict"

# Start the interactive multi-line human REPL
sbt "run repl"

# Start the AI-native NDJSON interactive proof server
sbt "run serve"
```

## Example: Verified Insertion Sort (`stdlib/Sorting.samurai`)

```scala
import Prelude.*
import Nat.*
import List.*

def insert(element: Nat, sortedItems: List[Nat]): List[Nat] = {
  sortedItems match {
    case List.Nil => List.Cons(element, List.Nil[Nat])
    case List.Cons(head, tail) =>
      if (ble(element, head)) {
        List.Cons(element, List.Cons(head, tail))
      } else {
        List.Cons(head, insert(element, tail))
      }
  }
}

def insertionSort(items: List[Nat]): List[Nat] = {
  items match {
    case List.Nil => List.Nil[Nat]
    case List.Cons(head, tail) => insert(head, insertionSort(tail))
  }
}

@simp
theorem lengthInsertionSort(items: List[Nat]): length(insertionSort(items)) === length(items) = by {
  induction(items) {
    case Nil => { refl }
    case Cons(head, tail, ih) => {
      simp
      rewrite(ih)
      refl
    }
  }
}
```

## Project Structure

- `src/main/scala/samurai/kernel/` — Small Trusted Computing Base (`Term`, `Env`, `NbE`, `Positivity`, `Termination`, `TypeChecker`, `Pretty`)
- `src/main/scala/samurai/syntax/` — Whitespace-insensitive Scala 3 brace lexer, AST, and parser
- `src/main/scala/samurai/elab/` — Bidirectional elaborator, metavariable unification, pattern/record/module compilation
- `src/main/scala/samurai/tactic/` — LCF-style tactics (`intro`, `exact`, `apply`, `refl`, `symmetry`, `trans`, `rewrite`, `congr`, `induction`, `cases`, `split`, `left`, `right`, `exists`, `contradiction`, `discriminate`, `injection`, `have`, `unfold`, `simp`, `trivial`, `decide`, `auto`) and tactic recommender (`suggest`)
- `src/main/scala/samurai/extract/` — Sound `Prop`/type erasure IR and code emitters (`Scala3Emitter`, `TsEmitter`, `JsEmitter`)
- `src/main/scala/samurai/ai/` — Branching JSON-RPC proof server (`ProofSessionServer`) and multi-line human `Repl`
- `stdlib/` — 100% axiom-free verified standard library (`Prelude`, `Nat`, `List`, `Vec`, `Tree`, `Sorting`)
- `examples/` — Runnable examples (`HelloProof`, `VerifiedSort`, `SafeVec`)
