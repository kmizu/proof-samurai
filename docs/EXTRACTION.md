# Verified Code Extraction

Proof Samurai separates **computational data (`Type`)** from **logical evidence (`Prop`)**. Because the Trusted Kernel enforces strict subsingleton elimination, all `Prop` values can be **soundly erased** without changing program behavior!

## What Stays vs. What Gets Erased

| Proof Samurai Construct | Sort | Extracted Output (Scala 3 / TS / JS / Haskell / OCaml) |
|---|---|---|
| `enum Nat: Type`, `enum List[A]: Type`, `enum Tree[A]: Type` | `Type` | Kept as clean algebraic data types (`enum` / tagged unions / `data` / `type`) |
| `case class Queue[A](front: List[A], back: List[A])` | `Type` | Kept as Scala 3 `final case class`, TS/JS objects, or Haskell/OCaml ADTs |
| `def insertionSort`, `def enqueue`, `def vecHead` | `Type` | Kept as clean recursive functions (mutual recursion grouped as `let rec ... and ...` in OCaml) |
| `enum Eq`, `enum Le`, `enum Acc`, `enum And`, `enum Or`, `enum False` | `Prop` | **Completely erased** (0 bytes in output!) |
| `theorem insertionSortIsSorted`, `theorem countInsertionSort` | `Prop` | **Completely erased** (verified before erasure!) |
| `Subset.Mk(value, proof)` (`proof: P(value)`) | `Type` + `Prop` field | `proof` field **completely erased** → `Subset.Mk(value)` (`Subset_Mk value`) |
| Impossible indexed match branch (e.g. `Vec.Nil` in `vecHead`) | Unreachable | Erased to `throw new AssertionError(...)` / `P.error` / `failwith` |

## Example: Verified Insertion Sort → Production Scala 3

In `stdlib/Sorting.samurai`, `sortVerified` returns a `Subset` bundling the sorted list with a proof of BOTH sortedness (`Sorted(output)`) and multiset permutation (`forall target => count(target, output) === count(target, input)`):

```scala
def sortVerified(items: List[Nat]):
  Subset[List[Nat], (output: List[Nat]) => IsSortedPermutation(items, output)]
```

When you run:
```bash
sbt "run extract stdlib/Sorting.samurai --target scala3 --module VerifiedSorting --strict"
```

Proof Samurai verifies all 51 theorems with **0 axioms**, erases every proof, and emits clean, standalone Scala 3 brace code:

```scala
object VerifiedSorting {
  enum Subset[Domain] {
    case Mk(value: Domain)
  }

  def sortVerified(items: List[Nat]): Subset[List[Nat]] = {
    Subset.Mk[List[Nat]](insertionSort(items))
  }
}
```

## Extraction Targets

### 1. Scala 3 (`--target scala3`)
Standalone, brace-delimited Scala 3 code with zero runtime dependencies. Compiles directly with `scalac`.
```bash
sbt "run extract stdlib/Sorting.samurai --target scala3 --module VerifiedSorting --out out/VerifiedSorting.scala --strict"
```

### 2. TypeScript (`--target ts`)
Clean ES module with strict discriminated unions and typed generic functions.
```bash
sbt "run extract stdlib/Sorting.samurai --target ts --out out/sorting.ts --strict"
```

### 3. JavaScript (`--target js`)
Zero-dependency ES module runnable directly in Node.js or browsers.
```bash
sbt "run extract stdlib/Sorting.samurai --target js --out out/sorting.mjs --strict"
```

### 4. Haskell (`--target haskell` / `--target hs`)
Standalone Haskell 2010 / GHC module using `NoImplicitPrelude` + `import qualified Prelude as P` (preventing collisions with Prelude's `Bool`, `Either`, `map`, `length`, `filter`, etc.), clash-free `Type_Ctor` constructors (`Nat_Zero`, `List_Cons`, `Vec_Cons`, `Subset_Mk`), and automatic `deriving (P.Eq, P.Show)` on first-order ADTs.
```bash
sbt "run extract stdlib/Sorting.samurai --target haskell --module VerifiedSorting --out out/VerifiedSorting.hs --strict"
```

### 5. OCaml (`--target ocaml` / `--target ml`)
Standalone OCaml (4.x / 5.x) module with clash-free `Type_Ctor` variant constructors, SCC-ordered `type ... and ...` and `let rec ... and ...` blocks for mutual recursion (`isEven` / `isOdd`), and `Stdlib.unit` thunking for zero-argument unreachable definitions (`absurd`) so module initialization never crashes or hits the value restriction.
```bash
sbt "run extract stdlib/Sorting.samurai --target ocaml --module VerifiedSorting --out out/verified_sorting.ml --strict"
```

## CI/CD Strict Trust Gates (`--strict`, `--total`, `--json`)

In CI pipelines or AI agent workflows, pass `--strict` so extraction fails if any `sorry` or `axiom` appears anywhere in the dependency cone, and optionally `--total` to also reject any `partial def`:

```bash
sbt "run extract stdlib/Sorting.samurai --target scala3 --strict --total --json"
```

The JSON response includes a complete `manifest` listing `extractedTypes`, `extractedFunctions`, `erasedPropositions`, `verifiedTheorems`, `axiomsUsed`, `partialFunctions`, `isAxiomFree`, and `isTotal`.
