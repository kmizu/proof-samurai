# Proof Samurai Trusted Kernel Architecture

*New to dependent type theory? Start with [CoC & CIC: Inside the Theorem Prover](COC_CIC.md) for a self-contained explanation of Curry-Howard, `Pi` types, inductive motives, NbE conversion, and why each soundness guard blocks a concrete paradox.*

Proof Samurai follows the **de Bruijn criterion**: all surface elaboration, metavariable unification, pattern compilation, tactic scripts, automated proof search (`auto`), and AI agent sessions are **untrusted**. Every declaration and proof term must pass through the small, independent Trusted Kernel (`samurai.kernel`) before entering `KernelEnv`.

## Soundness Guarantees

1. **Universe Stratification (`Sort.scala` / `TypeChecker.scala`)**
   - `Prop : Type(0)` and `Type(i) : Type(i + 1)` with cumulative subtyping `Type(i) <= Type(j)` for `i <= j`.
   - `Type(i) : Type(i)` is rejected, preventing Girard's / Russell's paradox.
   - Predicativity of `Type(k)` inductives: constructor fields of a `Type(k)` inductive cannot live in `Type(j)` for `j > k`.

2. **Strict Positivity (`Positivity.scala`)**
   - Inductive types cannot appear to the left of an arrow (`=>`) in any constructor field, nor inside arbitrary applications or their own result indices.
   - Transparent definitions (like `def Not(P: Prop): Prop = P => False`) are expanded prior to positivity checking, preventing hidden negative occurrences and Curry's paradox.

3. **Subsingleton `Prop` Elimination (`TypeChecker.scala`)**
   - `Prop` is impredicative for `Pi` types and proof-irrelevant.
   - Eliminating a `Prop` inductive into `Type(k)` is allowed **only** when the inductive is a subsingleton (0 constructors like `False`, or 1 constructor whose every field lives in `Prop` or is forced directly by a result index, like `Eq`, `True`, and `Acc`).
   - Eliminating `Or` or `Exists` into `Type` is rejected (`K025`), ensuring both logical consistency and sound proof erasure during code extraction.

4. **Structural & Mutual Termination Checking (`Termination.scala`)**
   - Every recursive `Fix` and mutually recursive `MutualFix` must have an inductive decreasing parameter at `recArgIdx` (shared across mutual definitions).
   - Every recursive call must be fully applied up to `recArgIdx` with a structurally strictly smaller subterm obtained from pattern matching on the decreasing parameter (including higher-order recursive fields such as `Acc.Intro`, which enables 0-axiom well-founded recursion via `termination_by`).
   - Unapplied or non-decreasing recursive references are rejected (`K020`), preventing `def loop(n: Nat): False = loop(n)` and mutual non-terminating cycles.
   - During NbE (`NbE.scala`), `Fix` and `MutualFix` only unfold when their decreasing argument is a constructor value (`VCtor`), guaranteeing termination of normalization.

5. **Total / Partial Isolation (`TypeChecker.scala`, `Env.scala`)**
   - `partial def` declarations may use unrestricted recursion, but cannot return a `Prop` type or universe sort (`K030`), are stored opaque in `KernelEnv` (never unfolded during type checking), and cannot be referenced by any total `def`, `theorem`, `enum`, or `axiom` (`K031`).
   - `#eval` evaluates `partial def` under both step and recursion-depth guards (`E033`), and code extraction transparently reports `partialFunctions` in `ExtractionManifest` (`--total` forbids any partial function).

6. **Exhaustiveness Checking (`TypeChecker.scala`)**
   - Every core `Match` must supply branches covering every constructor of the inductive type in order.
   - Surface matches on indexed families that omit provably unreachable constructors (such as `Vec[A](Nat.Succ(n))` omitting `Vec.Nil`) are compiled by the elaborator into discriminating motives and still verified in full by the kernel.

7. **Explicit Axiom & `sorry` Tracking (`Env.scala`)**
   - `KernelEnv` transitively tracks `axiomsUsed` for every checked definition and theorem.
   - `--strict` checking and strict code extraction fail if any axiom or `sorry` is used anywhere in the dependency cone.
