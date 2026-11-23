# Kernel & Type Error Guide

When Proof Samurai rejects a definition or proof, the check is enforcing logical soundness (preventing proofs of `False` and ensuring safe extraction). Below are common error codes, their causes, and fixes.

## `K020` — Termination Error (Structural Recursion Guard)

**Cause:** Allowing non-terminating functions such as `def loop(n: Nat): False = loop(n)` would make the logic inconsistent. Every recursive `def` must pass a structurally strictly smaller subterm obtained from pattern matching on a decreasing parameter.

**Rejected example (reconstructing a value instead of passing the subterm):**

```scala
// Rejected by K020: List.Cons(nextHead, rest) is reconstructed, not a direct subterm
case List.Cons(head, tail) =>
  tail match {
    case List.Cons(nextHead, rest) => isSortedBool(List.Cons(nextHead, rest))
  }
```

**Fix (pass the pattern-matched `tail` directly):**

```scala
case List.Cons(head, tail) =>
  tail match {
    case List.Cons(nextHead, _) => isSortedBool(tail)
  }
```

## `K006` — Strict Positivity Violation

**Cause:** Allowing an inductive type `Bad` to appear on the left side of `=>` inside its own constructor (`case Mk(fn: Bad => False)`) enables Curry's paradox.

**Fix:** Do not place the inductive type in function argument positions (`Bad => ...`). Recursive occurrences in function return positions (such as `case Lim(step: Nat => Ord)`) are strictly positive and permitted.

## `K025` — Illegal Elimination of `Prop` into `Type`

**Cause:** `Prop` terms are erased during code extraction. If a computational function inspects `Or[P, Q]` or `Exists[A, P]` to decide which value to return, the erased program would lack the runtime branch information.

**Fix:**
- Use `Either[A, B]` (in `Type`) instead of `Or[P, Q]` when runtime branching is needed.
- Use `Subset[A, P]` (in `Type`) instead of `Exists[A, P]` when extracting a witness `value: A` while erasing `proof: P(value)`.
- `False` and `Eq` are subsingletons, so eliminating `False` (`absurd`) and `Eq` (`rewrite` / `subst`) into `Type` is permitted.

## `K005` — Universe Level Exceeded (`Type0` vs `Type1`)

**Cause:** A `Type` (`Type0`) inductive cannot store arbitrary `Type0` types inside a field, as that would violate predicativity and allow Girard's paradox.

**Fix:** Annotate the container enum as `: Type1` (for example, `enum TypeBox: Type1 { case Mk(inner: Type) }`).

## `K026` / `E071` — Non-Exhaustive `match`

**Cause:** Omitting a constructor creates a partial function that can crash at runtime and break soundness.

**Fix:** Handle every constructor of the matched `enum`, or add a fallback `case _ => ...`. For indexed families such as `Vec[A](Nat.Succ(n))`, provably unreachable constructors like `Vec.Nil` are discharged automatically by the elaborator.

## `K030` / `K031` — Partial Function Soundness & Isolation

**Cause:**
- `K030`: A `partial def` attempted to return a `Prop` type (which would let a diverging loop inhabit `False`).
- `K031`: A total `def` or `theorem` referenced a `partial def` (which could leak non-termination into the logical fragment).

**Fix:**
- If the function actually terminates by a `Nat` measure (such as division, GCD, or Quicksort), use `import WellFounded.*` with a `termination_by { ... }` clause instead of `partial def`.
- Keep `partial def` at the computational boundary returning `Type`, and call it only from other `partial def`s or extracted host code.

## `T010` — Reflexivity (`refl`) Failed

**Cause:** `refl` closes `lhs === rhs` only when both sides reduce to the exact same normal form by computation.

**Fix:**
- For `Nat` semiring equalities (`+`, `*`, `0`, `Succ`), use `arith`.
- To unfold definitions and apply `@simp` lemmas, use `simp` or `simp(*)`.
- To inspect the remaining difference between both sides, replace `refl` with `?check`.

## `T015` — Rewrite Target Not Found

**Cause:** The goal either has not unfolded the relevant definition yet, or the equality points in the opposite direction.

**Fix:**
1. Run `simp` before `rewrite(lemma)`.
2. Try `rewriteRev(lemma)` (right-to-left) or `subst(lemma)`.
3. If the variable to rewrite appears in a hypothesis introduced before `cases(x)`, call `revert(hypName)` before `cases(x)`.
