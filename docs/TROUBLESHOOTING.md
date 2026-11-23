# Kindful Guide to Kernel & Type Errors

When Proof Samurai rejects a definition or proof, **it is protecting logical soundness** — making sure it is impossible to prove `False` or extract buggy code. Here is what each error means in plain English, and how to fix it quickly.

## `K020` — Termination Error (Structural Recursion Guard)

**Why it happens:** If non-terminating functions like `def loop(n: Nat): False = loop(n)` were allowed, you could "prove" any false theorem! Therefore, every recursive `def` must pass a **structurally strictly smaller** subterm from pattern matching on a decreasing parameter.

**Common pitfall (reconstructing a value instead of passing the subterm):**
```scala
// Rejected by K020: `List.Cons(nextHead, rest)` is reconstructed, not a direct subterm!
case List.Cons(head, tail) =>
  tail match {
    case List.Cons(nextHead, rest) => isSortedBool(List.Cons(nextHead, rest))
  }
```

**Kindful fix (pass `tail` directly — faster AND provably terminating!):**
```scala
case List.Cons(head, tail) =>
  tail match {
    case List.Cons(nextHead, _) => isSortedBool(tail)
  }
```

## `K006` — Strict Positivity Violation

**Why it happens:** Allowing an inductive type `Bad` to appear on the left side of `=>` inside its own constructor (`case Mk(fn: Bad => False)`) leads to **Curry's paradox**, which breaks soundness.

**Kindful fix:** Avoid self-referential types in function argument positions (`Bad => ...`). Recursive occurrences in function *return* positions (like `case Lim(step: Nat => Ord)`) are strictly positive and completely allowed!

## `K025` — Illegal Elimination of `Prop` into `Type`

**Why it happens:** `Prop` proofs are erased when extracting runnable code. If a computational function tried to inspect `Or[P, Q]` or `Exists[A, P]` to decide whether to return `0` or `1`, the extracted code wouldn't know which branch to take!

**Kindful fix:**
- Use `Either[A, B]` (in `Type`) instead of `Or[P, Q]` when you need runtime branching.
- Use `Subset[A, P]` (in `Type`) instead of `Exists[A, P]` when you need to extract the witness `value: A` while erasing `proof: P(value)`.
- Note: `False` and `Eq` **are** subsingletons, so eliminating `False` (`absurd`) and `Eq` (`rewrite`/`subst`) into `Type` is always allowed!

## `K005` — Universe Level Exceeded (`Type0` vs `Type1`)

**Why it happens:** A small `Type` (`Type0`) inductive cannot store arbitrary `Type0` types inside a field (that would violate predicativity and allow Girard's paradox).

**Kindful fix:** Annotate the container enum as `: Type1` (e.g. `enum TypeBox: Type1 { case Mk(inner: Type) }`).

## `K026` / `E071` — Non-Exhaustive `match`

**Why it happens:** Missing a constructor case would create a partial function that crashes at runtime and breaks soundness.

**Kindful fix:** Handle every constructor of the matched `enum`, or add a catch-all `case _ => ...`. (For indexed families like `Vec[A](Nat.Succ(n))`, Proof Samurai automatically discharges provably impossible constructors like `Vec.Nil`!)

## `T010` — Reflexivity (`refl`) Failed

**Why it happens:** `refl` only closes `lhs === rhs` when both sides already reduce to the exact same term by computation.

**Kindful fix:**
- For `Nat` algebra (`+`, `*`, `0`, `Succ`), try **`arith`**!
- To unfold definitions and apply `@simp` lemmas, try **`simp`** or **`simp(*)`**!
- To inspect what is still different between LHS and RHS, replace `refl` with **`?check`**!

## `T015` — Rewrite Target Not Found

**Why it happens:** Either the goal hasn't been simplified yet, or the equality points in the opposite direction.

**Kindful fix:**
1. Run `simp` before `rewrite(lemma)`.
2. Try `rewriteRev(lemma)` (rewrites right-to-left) or `subst(lemma)`.
3. If the variable you want to rewrite is inside a hypothesis bound *before* `cases(x)`, call `revert(hypName)` before `cases(x)`!
