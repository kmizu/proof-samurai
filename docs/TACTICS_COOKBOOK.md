# Friendly Tactic Cookbook

Instead of memorizing an alphabetical list of tactics, look up **what your current goal looks like** and pick the recipe that fits.

## Quick Cheat Sheet by Goal Shape

| What your goal looks like | First tactic to try | What it does |
|---|---|---|
| `a === b` (concrete values, e.g. `2 + 3 === 5`) | `refl` or `decide` | Computes both sides and closes if equal |
| `a === b` (`Nat` with `+`, `*`, `0`, `Succ`) | `arith` (or `ring`) | Proves any commutative semiring `Nat` identity in 1 step! |
| `a === b` (with `@simp` lemmas or definitions) | `simp` or `simp(*)` | Simplifies definitions, `@simp` lemmas, and (`*`) local equalities |
| `f(a) === f(b)` | `congr` | Reduces to proving `a === b` |
| `a === c` (needs an intermediate expression `b`) | `trans(b)` or `calc { ... }` | Splits into `a === b` and `b === c` |
| `a === b` (have hypothesis `h: b === a`) | `symmetry` | Flips goal to `b === a` |
| `forall (x: A) => ...` or `P => Q` | `intro(x)` / `intros(x, y)` | Moves binders/premises into your hypotheses |
| `P /\ Q` | `split` | Splits into two subgoals: `P` and `Q` |
| `P \/ Q` | `left` or `right` | Choose which side of the disjunction to prove |
| `exists (x: A) => P(x)` | `exists(witness)` | Supplies a concrete witness value |
| Pure propositional logic (`=>`, `/\`, `\/`, `~`) | `auto` (or `samurai`) | Searches and verifies a complete proof automatically |
| Have impossible `h: 0 === Nat.Succ(n)` or `h: true === false` | `discriminate(h)` | Closes **any** goal by constructor disjointness |
| Have `h: Nat.Succ(a) === Nat.Succ(b)` | `injection(h, eqAB)` | Extracts `eqAB : a === b` into hypotheses |
| Have `h: False` or both `P` and `~P` | `contradiction` | Closes **any** goal immediately |
| Want to prove goal by deriving a contradiction | `exfalso` | Changes goal to `False` |

## Pattern 1: Rewriting Chains (`rewrite` & `rewriteRev`)

You can chain multiple rewrites in a single readable line:

```scala
import Prelude.*
import Nat.*

theorem chainRewrites(first: Nat, second: Nat, third: Nat, eq1: first === second, eq2: second === third):
  first + 1 === third + 1 = by {
  rewrite(eq1, eq2)
  refl
}
```

Use `rewriteRev(lemma)` to rewrite right-to-left (`rhs` → `lhs`), or `subst(eqHyp)` to try either direction automatically.

## Pattern 2: Case Splitting on `if (cond)` While Remembering the Condition!

When proving properties about functions containing `if (ble(x, y))`, you often need to **remember** whether `ble(x, y)` was `true` or `false` inside each branch. Pass a second argument to `cases`:

```scala
cases(ble(element, head), cmpEq) {
  case True => {
    // Here `cmpEq : ble(element, head) === true` is in scope!
  }
  case False => {
    // Here `cmpEq : ble(element, head) === false` is in scope!
  }
}
```

This is 100% kernel-verified with zero axioms (built from a pure `Eq.Refl` motive).

## Pattern 3: Generalizing Before Induction (`revert`)

If your induction hypothesis needs to hold for *all* values of a second variable `right` (not just one fixed `right`), call `revert(right)` right before `induction(left)`:

```scala
import Prelude.*
import Nat.*

theorem bleTotalExample(left: Nat, right: Nat):
  (ble(left, right) === true) \/ (ble(right, left) === true) = by {
  revert(right)
  exact(bleTotal(left))
}
```

## Pattern 4: Forward Reasoning with `have` & `specialize`

Break complex proofs into readable, named checkpoints with `have(name: Type) { ... }`:

```scala
import Prelude.*
import Nat.*

theorem forwardReasoning(left: Nat, right: Nat, eqLR: left === right):
  Nat.Succ(left) === Nat.Succ(right) = by {
  have(step: left + 1 === right + 1) {
    rewrite(eqLR)
    refl
  }
  rewrite(eqLR)
  refl
}
```

## Pattern 5: Induction on Recursive Data Types (`Nat`, `List`, `Tree`)

`induction(x)` works on **any** non-indexed inductive type and automatically generates one induction hypothesis per recursive field (e.g. `ihLeft`, `ihRight` on a binary `Tree.Node`):

```scala
import Prelude.*
import Tree.*

theorem mirrorTwice[Element](tree: Tree[Element]): mirror(mirror(tree)) === tree = by {
  induction(tree) {
    case Leaf => { refl }
    case Node(left, value, right, ihLeft, ihRight) => {
      simp
      rewrite(ihLeft, ihRight)
      refl
    }
  }
}
```
