# Tactic Cookbook

Look up tactics by the shape of your current goal rather than memorizing an alphabetical list.

Every tactic below generates an ordinary kernel-checked function term (lambdas, `match` expressions, constructor calls, recursive calls, or type-safe equality casts). See **How Proofs & Tactics Relate to Ordinary Programs** (Chapter 02) for side-by-side comparisons of direct `def` proofs vs. `by { ... }` tactic scripts.

## Reference by Goal Shape

| Current Goal / Context | First Tactic to Try | Programming Equivalent | Behavior |
|---|---|---|---|
| `a === b` (concrete values, e.g. `2 + 3 === 5`) | `refl` or `decide` | `Eq.Refl` (compile-time eval) | Normalizes both sides and closes if equal |
| `a === b` (`Nat` with `+`, `*`, `0`, `Succ`) | `arith` (or `ring`) | Verified boilerplate generator | Proves commutative semiring `Nat` identities with 0 axioms |
| `Le` / `Lt` / `ble` / `blt` / `beq` / linear `Nat` arithmetic & inequalities | `omega` (or `lia`) | Verified linear solver | Proves `Nat` ordering chains, cancellation, antisymmetry, and contradictions with 0 axioms |
| Chained equalities, congruence `f(a) === f(b)`, injectivity, disjointness | `cc` | Verified E-graph / congruence closure | Closes multi-hop equalities & constructor contradictions automatically (0 axioms) |
| Intuitionistic propositional logic (`=>`, `/\`, `\/`, `~`, `Iff`) | `tauto` | Verified propositional solver | Complete intuitionistic tautology solver (0 axioms) |
| `a === b` (with `@simp` lemmas or definitions) | `simp` / `simp(*)` / `simp in h` | Verified boilerplate generator | Unfolds definitions and rewrites goal, hypothesis `h`, or `*` |
| `f(a) === f(b)` | `congr` | `congrArg(f, ...)` | Reduces to proving `a === b` |
| `a === c` (via an intermediate expression `b`) | `trans(b)` or `calc { ... }` | Chained equality casts | Splits into `a === b` and `b === c` |
| `a === b` (have hypothesis `h: b === a`) | `symmetry` | `eqSym(...)` | Flips the goal to `b === a` |
| `forall (x: A) => ...` or `P => Q` | `intro(x)` / `intros(x, y)` | `(x, y) => ...` | Moves binders or premises into local hypotheses |
| `P /\ Q` | `split` | `And.Intro(?, ?)` (2-tuple) | Splits into two subgoals: `P` and `Q` |
| `P \/ Q` | `left` or `right` | `Or.Inl(?)` / `Or.Inr(?)` (`Either`) | Selects which side of the disjunction to prove |
| `exists (x: A) => P(x)` | `exists(witness)` | `Exists.Intro(w, ?)` (value + proof pair) | Supplies a concrete witness |
| Propositional logic (`=>`, `/\`, `\/`, `~`) | `auto` (or `samurai`) | Verified boilerplate generator | Performs bounded search and synthesizes a kernel-checked term |
| Conflicting constructor equality `h: 0 === Nat.Succ(n)` or `true === false` | `discriminate(h)` | Unreachable branch (`Nothing`) | Closes any goal by constructor disjointness |
| Same-constructor equality `h: Nat.Succ(a) === Nat.Succ(b)` | `injection(h, eqAB)` | Constructor field extraction | Extracts `eqAB : a === b` into hypotheses |
| `h: False` or both `P` and `~P` in hypotheses | `contradiction` | Exhaustive match on `False` | Closes any goal immediately |
| Proving the goal by deriving a contradiction | `exfalso` | `absurd(falseProof)` | Replaces the goal with `False` |

## Pattern 1: Chained Rewriting (`rewrite` and `rewriteRev`)

Multiple rewrites can be chained in one call:

```scala
import Prelude.*
import Nat.*

theorem chainRewrites(first: Nat, second: Nat, third: Nat, eq1: first === second, eq2: second === third):
  first + 1 === third + 1 = by {
  rewrite(eq1, eq2)
  refl
}
```

Use `rewriteRev(lemma)` to rewrite right-to-left (`rhs` -> `lhs`), or `subst(eqHyp)` to attempt either direction automatically.

## Pattern 2: Case Splitting While Keeping the Branch Equation (`cases(expr, eqHyp)`)

When reasoning about functions containing `if (ble(x, y))`, you often need an equality hypothesis recording whether `ble(x, y)` evaluated to `true` or `false` inside each branch. Pass a second argument to `cases`:

```scala
cases(ble(element, head), cmpEq) {
  case True => {
    // cmpEq : ble(element, head) === true is in scope
  }
  case False => {
    // cmpEq : ble(element, head) === false is in scope
  }
}
```

This is compiled into a pure `Eq.Refl` motive and requires zero axioms.

## Pattern 3: Generalizing Before Induction (`revert`)

If an induction hypothesis must hold for all values of a second variable `right` rather than one fixed value, call `revert(right)` immediately before `induction(left)`:

```scala
import Prelude.*
import Nat.*

theorem bleTotalExample(left: Nat, right: Nat):
  (ble(left, right) === true) \/ (ble(right, left) === true) = by {
  revert(right)
  exact(bleTotal(left))
}
```

## Pattern 4: Forward Reasoning with `have` and `specialize`

Introduce named intermediate facts with `have(name: Type) { ... }`:

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

`induction(x)` works on any non-indexed inductive type and generates one induction hypothesis per recursive field (for example, `ihLeft` and `ihRight` on a binary `Tree.Node`):

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

## Pattern 6: Practical Automation (`omega`, `cc`, `tauto`) and Combinators (`<;>`, `in hyp`, `obtain`, `by_cases`)

Combine proof-producing decision procedures with goal combinators to keep real-world proofs short and readable:

```scala
import Prelude.*
import Nat.*
import WellFounded.*

// Linear Nat inequalities, cancellation, antisymmetry, and constructive contradiction
theorem strictFromNeq(a: Nat, b: Nat, hLe: Le(a, b), hNeq: a !== b): Lt(a, b) = by {
  omega
}

// Multi-hop equality & function congruence
theorem congruenceChain[A](f: A => A, g: A => A, a: A, b: A, c: A, h1: a === b, h2: f(b) === c):
  g(f(a)) === g(c) = by {
  cc
}

// Rewriting and simplifying inside hypotheses (`in h` or `in *`)
theorem rewriteHyp(a: Nat, b: Nat, c: Nat, hEq: a === b, hLe: Le(a + 1, c)): Le(b, c) = by {
  rewrite(hEq) in hLe
  omega
}

// Flat destructuring (`obtain`) and multi-subgoal chaining (`<;>`, `by_cases`, `first`, `try`, `all`)
theorem totalOrder(a: Nat, b: Nat): (ble(a, b) === true) \/ (ble(b, a) === true) = by {
  by_cases(ble(a, b), cmp) <;> first { { left; omega } | { right; omega } }
}
```


## Pattern 7: Worked Examples, One Tactic at a Time

Every proof below is taken verbatim from [`examples/TacticGallery.samurai`](https://github.com/kmizu/proof-samurai/blob/main/examples/TacticGallery.samurai), which is verified axiom-free by the test suite (`sbt "run check examples/TacticGallery.samurai --strict"`). The comment above each one says which ordinary program the tactic is building.

### Logic is programming: `intros`, `obtain`, `left`, `split`, `exists`

```scala
// A proof of `P => Q => R` is a curried function; swapping arguments is a proof.
theorem swapArgs(P: Prop, Q: Prop, R: Prop): (P => Q => R) => (Q => P => R) = by {
  intros(f, q, p)
  exact(f(p, q))
}

// `/\` is a pair (`obtain` unpacks it); `\/` is Either (`left` picks `Inl`).
theorem andImpliesOr(P: Prop, Q: Prop): (P /\ Q) => (P \/ Q) = by {
  intro(h)
  obtain(hp, hq) = h
  left
  exact(hp)
}

// Building a pair means supplying both components.
theorem andFromBoth(P: Prop, Q: Prop, hp: P, hq: Q): Q /\ P = by {
  split
  exact(hq)
  exact(hp)
}

// An existential is a (witness, proof) pair: `Exists.Intro(Succ(n), Eq.Refl)`.
theorem hasSuccessor(n: Nat): exists (m: Nat) => m === Nat.Succ(n) = by {
  exists(Nat.Succ(n))
  refl
}
```

### Computation and constructors: `refl`, `decide`, `discriminate`, `injection`, `contradiction`

```scala
theorem sixTimesSeven: 6 * 7 === 42 = by { refl }       // closed by running the program
theorem threeIsNotTen: ~Le(10, 3) = by { decide }       // decidable, so evaluate it

// Different constructors never collide; the same constructor is injective.
theorem succIsNotZero(n: Nat, h: Nat.Succ(n) === 0): False = by {
  discriminate(h)
}

theorem succCancel(a: Nat, b: Nat, h: Nat.Succ(a) === Nat.Succ(b)): a === b = by {
  injection(h, eq)
  exact(eq)
}

// `P` and `~P` together prove any goal.
theorem fromContradiction(P: Prop, hp: P, hnp: ~P): 1 === 2 = by {
  contradiction
}
```

### Equational reasoning: `symmetry`, `trans`, `calc`, `simp in h`

```scala
theorem meetInTheMiddle(a: Nat, b: Nat, c: Nat, h1: a === b, h2: c === b): a === c = by {
  trans(b)
  exact(h1)
  symmetry
  exact(h2)
}

theorem calcExample(a: Nat, b: Nat): (a + b) + 0 === b + a = {
  calc {
    (a + b) + 0
    === a + b by { simp }
    === b + a by { arith }
  }
}

theorem simplifyHypothesis(a: Nat, b: Nat, h: (a + 0) === (b + 0)): a === b = by {
  simp in h
  exact(h)
}
```

### Automation: `arith`, `omega`, `cc`, `tauto`, `auto`

```scala
theorem squareOfSum(a: Nat, b: Nat): (a + b) * (a + b) === a * a + 2 * (a * b) + b * b = by {
  arith
}

theorem windowBound(x: Nat, lo: Le(10, x), hi: Le(x, 20)): Le(x, 25) = by {
  omega
}

theorem congruenceChain(f: Nat => Nat, a: Nat, b: Nat, c: Nat, h1: a === b, h2: f(b) === c):
  f(f(a)) === f(c) = by {
  cc
}

theorem distribute(P: Prop, Q: Prop, R: Prop): (P /\ (Q \/ R)) => ((P /\ Q) \/ (P /\ R)) = by {
  tauto
}
```

### Proving things about your own functions: `induction`, `by_cases`

```scala
def double(n: Nat): Nat = {
  n match {
    case Nat.Zero => 0
    case Nat.Succ(pred) => Nat.Succ(Nat.Succ(double(pred)))
  }
}

// The induction hypothesis `ih` is just the recursive call on `pred`.
theorem doubleIsAddSelf(n: Nat): double(n) === n + n = by {
  induction(n) {
    case Zero => { refl }
    case Succ(pred, ih) => {
      simp
      rewrite(ih)
      refl
    }
  }
}

def total(items: List[Nat]): Nat = {
  items match {
    case List.Nil => 0
    case List.Cons(head, tail) => head + total(tail)
  }
}

theorem totalOfAppend(first: List[Nat], second: List[Nat]):
  total(first ++ second) === total(first) + total(second) = by {
  induction(first) {
    case Nil => { simp }
    case Cons(head, tail, ih) => {
      simp
      rewrite(ih)
      arith
    }
  }
}

// Branch on the Bool test inside the function, then let `omega` finish each branch.
def clamp(x: Nat, cap: Nat): Nat = {
  if (x <= cap) { x } else { cap }
}

theorem clampStaysBelowCap(x: Nat, cap: Nat): Le(clamp(x, cap), cap) = by {
  unfold(clamp)
  by_cases(ble(x, cap), cmp) <;> { simp; omega }
}
```
