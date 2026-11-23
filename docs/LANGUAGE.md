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
- **Structure**: `intro(x)`, `intros(x, y)`, `revert(x)`, `exact(term)`, `apply(term)`, `assumption`, `have(name: Type) { ... }`, `specialize(hyp, arg1, ...)`
- **Equality**: `refl`, `symmetry`, `trans(mid)`, `rewrite(h1, h2, ...)`, `rewriteRev(h1, ...)`, `subst(eq)`, `congr`
- **Inductives**: `induction(x) { case ... => { ... } }`, `cases(expr) { case ... => { ... } }`, `cases(expr, eqHyp) { case ... => { ... } }`, `discriminate`, `injection(h, name)`
- **Logic**: `split`, `left`, `right`, `exists(witness)`, `contradiction`, `exfalso`
- **Automation**: `unfold(defName)`, `simp`, `simp(*)`, `simp(lem1, lem2)`, `arith` / `ring` (sound proof-producing Nat commutative semiring solver), `trivial`, `decide`, `auto` (or `samurai`)
- **Development**: `?holeName`, `sorry` (explicitly tracked in kernel trust reports!)
