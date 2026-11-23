# 言語リファレンス

Proof Samurai はインデント非依存の **Scala 3 ブレース構文** を採用しています。`module`、`enum`、`def`、`theorem`、`match`、`if` / `else`、`calc`、`by` の各ブロックはすべて `{ ... }` で区切られます。

## 宣言構文

### 帰納的データ型（`enum`）

```scala
enum Nat: Type {
  case Zero
  case Succ(pred: Nat)
}

// 添字付き帰納族（長さ付きベクタ）
enum Vec[Element](size: Nat): Type {
  case Nil: Vec[Element](Nat.Zero)
  case Cons(tailSize: Nat, head: Element, tail: Vec[Element](tailSize)): Vec[Element](Nat.Succ(tailSize))
}

// 命題は Prop に属し、コード抽出時に完全に消去される
enum Le(lower: Nat, upper: Nat): Prop {
  case Refl(value: Nat): Le(value, value)
  case Step(lower: Nat, upper: Nat, prev: Le(lower, upper)): Le(lower, Nat.Succ(upper))
}
```

### レコード型（`case class`）

```scala
case class Pair[First, Second](first: First, second: Second)

def swap[A, B](pair: Pair[A, B]): Pair[B, A] = {
  Pair(pair.second, pair.first)
}
```

### 再帰関数（`def`）と定理（`theorem` / `lemma`）

- 角括弧の型パラメータ `[A, B]` は呼び出し側で暗黙引数として推論されます。
- 構造的再帰における減少引数は自動的に検出されます（必要に応じて `@decreasing(paramName)` で明示可能）。
- 定理の本体は直接の証明項として記述することも、`by { ... }` タクティクブロックで記述することもできます。
- `@simp` アノテーションを付けた等式定理は、`simp` タクティクの書き換え規則に登録されます。

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

## 演算子と糖衣構文

| 構文 | 意味 |
|---|---|
| `a === b`, `a !== b` | 命題的等価 `Eq` および否定 `Not(Eq)` |
| `P /\ Q`, `P \/ Q`, `~P` | 論理積 `And`、論理和 `Or`、否定 `Not` |
| `forall (x: A) => B` | 依存関数型 / 全称量化（`Pi`） |
| `exists (x: A) => P` | 存在命題（`Exists`） |
| `a + b`, `a - b`, `a * b` | `Nat` の算術演算（`add`, `sub`, `mul`） |
| `a == b`, `a != b`, `a <= b`, `a < b` | ブール値比較（`beq`, `ble`, `blt`） |
| `a && b`, `a \|\| b`, `!a` | ブール論理演算（`andBool`, `orBool`, `notBool`） |
| `h :: t`, `xs ++ ys`, `[1, 2, 3]`, `[]` | `List.Cons`、`append`、リストリテラルおよびリストパターン |
| `xs.length`, `pair.first` | UFCS 呼び出しおよび `case class` フィールド参照 |
| `0, 1, 2`, `true, false` | `Nat` リテラルおよび `Bool` リテラル |

## 等式推論（`calc { ... }`）

複数の等式変形を順序立てて記述できます。各ステップは内部で推移律（`Eq.trans`）のカーネル証明項に変換されます。

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

## 組み込みタクティク一覧（`by { ... }`）

- **基本構造**: `intro(x)`, `intros(x, y)`, `revert(x)`, `exact(term)`, `apply(term)`, `assumption`, `have(name: Type) { ... }`, `specialize(hyp, arg1, ...)`
- **等式操作**: `refl`, `symmetry`, `trans(mid)`, `rewrite(h1, h2, ...)`, `rewriteRev(h1, ...)`, `subst(eq)`, `congr`
- **帰納型**: `induction(x) { case ... => { ... } }`, `cases(expr) { case ... => { ... } }`, `cases(expr, eqHyp) { case ... => { ... } }`, `discriminate`, `injection(h, name)`
- **命題論理**: `split`, `left`, `right`, `exists(witness)`, `contradiction`, `exfalso`
- **自動化**: `unfold(defName)`, `simp`, `simp(*)`, `simp(lem1, lem2)`, `arith` / `ring`（公理 0 の `Nat` 可換半環ソルバ）, `trivial`, `decide`, `auto`（別名 `samurai`）
- **開発支援**: `?holeName`（未完ゴール検査）, `sorry`（カーネルの信頼レポートで明示的に追跡される）
