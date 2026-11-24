# タクティク・クックブック

タクティクをアルファベット順に暗記するのではなく、現在のゴールの形から適切なタクティクを選ぶための実践リファレンスです。

以下の各タクティクはいずれも裏側で通常の関数項（ラムダ・`match`・コンストラクタ呼び出し・再帰呼び出し・安全な等式キャスト）を生成し、最終的に信頼カーネルが検証します。通常の `def` で書いた証明との具体的な見比べは第 02 章「証明とタクティクは通常のプログラムと何の関係があるのか」を参照してください。

## ゴール形状別リファレンス

| 現在のゴール・状況 | 最初に試すタクティク | 通常コードでの対応 | 動作 |
|---|---|---|---|
| `a === b`（具体値。例: `2 + 3 === 5`） | `refl` または `decide` | `Eq.Refl`（コンパイル時評価） | 両辺を正規化して一致すれば証明完了 |
| `a === b`（`+`, `*`, `0`, `Succ` から成る `Nat` の等式） | `arith`（または `ring`） | ボイラープレート自動合成 | 可換半環の恒等式を公理 0 の証明項で一括証明 |
| `a === b`（`@simp` 補題や関数定義を含む） | `simp` または `simp(*)` | ボイラープレート自動合成 | 定義展開・`@simp` 規則適用（`*` は局所等式仮定も使用） |
| `f(a) === f(b)` | `congr` | `congrArg(f, ...)` | `a === b` の証明へ帰着 |
| `a === c`（中間式 `b` を経由したい） | `trans(b)` または `calc { ... }` | 等式キャストの連鎖 | `a === b` と `b === c` に分割 |
| `a === b`（仮定に `h: b === a` がある） | `symmetry` | `eqSym(...)` | ゴールを `b === a` に反転 |
| `forall (x: A) => ...` または `P => Q` | `intro(x)` / `intros(x, y)` | `(x, y) => ...` | 束縛変数や前提を仮定へ移動 |
| `P /\ Q` | `split` | `And.Intro(?, ?)`（2 要素タプル） | `P` と `Q` の 2 つのサブゴールに分割 |
| `P \/ Q` | `left` または `right` | `Or.Inl(?)` / `Or.Inr(?)`（`Either`） | 証明する側の分岐を選択 |
| `exists (x: A) => P(x)` | `exists(witness)` | `Exists.Intro(w, ?)`（値と証拠のペア） | 具体的な証人（witness）を提示 |
| 命題論理の組合せ（`=>`, `/\`, `\/`, `~`） | `auto`（または `samurai`） | ボイラープレート自動合成 | 探索を行い、カーネル検証済みの証明項を合成 |
| 矛盾する等式仮定 `h: 0 === Nat.Succ(n)` や `true === false` | `discriminate(h)` | 到達不能分岐の消去（`Nothing`） | コンストラクタの非交性により任意のゴールを閉じる |
| 同一コンストラクタの等式 `h: Nat.Succ(a) === Nat.Succ(b)` | `injection(h, eqAB)` | コンストラクタ引数分解 | 引数の等式 `eqAB : a === b` を仮定に追加 |
| 仮定に `h: False` がある、または `P` と `~P` の両方がある | `contradiction` | `False` の空 `match` | 矛盾から即座にゴールを閉じる |
| 背理法的に `False` を導きたい | `exfalso` | `absurd(falseProof)` | ゴールを `False` に変更 |

## パターン 1: 連続書き換え（`rewrite` / `rewriteRev`）

複数の等式による書き換えを 1 行にまとめて記述できます。

```scala
import Prelude.*
import Nat.*

theorem chainRewrites(first: Nat, second: Nat, third: Nat, eq1: first === second, eq2: second === third):
  first + 1 === third + 1 = by {
  rewrite(eq1, eq2)
  refl
}
```

右辺から左辺の向きに書き換える場合は `rewriteRev(lemma)` を使います。どちらの向きでも自動試行したい場合は `subst(eqHyp)` が便利です。

## パターン 2: 条件式を記憶したケース分割（`cases(expr, eqHyp)`）

`if (ble(x, y))` を含む関数の性質を証明するとき、各分岐の中で `ble(x, y)` が `true` だったか `false` だったかの等式仮定が必要になることがあります。`cases` の第 2 引数に仮定名を渡すと、各分岐に等式仮定が束縛されます。

```scala
cases(ble(element, head), cmpEq) {
  case True => {
    // この分岐では cmpEq : ble(element, head) === true が利用可能
  }
  case False => {
    // この分岐では cmpEq : ble(element, head) === false が利用可能
  }
}
```

この機構は純粋な `Eq.Refl` のモチーフ構成で実装されており、公理を一切追加しません。

## パターン 3: 帰納法前の一般化（`revert`）

帰納法の仮定を、別の変数 `right` の特定の値に対してだけでなく**すべての `right`** に対して適用したい場合は、`induction(left)` の直前に `revert(right)` を呼び出します。

```scala
import Prelude.*
import Nat.*

theorem bleTotalExample(left: Nat, right: Nat):
  (ble(left, right) === true) \/ (ble(right, left) === true) = by {
  revert(right)
  exact(bleTotal(left))
}
```

## パターン 4: 前向き推論（`have` と `specialize`）

複雑な証明を名前付きの中間事実へ分割するには `have(name: Type) { ... }` を使用します。

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

## パターン 5: 再帰データ型に対する構造的帰納法（`Nat`, `List`, `Tree`）

`induction(x)` は添字のない任意の帰納型に対して機能し、再帰フィールドごとに帰納法の仮定（二分木 `Tree.Node` であれば `ihLeft`, `ihRight` の 2 つ）を自動生成します。

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
