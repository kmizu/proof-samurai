# タクティク・クックブック

タクティクをアルファベット順に暗記するのではなく、現在のゴールの形から適切なタクティクを選ぶための実践リファレンスです。

以下の各タクティクはいずれも裏側で通常の関数項（ラムダ・`match`・コンストラクタ呼び出し・再帰呼び出し・安全な等式キャスト）を生成し、最終的に信頼カーネルが検証します。通常の `def` で書いた証明との具体的な見比べは第 02 章「証明とタクティクは通常のプログラムと何の関係があるのか」を参照してください。

## ゴール形状別リファレンス

| 現在のゴール・状況 | 最初に試すタクティク | 通常コードでの対応 | 動作 |
|---|---|---|---|
| `a === b`（具体値。例: `2 + 3 === 5`） | `refl` または `decide` | `Eq.Refl`（コンパイル時評価） | 両辺を正規化して一致すれば証明完了 |
| `a === b`（`+`, `*`, `0`, `Succ` から成る `Nat` の等式） | `arith`（または `ring`） | ボイラープレート自動合成 | 可換半環の恒等式を公理 0 の証明項で一括証明 |
| `Le`・`Lt`・`ble`・`blt`・`beq`・線形 `Nat` 不等式と矛盾 | `omega`（または `lia`） | 線形算術ソルバ（公理 0） | 推移律・両辺消去・反対称性・背理法を一括証明 |
| 等式連鎖・合同 `f(a) === f(b)`・単射性・矛盾 | `cc` | 合同閉包ソルバ（公理 0） | 多段等式置換・関数適用合同・コンストラクタ矛盾を自動証明 |
| 直観主義命題論理（`=>`, `/\`, `\/`, `~`, `Iff`） | `tauto` | 命題論理決定手続き（公理 0） | 対偶・ド・モルガン・分配則等の恒真式を一括証明 |
| `a === b`（`@simp` 補題や関数定義を含む） | `simp` / `simp(*)` / `simp in h` | ボイラープレート自動合成 | ゴール・仮定 `h`・全体 `*` を定義展開と `@simp` で簡約 |
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

## パターン 6: 実用的な自動証明（`omega`・`cc`・`tauto`）とコンビネータ（`<;>`・`in hyp`・`obtain`・`by_cases`）

証明生成型の決定手続きとタクティクコンビネータを組み合わせることで、実務的な証明を短く保てます。

```scala
import Prelude.*
import Nat.*
import WellFounded.*

// 線形 Nat 不等式・両辺消去・反対称性・構成的背理法
theorem strictFromNeq(a: Nat, b: Nat, hLe: Le(a, b), hNeq: a !== b): Lt(a, b) = by {
  omega
}

// 多段の等式連鎖と関数適用の合同閉包
theorem congruenceChain[A](f: A => A, g: A => A, a: A, b: A, c: A, h1: a === b, h2: f(b) === c):
  g(f(a)) === g(c) = by {
  cc
}

// 仮定の中身を直接書き換え・簡約（`in h` / `in *`）
theorem rewriteHyp(a: Nat, b: Nat, c: Nat, hEq: a === b, hLe: Le(a + 1, c)): Le(b, c) = by {
  rewrite(hEq) in hLe
  omega
}

// フラット分解（`obtain`）と全サブゴール連鎖（`<;>`, `by_cases`, `first`, `try`, `all`）
theorem totalOrder(a: Nat, b: Nat): (ble(a, b) === true) \/ (ble(b, a) === true) = by {
  by_cases(ble(a, b), cmp) <;> first { { left; omega } | { right; omega } }
}
```


## パターン 7: タクティクを 1 つずつ試す実例集

以下の証明はすべて [`examples/TacticGallery.samurai`](https://github.com/kmizu/proof-samurai/blob/main/examples/TacticGallery.samurai) からそのまま引用しています。このファイルはテストスイートで公理 0 として検証されます（`sbt "run check examples/TacticGallery.samurai --strict"`）。各証明の上のコメントに、そのタクティクが裏でどんな通常のプログラムを組み立てているかを書いています。

### 論理はプログラミング: `intros`, `obtain`, `left`, `split`, `exists`

```scala
// `P => Q => R` の証明はカリー化された関数。引数の順序を入れ替える関数がそのまま証明になる。
theorem swapArgs(P: Prop, Q: Prop, R: Prop): (P => Q => R) => (Q => P => R) = by {
  intros(f, q, p)
  exact(f(p, q))
}

// `/\` はペア（`obtain` で分解）、`\/` は Either（`left` で `Inl` を選ぶ）。
theorem andImpliesOr(P: Prop, Q: Prop): (P /\ Q) => (P \/ Q) = by {
  intro(h)
  obtain(hp, hq) = h
  left
  exact(hp)
}

// ペアを作るには両方の要素を渡す。
theorem andFromBoth(P: Prop, Q: Prop, hp: P, hq: Q): Q /\ P = by {
  split
  exact(hq)
  exact(hp)
}

// 存在命題は (証人, 証明) のペア: `Exists.Intro(Succ(n), Eq.Refl)`。
theorem hasSuccessor(n: Nat): exists (m: Nat) => m === Nat.Succ(n) = by {
  exists(Nat.Succ(n))
  refl
}
```

### 計算とコンストラクタ: `refl`, `decide`, `discriminate`, `injection`, `contradiction`

```scala
theorem sixTimesSeven: 6 * 7 === 42 = by { refl }       // プログラムを実行して閉じる
theorem threeIsNotTen: ~Le(10, 3) = by { decide }       // 決定可能なので評価して判定

// 異なるコンストラクタは衝突せず、同じコンストラクタは単射。
theorem succIsNotZero(n: Nat, h: Nat.Succ(n) === 0): False = by {
  discriminate(h)
}

theorem succCancel(a: Nat, b: Nat, h: Nat.Succ(a) === Nat.Succ(b)): a === b = by {
  injection(h, eq)
  exact(eq)
}

// `P` と `~P` が同時にあれば、どんなゴールも証明できる。
theorem fromContradiction(P: Prop, hp: P, hnp: ~P): 1 === 2 = by {
  contradiction
}
```

### 等式推論: `symmetry`, `trans`, `calc`, `simp in h`

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

### 自動化: `arith`, `omega`, `cc`, `tauto`, `auto`

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

### 自作関数についての証明: `induction`, `by_cases`

```scala
def double(n: Nat): Nat = {
  n match {
    case Nat.Zero => 0
    case Nat.Succ(pred) => Nat.Succ(Nat.Succ(double(pred)))
  }
}

// 帰納法の仮定 `ih` は `pred` に対する再帰呼び出しそのもの。
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

// 関数内の Bool 判定で分岐し、各分岐を `omega` に任せる。
def clamp(x: Nat, cap: Nat): Nat = {
  if (x <= cap) { x } else { cap }
}

theorem clampStaysBelowCap(x: Nat, cap: Nat): Le(clamp(x, cap), cap) = by {
  unfold(clamp)
  by_cases(ble(x, cap), cmp) <;> { simp; omega }
}
```
