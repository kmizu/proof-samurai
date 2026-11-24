# 証明とタクティクは通常のプログラムと何の関係があるのか

証明支援系を初めて触るプログラマが最も疑問に思いやすいのは、次の 2 点です。

1. `intro`、`cases`、`induction`、`rewrite`、`split` といった**タクティクは一体何をしているのか**（通常のプログラミングと別世界の儀式なのか）。
2. 証明を書くことが、**実際に動く本番プログラムにどう効いてくるのか**。

この章では、型理論の専門用語を使わず、通常の関数型プログラミング（Scala / TypeScript / Rust）との対応関係だけで説明します。

---

## 1. 証明の実体は「ただの関数」であり、タクティクはその関数を書く補助ツール

Proof Samurai では、`theorem` と `def` に**本質的な違いはありません**。

- **型（命題）** = 「入力に対して満たすべき仕様」
- **証明** = 「その仕様（型）の値を返す、普通の純粋関数」
- **タクティク（`by { ... }`）** = 「その関数本体（`match`・ラムダ・再帰呼び出し）を、コンパイラに型を確認させながら少しずつ組み立てるためのコード生成コマンド」

実際のコードで見比べると一目で分かります。

### 例 1: 論理積の入れ替え（`And` = ただの 2 要素タプル）

`P /\ Q`（`And[P, Q]`）は、`case Intro(left: P, right: Q)` を持つ 2 要素の `case class`（タプル）と同じです。次の 2 つは、**カーネルに渡る実体が同じ関数**になります。

```scala
import Prelude.*

// 通常の関数として直接書いた版（タクティク不使用）
def andCommAsFunction(left: Prop, right: Prop, both: left /\ right): right /\ left = {
  both match {
    case And.Intro(leftProof, rightProof) => And.Intro[right, left](rightProof, leftProof)
  }
}

// まったく同じ関数を by { ... } タクティクで組み立てた版
theorem andCommWithTactics(left: Prop, right: Prop, both: left /\ right): right /\ left = by {
  cases(both) {
    case Intro(leftProof, rightProof) => {
      split
      exact(rightProof)
      exact(leftProof)
    }
  }
}
```

対応関係は次の通りです。

- `cases(both)` → `both match { ... }` を書く
- `split` → `And.Intro(?, ?)` というコンストラクタ呼び出しを作り、引数を 2 つのサブゴールに分ける
- `exact(rightProof)` → 1 つ目の引数に `rightProof` を埋める

### 例 2: 帰納法（`induction` = 構造的再帰関数）

「任意の自然数 `value` に対して `value + 0 === value`」という証明も、実は **`value` に対する普通の再帰関数**です。

```scala
import Prelude.*
import Nat.*

// 通常の再帰関数として直接書いた版（タクティク不使用）
def addZeroRightAsFunction(value: Nat): value + 0 === value = {
  value match returning (n: Nat) => n + 0 === n {
    case Nat.Zero => Eq.Refl[Nat, 0]
    case Nat.Succ(pred) =>
      congrArg[Nat, Nat](
        (k: Nat) => Nat.Succ(k),
        pred + 0,
        pred,
        addZeroRightAsFunction(pred)
      )
  }
}

// 同じ再帰関数を by { ... } タクティクで書いた版
theorem addZeroRightWithTactics(value: Nat): value + 0 === value = by {
  induction(value) {
    case Zero => { refl }
    case Succ(pred, ih) => {
      rewrite(ih)
      refl
    }
  }
}
```

直接 `def` で書くと、依存パターンマッチの戻り値型注釈（`returning (n: Nat) => n + 0 === n`）や `congrArg` による等式変換を毎回手で書く必要があり煩雑です。`by { induction(value) { ... } }` は、まさにその再帰関数と `match` と等式変換コードを裏側で自動組み立てしてくれます。

なお、タクティクが生成した関数本体は**無条件に信用されず**、最後に信頼カーネル（`samurai.kernel`）が通常の関数とまったく同じ型検査・停止性検査・網羅性検査を最初からやり直します。

---

## 2. タクティクと通常のプログラム構文の対応表

各タクティクが「裏側でどんなコードを生成しているか」を知っておくと、迷わずに使い分けられます。

| タクティク | 通常のプログラムでの対応物 | 何をしているか |
|---|---|---|
| `intro(x)` / `intros(x, y)` | `(x, y) => ...` | ラムダ式（関数引数）を受け取る |
| `exact(expr)` | `return expr` | その式をそのまま関数の戻り値として返す |
| `apply(fn)` | `fn(?, ?)` | 関数 `fn` を呼び出し、未決定の引数を残りの作業（サブゴール）にする |
| `have(v: T) { ... }` | `val v: T = ...` | 関数内にローカル変数を 1 つ導入する |
| `cases(x) { ... }` | `x match { ... }` | 代数的データ型（`enum` / `Bool`）でパターンマッチ分岐する |
| `induction(x) { ... }` | 再帰 `def` + `match` | `x` で `match` し、再帰フィールドに対する自己呼び出し結果を `ih` として受け取る |
| `split` | `And.Intro(?, ?)` | 2 要素タプル（論理積）を組み立てる |
| `left` / `right` | `Or.Inl(?)` / `Or.Inr(?)` | `Either.Left` / `Either.Right` に相当するタグを選んで返す |
| `exists(w)` | `Exists.Intro(w, ?)` | 値 `w` とその性質の証拠のペアを作る |
| `refl` | `Eq.Refl` | 左右を計算（正規化）して同じ値なら「等しい証拠」を返す |
| `rewrite(eq)` | 等式による安全な型キャスト | `a === b` の証拠を使って、型の中の `a` を `b` に書き換える |
| `discriminate(h)` | 到達不能分岐の消去（`Nothing`） | `0 === Succ(n)` や `true === false` のような矛盾から「この分岐は実行されない」ことを示す |
| `injection(h, eq)` | コンストラクタ分解 | `Succ(a) === Succ(b)` から中身の等式 `a === b` を取り出す |
| `simp` / `arith` / `omega` / `cc` / `tauto` / `auto` | ボイラープレートの自動生成 | 定義展開・半環・線形不等式・合同閉包・命題論理の関数本体を自動合成する（カーネルが事後検証） |
| `t1 <;> t2` / `rewrite(...) in h` / `obtain(x, h) = e` | 証明スクリプトのコンビネータ | 全サブゴールへの一括適用、仮定 `h` の直接書き換え、タプル・存在型の 1 行分解を行う |

---

## 3. 証明は本番のプログラムにどう効いてくるのか

証明は「数式のパズル」ではなく、通常のプログラム開発における 4 つの具体的な課題を解決するために使います。

### 3.1 ユニットテストでは網羅できない仕様を全入力で保証する

たとえば挿入ソート `insertionSort(items: List[Nat])` をテストする場合、通常のテストコードでは `[3, 1, 2]` や `[]` といった有限個のサンプルしか確認できません。

`stdlib/Sorting.samurai` では、以下の 2 つを**すべてのリスト `items`** に対して証明しています。

- `insertionSortIsSorted(items)`: 出力が昇順に並んでいる（`Sorted(insertionSort(items))`）
- `countInsertionSort(target, items)`: 任意の要素 `target` の出現回数が入力と一致する（要素が消えたり増えたりしない）

### 3.2 実務アルゴリズムの停止性チェックを通す（`termination_by`）

構造的再帰だけでは書けないアルゴリズム（クイックソート、ユークリッドの互除法 `gcd`、除算 `divNat` 等）を全関数として書くとき、コンパイラは「再帰呼び出しごとに測度が真に小さくなっていること」の証拠を求めます。

たとえば `stdlib/WellFounded.samurai` の `quickSort` では、

- 「`filter(pred, rest)` の長さは `rest` の長さ以下である」という定理 `lengthFilterLe`（タクティクで証明）

を用意しておくことで、`quickSort` 本体に `fuel: Nat` を一切書かずに停止性をコンパイラへ証明できます。つまり**タクティクで書いた補題が、そのまま普通の関数定義の型検査を通す部品になる**という関係にあります。

### 3.3 `Option` や実行時例外を型で排除する

`stdlib/Vec.samurai` の `vecHead` は、長さが `Nat.Succ(n)`（1 以上）であることを型に持つため、空ベクタ `Vec.Nil` の分岐が到達不能であることがコンパイル時に証明されます。呼び出し側で `Option` を剥がしたり、実行時例外を想定したりする必要がなくなります。

### 3.4 実行時オーバーヘッド 0 の本番コード抽出（`Subset` と `Prop` 消去）

`stdlib/Sorting.samurai` の `sortVerified` は、結果リストと「整列済みかつ元の要素の並び替えであることの証明」を `Subset` に入れて返します。

```scala
// Proof Samurai 側（仕様の証明を型に含める）
def sortVerified(items: List[Nat]):
  Subset[List[Nat], (output: List[Nat]) => IsSortedPermutation(items, output)]
```

しかし Scala 3 / TypeScript / JavaScript / Haskell / OCaml へ抽出すると、`Prop` に属する証明項と定理は**すべて 0 バイトに消去**され、実行時コードには純粋なアルゴリズムだけが残ります。

```scala
// 抽出後の Scala 3 コード（証明フィールドは完全に消去される）
enum Subset[Domain] {
  case Mk(value: Domain)
}

def sortVerified(items: List[Nat]): Subset[List[Nat]] = {
  Subset.Mk[List[Nat]](insertionSort(items))
}
```

つまり、Proof Samurai における証明は**「コンパイル時に仕様を完全に検証し、出荷バイナリには 1 バイトも残さないための仕組み」**です。

---

## 4. すべての関数に証明を書く必要はない

実務的な開発では、関数の役割に応じて 3 段階の書き方を使い分けられます。

| 書き方 | 向いているコード | 停止性保証 | 定理からの参照 | 抽出 |
|---|---|---|---|---|
| 通常の `def`（構造的再帰 / `mutual`） | データ構造操作・ビジネスロジックの中核 | あり（自動検査） | 可能 | 通常の関数 |
| `def ... termination_by { ... }` | `divNat`・`gcd`・`quickSort` 等のアルゴリズム | あり（`Acc` で検証・抽出時消去） | 可能 | 通常の関数（`Acc` 消去） |
| `partial def` | 停止性が未知・無界な処理、アプリ境界の処理 | なし（型・網羅性のみ検査） | 不可（`K031` で隔離） | 通常の関数（マニフェストに明記） |

まずはコアとなるアルゴリズムやデータ構造だけを通常の `def`（または `termination_by`）で書いて必要な性質を証明し、周辺の入出力や無界ループは `partial def` や抽出先の Scala 3 / TypeScript 側に置くのが現実的な設計です。
