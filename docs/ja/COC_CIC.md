# CoC / CIC 完全ガイド：カリー＝ハワード同型から信頼カーネルまで

定理証明支援系（Coq / Rocq、Lean、Agda、Proof Samurai など）は、外から見ると「不思議な推論エンジンが数学を解いているブラックボックス」に見えがちです。しかし、その土台にある **カリー＝ハワード同型**・**CoC（Calculus of Constructions：構成の計算）**・**CIC（Calculus of Inductive Constructions：帰納的構成の計算）** を順番にたどると、**魔法は一切なく、極めて小さな静的型検査器そのもの**であることがすっきりと腑に落ちます。

この章は、型理論の予備知識がないプログラマでも最初から最後まで独力で読み切り、**「なぜ型検査だけで数学の証明を保証できるのか」「なぜ帰納型・宇宙階層・厳密正性・停止性検査が必要なのか」「タクティクの裏で実際に何が起きているのか」**を完全に理解できるよう設計しています。登場するコードはすべて Proof Samurai の実コード（およびカーネル実装 `src/main/scala/samurai/kernel/`）と 1 対 1 で対応しています。

---

## 第 0 部：全体像 — 定理証明器はなぜ「ブラックボックス」ではないのか

定理証明器の設計は **de Bruijn 基準（de Bruijn criterion）** と呼ばれるたった 1 つの原則で貫かれています。

```text
  [人間 / タクティク / AI が書く世界（信頼しない = Untrusted）]
    Surface 構文 / タクティク (omega, cc, tauto, simp, auto) / エラボレータ
                          |
                          |  探索・自動化・展開の結果として
                          |  「具体的な 1 本の証明項 (Core Term)」を生成
                          v
  [信頼カーネル（Trusted Computing Base = samurai.kernel）]
    Term (たった 12 種類の AST) + TypeChecker + NbE + Positivity + Termination
                          |
                          |  「この項 t は本当に型 T を持つか？」だけを厳密検証
                          v
               OK (KernelEnv に登録) / NG (エラーで拒否)
```

- **タクティク（`omega`、`simp`、`induction`、`auto`）や AI エージェントは一切信頼しません。** これらは「証明項（ただの純粋関数プログラム）」を組み立てるための補助ツールにすぎません。
- **正しさを保証するのは小規模なカーネルだけ。** たとえタクティクやエラボレータにバグがあっても、生成された項がカーネルの型検査を通らなければ定理として登録されません。

つまり定理証明器の正体を完全に理解するとは、次の 4 段階を順に理解することに他なりません。

1. **カリー＝ハワード同型**：論理の命題＝型、証明＝プログラムという土台
2. **CoC（構成の計算）**：通常関数・ジェネリクス・型コンストラクタ・依存型を 1 つの `Pi` に統合する仕組み
3. **CIC（帰納的構成の計算）**：帰納型・依存パターンマッチ（`motive`）・等式 `Eq`・構造的再帰（`Fix`）
4. **変換規則（NbE）と 4 つの健全性ガード**：型の中の計算と、パラドックスを防ぐ 4 つの制約

順番にゼロから見ていきましょう。

---

## 第 1 部：カリー＝ハワード同型 — 命題は型、証明はプログラム

普段のプログラミングでは、「型 `A` はデータの形（`Int` や `String`）」であり、「値 `x : A` はそのデータ」だと考えます。ここで発想を少しだけ広げてみてください。

> **命題 `P` を 1 つの「型」だとみなしたとき、`P` が真（証明可能）であるとは、型 `P` を持つ停止する値 `pf : P` を実際に 1 つ作れることである。**

この対応を **カリー＝ハワード同型（Curry-Howard isomorphism）** と呼びます。単なる比喩ではなく、論理の推論規則とプログラミング言語の型規則が**完全に 1 対 1 で一致**します。

### 1.1 含意 `P => Q` は「関数」

「もし `P` が成り立つなら `Q` が成り立つ（`P => Q`）」という命題を証明するとはどういうことでしょうか。それは、**「`P` の証明を受け取ったら、それを加工して `Q` の証明を返す関数」**を書くことそのものです。

実際、次の 4 つの論理の法則は、タクティクを 1 つも使わず**普通の関数としてそのまま証明**できます。

```scala
import Prelude.*

// 1. 反射律: P => P  は「恒等関数」そのもの
def propId[P: Prop](p: P): P = { p }

// 2. 三段論法 (モーダスポネンス): P と P => Q から Q を得る = 「関数適用」そのもの
def modusPonensTerm[P: Prop, Q: Prop](p: P, f: P => Q): Q = { f(p) }

// 3. 含意の推移律: (P => Q) と (Q => R) から (P => R) = 「関数合成」そのもの
def implTrans[P: Prop, Q: Prop, R: Prop](f: P => Q, g: Q => R): P => R = {
  (p: P) => g(f(p))
}

// 4. 弱化 (K コンビネータ): P ならば (Q ならば P) = 「第 2 引数を捨てる定数関数」
def weaken[P: Prop, Q: Prop](p: P): Q => P = {
  (_: Q) => p
}
```

ここで重要な感覚がつかめます。
- 論理の **仮定の導入（`P` を仮定して `Q` を示す）** ＝ **ラムダ抽象 `(p: P) => ...`**
- 論理の **モーダスポネンス（`P => Q` と `P` から `Q` を得る）** ＝ **関数適用 `f(p)`**

### 1.2 論理積 `P /\ Q` は「ペア（直積型）」

「`P` かつ `Q`（`P /\ Q`）」を証明するには、`P` の証明と `Q` の証明の**両方**を揃えて渡す必要があります。これはプログラミングにおける **ペア型（2 要素のタプル）** と完全に同じです。

```scala
// stdlib/Prelude.samurai における実際の定義
enum And[Left: Prop, Right: Prop]: Prop {
  case Intro(leftProof: Left, rightProof: Right)
}

// 「P かつ Q ならば Q かつ P」の証明 = ペアの左右を入れ替える関数！
def andCommTerm[P: Prop, Q: Prop](h: P /\ Q): Q /\ P = {
  h match {
    case And.Intro(hp, hq) => And.Intro[Q, P](hq, hp)
  }
}
```

- `P /\ Q` を**作る（導入規則）** ＝ コンストラクタ `And.Intro(hp, hq)` を呼ぶ
- `P /\ Q` を**使う（除去規則）** ＝ `match` で中身 `hp`, `hq` を取り出す

### 1.3 論理和 `P \/ Q` は「タグ付きユニオン（直和型 / `Either`）」

「`P` または `Q`（`P \/ Q`）」を証明するには、「左の `P` の証明」か「右の `Q` の証明」の**どちらか一方**と、どちらを選んだかのタグを渡します。逆に `P \/ Q` の仮定を使って何かを示すときは、**左だった場合と右だった場合の両方**を場合分けで処理しなければなりません。これは Scala の `Either`（タグ付きユニオン）とまったく同じです。

```scala
// stdlib/Prelude.samurai における実際の定義
enum Or[Left: Prop, Right: Prop]: Prop {
  case Inl(leftProof: Left)
  case Inr(rightProof: Right)
}

// 「P または Q ならば Q または P」の証明 = Inl と Inr を入れ替えるパターンマッチ！
def orCommTerm[P: Prop, Q: Prop](h: P \/ Q): Q \/ P = {
  h match {
    case Or.Inl(hp) => Or.Inr[Q, P](hp)
    case Or.Inr(hq) => Or.Inl[Q, P](hq)
  }
}
```

### 1.4 真 `True` は「Unit 型」、偽 `False` は「空型（コンストラクタ 0 個）」

ここがカリー＝ハワード同型の中で最も美しいポイントです。

```scala
// stdlib/Prelude.samurai における実際の定義
enum True: Prop {
  case Intro      // 引数なしのコンストラクタが 1 つだけ → 誰でもいつでも作れる（常に真）
}

enum False: Prop {
  // コンストラクタが 0 個！ → どう頑張っても値を 1 つも作れない（決して証明できない）
}
```

コンストラクタが 0 個の型 `False` に対して `match` を書くとどうなるでしょうか。分岐は **0 個で網羅的（exhaustive）** になります。

```scala
// 爆発律（Ex Falso Quodlibet）: 「矛盾 False から任意の命題 P が導ける」
def exFalsoTerm[P: Prop](absurd: False): P = {
  absurd match {}   // False にはコンストラクタが 0 個なので、0 分岐で完全網羅！
}
```

「矛盾から何でも導ける」という論理学の有名な規則は、型理論では単に **「あり得ないケースが 0 個の `match` はどんな返り値型にも適合する」** という自然な事実に還元されます。

### 1.5 否定 `~P` は「`P => False`（矛盾へ導く関数）」

否定 `~P` に特別な組み込み機能は不要です。「`P` は偽である」とは、**「もし誰かが `P` の証明を持ってきたら、そこから必ず矛盾 `False` を作ってみせる関数」**として定義できます。

```scala
// stdlib/Prelude.samurai
def Not(P: Prop): Prop = { P => False }

// 対偶: (P => Q) ならば (~Q => ~P) = ただの関数合成！
def contrapositiveTerm[P: Prop, Q: Prop](f: P => Q): (~Q) => (~P) = {
  (notQ: Q => False) => (p: P) => notQ(f(p))
}

// 二重否定の導入: P => ~~P = 値を関数に渡すだけ！
def doubleNegIntroTerm[P: Prop](p: P): ~(~P) = {
  (notP: P => False) => notP(p)
}
```

### 1.6 構成的論理（直観主義論理）と古典論理の違い

ここで初心者の方がよく抱く疑問に答えておきます。上の `P => ~~P` は 1 行で証明できましたが、逆の **二重否定除去 `~~P => P`** や **排中律 `P \/ ~P`** は、追加の公理なしでは証明できません。なぜでしょうか。

型として読んでみると理由は一目瞭然です。

- `P \/ ~P` の証明とは、任意の命題 `P` に対して「`Or.Inl(p)`（`P` の具体的証明）」か「`Or.Inr(notP)`（`P` の反証）」の**どちらかを実際に計算して返す関数**でなければなりません。
- しかし任意の命題（たとえば「チューリングマシン `M` が停止するかどうか」）に対して常に正しいタグを返す計算可能な関数は存在しません（停止性問題）。
- 同様に `~~P`（「`P => False` は矛盾する」）から、具体的な `P` の証拠（プログラムの値）を取り出す一般的な方法はありません。

このように「証拠（プログラム）を具体的に構成できたものだけを真とする論理」を **構成的論理（直観主義論理）** と呼びます。そのおかげで、**証明から実行可能なプログラムを抽出できる**という強力な性質が生まれます（もちろん `Nat` の大小比較や等価性など決定可能な命題については `n === m \/ n !== m` を公理 0 で証明できます）。

### 1.7 「対応」ではなく「同型」である理由：証明の簡約 ＝ プログラムの実行

カリー＝ハワードが単なる「対応」ではなく**同型（isomorphism）**と呼ばれるのは、**命題⇔型・証明⇔プログラム**だけでなく、**証明の整理（迂回の除去 / カット除去）⇔ プログラムの実行（`β` 簡約）**まで一致するからです。

たとえば、ペアを作ってすぐ左を取り出す迂回証明：

```scala
(And.Intro[P, Q](hp, hq)) match {
  case And.Intro(x, _) => x
}
```

これは計算（`ι` 簡約）すると直接 `hp` になります。同様に、補題（関数）を定義してすぐ適用する証明 `((p: P) => body)(hp)` は、`β` 簡約によって `body[p := hp]` へ正規化されます。**プログラムを実行すること自体が、証明から無駄な回り道を取り除く操作そのもの**なのです。

### 第 1 部の対応まとめ表

| 論理の概念 | プログラム / 型の概念 | 導入（作る） | 除去（使う） |
|---|---|---|---|
| 命題 `P` | 型 `P : Prop` | 型定義 | 型検査 |
| 証明 `pf` | 値 `pf : P` | 式の構成 | 式の評価 |
| 含意 `P => Q` | 関数型 `P => Q` | ラムダ `(p: P) => ...` | 関数適用 `f(p)` |
| 論理積 `P /\ Q` | ペア型 `And[P, Q]` | `And.Intro(hp, hq)` | `match` で分解 |
| 論理和 `P \/ Q` | タグ付きユニオン `Or[P, Q]` | `Or.Inl` / `Or.Inr` | `match` で全分岐処理 |
| 真 `True` | Unit 型 `True` | `True.Intro` | （情報なし） |
| 偽 `False` | 空型 `False` | （作れない） | 0 分岐 `match {}` |
| 否定 `~P` | 関数型 `P => False` | `(p: P) => ... : False` | `notP(p) : False` |

---

## 第 2 部：ラムダキューブから CoC へ — たった 1 つの `Pi` で 4 つの世界を統一する

第 1 部で扱ったのは **命題論理**（「`P` ならば `Q`」のように命題の中身には踏み込まない論理）だけでした。しかし実際のプログラミングや数学では、次のような **述語論理**（「すべての自然数 `n` について `n + 0 === n`」など、具体的な値に関する主張）を扱いたくなります。

これを型システムに取り込む歴史を整理したのが、ヘンク・バレンドレフトの **ラムダキューブ（Lambda Cube）** です。

### 2.1 ラムダキューブの 4 つの軸

プログラミング言語における「何かを受け取って何かを返す」仕組みは、入力と出力が「値（項）」か「型」かによって、全部で **4 通り** しかありません。

| 軸 | 何から何へ？ | プログラミングでの具体例 | 代表的な体系・言語 |
|---|---|---|---|
| 1 | **値 → 値** | `(n: Nat) => n + 1`（普通の関数） | 単純型付きラムダ計算 (`λ→`) / C |
| 2 | **型 → 値** | `[A: Type](x: A) => x`（ジェネリクス / 多相関数） | System F (`λ2`) / ML, Java, Rust |
| 3 | **型 → 型** | `List : Type => Type`（型コンストラクタ） | System `F_ω` (`λω`) / Haskell, Scala |
| 4 | **値 → 型** | `Vec[A](n)` や `n + 0 === n`（**依存型**） | `λP` (LF) / 依存型言語 |

これら 3 本の拡張軸（軸 2・軸 3・軸 4）を立方体の 3 辺として並べたものがラムダキューブです。

```text
               λω (型→型) --------------- λC = CoC (全 4 軸を統合!)
              /|                          /|
             / |                         / |
            /  |                        /  |
          λ2 (型→値) --------------- λP2   |
          |    |                      |    |
          |   λ_ω (型→型のみ) --------|--- λPω
          |   /                       |   /
          |  /                        |  /
          | /                         | /
          λ→ (値→値のみ) ------------ λP (値→型: 依存型)
```

立方体の一番奥・一番上の頂点 **`λC`** こそが、ティエリー・コカンとジェラール・ユエ（1988）が考案した **CoC（Calculus of Constructions：構成の計算）** です。

### 2.2 依存型とは何か（値によって型が変わる）

軸 4（値 → 型）は馴染みがない人も多いので、身近な例で考えてみます。

普通の関数 `Nat => List[Nat]` は、引数として `3` を渡しても `100` を渡しても、返り値の型はつねに同じ `List[Nat]` です。
これに対して **依存関数（Dependent Function）** では、**「渡した値 `n` そのものが返り値の型の中に現れる」**ことができます。

- 長さ付きベクタ：`zeros(n: Nat): Vec[Nat](n)`
  - `zeros(3)` の型は `Vec[Nat](3)`
  - `zeros(5)` の型は `Vec[Nat](5)`
- 全称命題（述語論理）：`addZeroRight(n: Nat): n + 0 === n`
  - `addZeroRight(3)` の型は `3 + 0 === 3`
  - `addZeroRight(5)` の型は `5 + 0 === 5`

この「引数 `x: A` の値によって返り値の型 `B(x)` が変わる関数型」を **依存積型（Dependent Product Type）** と呼び、記号では `Π(x: A). B(x)`、Proof Samurai の構文では **`forall (x: A) => B(x)`** と書きます。

### 2.3 CoC の大統一：4 種類の関数がすべて同じ `Pi` になる

CoC が驚くほど簡潔なのは、値と型の構文上の区別をなくし、ラムダキューブの 4 つの軸を**すべてたった 1 つの `Term.Pi(name, domain, codomain)` だけで表現する**点にあります。

| 書きたいもの | 実際の `Pi` 表現 | 特徴 |
|---|---|---|
| 普通の関数 `Nat => Bool` | `Pi("_", Nat, Bool)` | `codomain` に引数が現れない |
| 論理の含意 `P => Q` | `Pi("_", P, Q)` | `domain`, `codomain` が `Prop` |
| 多相関数（ジェネリクス）`[A](x: A) => x` | `Pi("A", Type0, Pi("x", A, A))` | `domain` が `Type0` |
| 型コンストラクタ `List` | `Pi("_", Type0, Type0)` | `Type0` を受けて `Type0` を返す |
| 述語（値から命題へ）`IsEven` | `Pi("_", Nat, Prop)` | `Nat` を受けて `Prop` を返す |
| 全称量化 `∀n:Nat. n + 0 = n` | `Pi("n", Nat, Eq(add(n, 0), n))` | `codomain` の中で値 `n` を使う |

「普通の関数」「含意」「ジェネリクス」「型コンストラクタ」「述語」「全称量化 `∀`」という 6 つもの概念が、カーネル内部では**完全に同一の `Term.Pi`** として統一されています。

### 2.4 対になる存在型：`Exists` と `Subset`（依存ペア `Σ`）

全称量化 `∀` が「依存関数型 `Π`」に対応するのに対し、存在量化 `∃x:A. P(x)` は **依存ペア型（Dependent Pair / Sigma Type `Σ`）** に対応します。依存ペアとは、「第 1 要素の値 `w: A`」と「その `w` についての証明 `proof: P(w)`」の組です。

Proof Samurai では用途に応じて 2 種類を使い分けます（どちらも `stdlib/Prelude.samurai` に定義）。

```scala
// 1. 論理用の存在命題 (Prop): 証明の中だけで使い、コード抽出時は 0 バイトに消去される
enum Exists[Domain: Type, Predicate: Domain => Prop]: Prop {
  case Intro(witness: Domain, proof: Predicate(witness))
}

// 2. 計算用の仕様付き値 (Type): 値本体は実行時に残り、proof フィールドだけ消去される！
enum Subset[Domain: Type, Predicate: Domain => Prop]: Type {
  case Mk(value: Domain, proof: Predicate(value))
}
```

例えば `stdlib/Sorting.samurai` の `sortVerified` は `Subset` を返すことで、「整列済みリストという実行時データ」と「本当に整列されていて要素数も保存されているという証明」を 1 つの返り値に束ねています。抽出時には `proof` が消えて純粋なソート済みリストだけが残ります。

### 2.5 純粋型システム（PTS）と宇宙の規則 `piSort`

`Pi(x: A, B)` 自身の型（どの宇宙に属するか）は、`A : s1` と `B : s2` の 2 つのソート（`Prop` または `Type(i)`）から一意に決まります。Proof Samurai の [Term.scala](https://github.com/kmizu/proof-samurai/blob/main/src/main/scala/samurai/kernel/Term.scala) では、この規則は文字通り次の **3 行** だけです。

```scala
def piSort(codSort: Sort): Sort = (this, codSort) match {
  case (_, Sort.Prop)              => Sort.Prop                 // Prop の非可述性
  case (Sort.Prop, Sort.Type(j))   => Sort.Type(j)              // 証明を受け取りデータを返す関数
  case (Sort.Type(i), Sort.Type(j))=> Sort.Type(math.max(i, j)) // 可述的な Type 階層
}
```

- 返り値型 `B` が `Prop` なら、入力 `A` が `Nat` でも `Type0` でも `Prop` でも、全体の型 `forall (x: A) => B` はつねに **`Prop`** になります（これを **`Prop` の非可述性（impredicativity）** と呼びます）。
- 返り値型 `B` が `Type(j)` なら、全体の型は `Type(max(i, j))` になります。

---

## 第 3 部：なぜ CoC だけでは足りないのか → CIC（帰納型・`motive`・`Eq`・帰納法）

ここまでで CoC の仕組みが見えました。ところが、**純粋な CoC だけでは実用的な数学やプログラミングの証明が書けません**。

### 3.1 純粋な CoC の限界（チャーチエンコーディングの壁）

純粋な CoC でも、自然数をチャーチ数 `ChurchNat = forall (X: Type) => (X => X) => X => X` として定義し、加算や乗算を書くことはできます。しかし次の 2 つの致命的な壁にぶつかります。

1. **「`0 !== 1`」が証明できない**: ペアノの公理の中で最も基本的な「`Zero` と `Succ(Zero)` は等しくない」という事実を、純粋な CoC では追加の公理なしに証明できないことが理論的に知られています。
2. **自然数の数学的帰納法を導出できない**: `forall (n: ChurchNat) => P(n)` を証明するための帰納法原理がチャーチ数の型から出てきません。

この壁を突破するために、CoC に **帰納型（Inductive Types）**・**依存パターンマッチ（`Match`）**・**構造的再帰（`Fix`）** を中核要素として組み込んだのが **CIC（Calculus of Inductive Constructions）** です。

### 3.2 パラメータ（Parameter）と添字（Index）の違い

CIC の帰納型定義 `enum` には 2 種類の型引数があります。ここを区別すると `List`・`Vec`・`Eq`・`Acc` がすべて同じ原理に見えてきます。

- **パラメータ（`[...]`）**: すべてのコンストラクタで**共通して固定**される引数。
- **添字 / インデックス（`(...)`）**: **コンストラクタごとに異なる具体的な値**をとれる引数（データ型の族＝Inductive Family を作る）。

```scala
// パラメータのみ: List[Element] は Nil でも Cons でも同じ Element
enum List[Element: Type]: Type {
  case Nil
  case Cons(head: Element, tail: List[Element])
}

// パラメータ Element + 添字 size: Nat（Nil は 0、Cons は Succ(tailSize)！）
enum Vec[Element: Type](size: Nat): Type {
  case Nil: Vec[Element](Nat.Zero)
  case Cons(tailSize: Nat, head: Element, tail: Vec[Element](tailSize)): Vec[Element](Nat.Succ(tailSize))
}

// パラメータ A, left + 添字 right: A（Refl は right = left のときだけ作れる！）
enum Eq[A: Type, left: A](right: A): Prop {
  case Refl: Eq[A, left](left)
}
```

### 3.3 依存パターンマッチと `motive` を完全に理解する

初心者が CIC で最初につまずきやすいのが `Match` の **`motive`（動機関数）** です。これを具体例で完全に解き明かしましょう。

普通のプログラミング言語の `match` では、すべての `case` 分岐が同じ 1 つの型 `R` を返さなければなりません。
CIC の `Match` は **「今マッチしている値 `x` に応じて、各分岐が返すべき型を変える関数 `motive`」** を受け取ります。

- 普通の `match`（非依存）: `motive = (_: Nat) => Bool`（どのケースでも常に `Bool` を返す）
- 依存 `match`: `motive = (k: Nat) => k + 0 === k`
  - `case Nat.Zero` 分岐で要求される型: `motive(Nat.Zero)` = `0 + 0 === 0`
  - `case Nat.Succ(pred)` 分岐で要求される型: `motive(Nat.Succ(pred))` = `Nat.Succ(pred) + 0 === Nat.Succ(pred)`

#### 実演：公理 0 で「`0 !== 1`（`discriminate`）」をゼロから証明する！

なぜ CIC では公理なしで `0 !== 1` が証明できるのでしょうか？ 答えは **「`Nat` を `Prop` に写す関数（大きな除去 / Large Elimination）」＋「`Eq` の `Match`」** の組み合わせです。

```scala
import Prelude.*
import Nat.*

// ステップ 1: 0 なら True、Succ(_) なら False を返す述語関数を定義する
def isZeroProp(n: Nat): Prop = {
  n match {
    case Nat.Zero    => True
    case Nat.Succ(_) => False
  }
}

// ステップ 2: h : 0 === 1 が与えられたら、returning (...) で motive を明示し、
//             isZeroProp(0) (= True) の証拠 True.Intro を isZeroProp(1) (= False) へ運ぶ！
def zeroNeqOneFromScratch(h: 0 === 1): False = {
  // motive は (y: Nat, _: Eq[Nat, 0](y)) => isZeroProp(y)
  //   - Refl 分岐で要求される型: isZeroProp(0) = True → True.Intro で型が合う！
  //   - Match 全体の型:          isZeroProp(1) = False！
  h match returning ((y: Nat, _: Eq[Nat, 0](y)) => isZeroProp(y)) {
    case Eq.Refl => True.Intro
  }
}
```

これを見た瞬間、ブラックボックスの蓋が一気に開きます。
- `discriminate` タクティクは不思議な魔術ではなく、裏側でまさにこの `isZeroProp` のような識別関数と `Eq` の `Match` を自動生成しているだけです。
- 同様に `Vec[A](Nat.Succ(n))` に対する `vecHead` で `Vec.Nil` が到達不能になるのも、添字 `Nat.Zero` と `Nat.Succ(n)` が等しくなれないことを同じ仕組みで導出しているからです。

### 3.4 等式 `Eq`（Paulin-Mohring 同一性型）と `rewrite` の正体

`stdlib/Prelude.samurai` にある `Eq` の定義を再確認します。

```scala
enum Eq[A: Type, left: A](right: A): Prop {
  case Refl: Eq[A, left](left)
}
```

`Eq` のコンストラクタは `Refl` の 1 つだけです。このたった 1 行の定義から、等号に関するすべての性質（対称律・推移律・合同性・書き換え `rewrite`）が **公理 0 で** 導かれます。

```scala
// 書き換えの本体（ライプニッツ置換 / Eq 除去規則）
def eqSubst[A: Type](P: A => Prop, x: A, y: A, eqProof: Eq[A, x](y), px: P(x)): P(y) = {
  eqProof match returning ((z: A, _: Eq[A, x](z)) => P(z)) {
    case Eq.Refl => px   // Refl のときは z = x なので P(x) がそのまま P(z) に一致！
  }
}

// 対称律 (x === y => y === x): P(z) を (z === x) として px = Refl を運ぶだけ！
def eqSymTerm[A: Type](x: A, y: A, h: x === y): y === x = {
  eqSubst[A]((z: A) => z === x, x, y, h, Eq.Refl[A, x])
}

// 推移律 (x === y => y === z => x === z): P(w) を (x === w) として h1 を h2 で運ぶ！
def eqTransTerm[A: Type](x: A, y: A, z: A, h1: x === y, h2: y === z): x === z = {
  eqSubst[A]((w: A) => x === w, y, z, h2, h1)
}

// 合同性 (x === y => f(x) === f(y)): P(w) を (f(x) === f(w)) として Refl を運ぶ！
def eqCongrTerm[A: Type, B: Type](f: A => B, x: A, y: A, h: x === y): f(x) === f(y) = {
  eqSubst[A]((w: A) => f(x) === f(w), x, y, h, Eq.Refl[B, f(x)])
}
```

タクティクの `symmetry`、`trans`、`congr`、`rewrite` はすべて、この `eqSubst`（つまり `Eq` に対する `Match`）を組み立てているにすぎません。

### 3.5 数学的帰納法 ＝ 構造的再帰関数 `Fix` ＋ 依存 `Match`

学校で習う数学的帰納法（「`n = 0` のとき成り立ち、`n = k` のとき成り立つと仮定して `n = k + 1` を示す」）も、CIC では特別な論理公理ではなく **「`n` に対して自分自身を `pred` で再帰呼び出しする関数」** と完全に同一です。

```scala
// タクティクを使わずに書いた「n + 0 === n」の帰納法証明
def addZeroRightDirect(n: Nat): n + 0 === n = {
  n match returning ((k: Nat) => k + 0 === k) {
    case Nat.Zero =>
      // 0 + 0 は定義上 0 に計算されるので Eq.Refl だけでよい
      Eq.Refl[Nat, Nat.Zero]
    case Nat.Succ(pred) => {
      // 帰納法の仮定 (IH) とは、より小さい値 pred に対する再帰呼び出しの結果そのもの！
      val ih: pred + 0 === pred = addZeroRightDirect(pred)
      // ih を使って Succ(pred + 0) === Succ(pred) を作る
      eqCongrTerm[Nat, Nat]((k: Nat) => Nat.Succ(k), pred + 0, pred, ih)
    }
  }
}
```

さらに Proof Samurai の CIC は、コンストラクタのフィールドに関数を含む **高階帰納型**（`stdlib/WellFounded.samurai` の `Acc.Intro` や、`stdlib/IO.samurai` の `IO.ReadNat(cont: Nat => IO[Result])`）の構造的再帰・帰納法もそのまま検証できます。

---

## 第 4 部：型の中の計算 — 定義的等価 vs 命題的等価、そして NbE

定理証明を始めた人が**必ず最初に疑問に思う現象**があります。

- `theorem leftZero(n: Nat): 0 + n === n = by { refl }` は **`refl` 一発** で通る。
- なのに `theorem rightZero(n: Nat): n + 0 === n = by { refl }` は **失敗し、`induction(n)` が必要** になる！

この違いを 100% 理解できると、証明が劇的に楽になります。鍵は **2 種類の「等しい」** の違いと **変換規則（Conversion Rule）** にあります。

### 4.1 定義的等価 (`≡`) と命題的等価 (`===`)

`stdlib/Nat.samurai` の `add` の定義を見てみましょう。

```scala
def add(left: Nat, right: Nat): Nat = {
  left match {
    case Nat.Zero       => right
    case Nat.Succ(pred) => Nat.Succ(add(pred, right))
  }
}
```

`add` は **第 1 引数 `left` でパターンマッチ** しています。

1. **`add(0, n)` の場合**: 第 1 引数が具体的なコンストラクタ `Nat.Zero` なので、カーネルの計算エンジン（NbE）が即座に `match` を 1 歩進めて **`n` へ簡約** します。よって `0 + n` と `n` は計算結果が完全に同一、すなわち **定義的等価（`0 + n ≡ n`）** です。変換規則 `[Conv]` により、`Eq.Refl[Nat, n]`（`n === n` の証明）がそのまま `0 + n === n` の証明として認められます。
2. **`add(n, 0)` の場合**: 第 1 引数が未知の変数 `n` なので、`match` はどちらの分岐に進むべきか決められず **そこで計算が止まります（stuck / neutral）**。したがって `n + 0` と `n` は定義的等価ではなく、`n` を `Zero` / `Succ(pred)` で場合分けして計算を進める **命題的等価（`===`）の証明項**（つまり `induction(n)`）が必要になります。

まとめると次の通りです。

| 種類 | 記号 | 誰が判定するか | 例 |
|---|---|---|---|
| **定義的等価**（計算上の同一性） | `A ≡ B` | カーネル（NbE）が自動で計算して判定 | `2 + 2 ≡ 4`, `0 + n ≡ n`, `((x) => x)(3) ≡ 3` |
| **命題的等価**（証明項が必要な等式） | `a === b` (`Eq`) | ユーザー / タクティクが `Eq` の値を構成 | `n + 0 === n`, `a + b === b + a`, `reverse(reverse(xs)) === xs` |

### 4.2 変換規則（Conversion Rule）

カーネルが型の中で計算を許す根拠が **変換規則 `[Conv]`** です。

```text
  Γ ⊢ t : A      A ≡ B (NbE で計算すると同じ、または累積性 A ⪯ B)
  ---------------------------------------------------------------  [Conv]
                            Γ ⊢ t : B
```

たとえば `t : Vec[Nat](2 + 2)` を `Vec[Nat](4)` が期待される場所へ渡しても、`2 + 2 ≡ 4` なので型エラーにならずそのまま通ります。

### 4.3 NbE（Normalization by Evaluation）の仕組み（`NbE.scala`）

「どうやってカーネルは `A ≡ B` を高速かつ確実に判定しているのか？」その実装が [NbE.scala](https://github.com/kmizu/proof-samurai/blob/main/src/main/scala/samurai/kernel/NbE.scala) の **NbE（評価による正規化）** です。

単純な構文木書き換え（代入を繰り返す方法）は遅くバグを生みやすいため、現代のカーネル（Lean / Agda / Proof Samurai）では 2 段階で正規化を行います。

1. **評価（`evaluate`: `Term -> Value`）**: de Bruijn の `Term` を、Scala のクロージャと環境（`EvalEnv`）を使ってセマンティック値 `Value` へ高速に評価する。変数で止まった式は `VNeutral(head, spine)` として保持する。
2. **読み戻し / 比較（`quote` / `isDefEq`）**: 2 つの `Value` を構造的に比較する（関数同士は新しい自由変数 `NVar(level)` を適用して本体を比較する `η` / 外延的比較）。

`NbE.scala` が行う簡約は次の 6 種類だけです。

| 簡約規則 | 記号 | 内容 |
|---|---|---|
| ベータ簡約 | `β` | `((x) => body)(arg)` を環境拡張 `x -> arg` で評価 |
| ゼータ簡約 | `ζ` | `Let(x, ty, v, body)` を `x -> eval(v)` で展開 |
| デルタ簡約 | `δ` | 透過的な `def` を展開（`partial def` と `axiom` は絶対に展開しない） |
| イオタ簡約 | `ι` | コンストラクタ `VCtor` に対する `Match` の該当分岐を実行 |
| 不動点展開 | `fix` | `Fix` / `MutualFix` は **減少引数が `VCtor`（具体的コンストラクタ）のときだけ** 展開 |
| 証明無関係性 | `PI` | 型付き比較において、同じ `Prop` 型 `P` に属する任意の 2 つの証明 `pf1, pf2 : P` を等しいとみなす |

`fix` を「減少引数が `VCtor` のときだけ展開する」設計のおかげで、`add(n, 0)` のように変数で止まった再帰呼び出しが無限展開されることは決してありません。

---

## 第 5 部：カーネルの全貌 — たった 12 種類の `Term` と型検査規則

Proof Samurai のカーネルが扱うコア言語の AST は [Term.scala](https://github.com/kmizu/proof-samurai/blob/main/src/main/scala/samurai/kernel/Term.scala) にすべて収まっています。複雑な表面構文（`do { ... }`、`calc { ... }`、`case class`、`if`、ネストしたパターンマッチ、`termination_by`、全タクティク）は、すべて最終的にこの **12 種類の `Term`** へコンパイルされます。

```scala
enum Term {
  // --- CoC コア（7 種類）---
  case USort(sort: Sort)                                   // Prop, Type0, Type1, ...
  case Var(idx: Int)                                       // de Bruijn インデックス変数
  case Const(name: String)                                 // 検証済み def / theorem / axiom
  case Pi(name: String, domain: Term, codomain: Term)      // 依存積型 forall (x: A) => B
  case Lam(name: String, domain: Term, body: Term)         // ラムダ抽象 (x: A) => body
  case App(fn: Term, arg: Term)                            // 関数適用 fn(arg)
  case Let(name: String, ty: Term, value: Term, body: Term)// 局所束縛 val x: T = v; body

  // --- CIC 帰納型拡張（5 種類）---
  case Ind(name: String)                                   // 帰納型名 (Nat, List, Eq, Acc, IO, ...)
  case Ctor(indName: String, ctorName: String)             // コンストラクタ (Nat.Succ, Eq.Refl, ...)
  case Match(indName: String, params: List[Term], motive: Term, scrutinee: Term, branches: List[MatchBranch])
  case Fix(name: String, recArgIdx: Int, ty: Term, body: Term)     // 構造的再帰
  case MutualFix(defs: List[MutualFixDef], selectedIndex: Int)     // 相互構造的再帰
}
```

### 5.1 de Bruijn インデックスの具体例

カーネル内部では変数名による衝突（キャプチャ）を完全に防ぐため、変数を **「何個外側の束縛を指すか」という 0 始まりの整数 `Var(idx)`** で表現します。

- `(x: Nat) => x` → `Lam("x", Nat, Var(0))`（0 個外側＝すぐ外側の `x`）
- `(x: Nat) => (y: Nat) => x` → `Lam("x", Nat, Lam("y", Nat, Var(1)))`（`y` を 1 つ飛び越えて `x` を指す）
- `(a: Nat) => (b: Nat) => a` → `Lam("a", Nat, Lam("b", Nat, Var(1)))`

名前 `x, y` と `a, b` は人間向けの表示ラベルにすぎず、構造は完全に同じです。そのためアルファ同値性（束縛変数名を変えただけの同一性）は、単純な木の一致判定 `Term.alphaEq` だけで済みます。

### 5.2 推論規則（`Γ ⊢ t : A`）の読み方

型理論の文献や解説でよく出る記法は、たった 3 つの記号さえ知っていれば誰でも読めます。

- **`Γ`（ガンマ / コンテキスト）**: 今スコープ内にあるローカル変数と仮定の一覧（例：`n : Nat, h : n === 0`）。
- **`Γ ⊢ t : A`（判断 / Judgment）**: 「コンテキスト `Γ` のもとで、項 `t` は型 `A` を持つ」という主張。
- **横線の上下**: 「横線の**上（前提）**がすべて成り立つならば、横線の**下（結論）**を認めてよい」という意味。

### 5.3 コア型検査規則一覧（`TypeChecker.scala`）

[TypeChecker.scala](https://github.com/kmizu/proof-samurai/blob/main/src/main/scala/samurai/kernel/TypeChecker.scala) が実装している核となる規則は次の通りです。

```text
  [Sort]   ----------------------           ----------------------------
             Γ ⊢ Prop : Type(0)               Γ ⊢ Type(i) : Type(i + 1)

  [Var]       (x : A) ∈ Γ
           -----------------
              Γ ⊢ x : A

  [Pi]     Γ ⊢ A : s1        Γ, x:A ⊢ B : s2
           ----------------------------------
              Γ ⊢ Π(x: A). B : piSort(s1, s2)

  [Lam]    Γ ⊢ A : s         Γ, x:A ⊢ b : B
           ----------------------------------
              Γ ⊢ (x: A) => b : Π(x: A). B

  [App]    Γ ⊢ f : Π(x: A). B      Γ ⊢ a : A
           ----------------------------------
                 Γ ⊢ f(a) : B[x := a]

  [Let]    Γ ⊢ A : s    Γ ⊢ v : A    Γ, x:A := v ⊢ b : B
           ----------------------------------------------
             Γ ⊢ (val x: A = v; b) : B[x := v]

  [Conv]   Γ ⊢ t : A        A ⪯ B  (NbE 等価または Type(i) <= Type(j))
           ------------------------------------------------------------
                                   Γ ⊢ t : B
```

さらに CIC の 2 つの規則が加わります。

- **`[Match]`**: 対象 `scrutinee : Ind(params, indices)` に対し、
  1. すべてのコンストラクタが網羅されていること（`K026`）、
  2. `Ind` が `Prop` で `motive` の返り先が `Type` の場合は Subsingleton であること（`K025`）、
  3. 各分岐本体が `motive(ctorIndices, Ctor(fields))` の型を持つこと、
  を検証し、全体に型 `motive(indices, scrutinee)` を与えます。
- **`[Fix]` / `[MutualFix]`**: 再帰関数の型 `ty` が well-typed であり、本体が自身を型 `ty` で仮定したもとで型 `ty` を持ち、かつ `Termination.scala` の構造的減少検査（`K020`）を通過することを検証します。

たったこれだけです。定理証明器のカーネルに「秘密のヒューリスティック」は 1 行もありません。

---

## 第 6 部：なぜ 4 つの健全性ガードが不可欠なのか（外すと起きるパラドックス）

CIC には通常のプログラミング言語にはない厳しいエラー（`K005`, `K006`, `K020`, `K025`, `K030`, `K031`）があります。これらは不便にするための規則ではなく、**1 つでも緩めると `False`（あり得ない矛盾）の証明項が作れてしまい、証明器全体が無意味になる**ために存在します。

### ガード 1：宇宙階層と可述性（`K005` — ジラールのパラドックスを防ぐ）

「型の型は何か？」と考えたとき、`Type : Type` と自分自身に属させてしまうと、集合論における「自分自身を含まないすべての集合の集合（ラッセルのパラドックス）」の型理論版である **ジラールのパラドックス（Girard's paradox, 1972）** が発生し、`False` の値（無限ループする証明項）が作れてしまいます。

そこで CIC では宇宙を無限階層に分けます。

```text
  Prop : Type0 : Type1 : Type2 : ...
```

- 累積性（Cumulativity）：`Type0` に属する型は `Type1` にも属するとみなせる（`Type(i) <= Type(j)` for `i <= j`）。
- `Type(k)` の帰納型の可述性：`enum Box: Type0 { case Mk(T: Type0, x: T) }` のように `Type0` の箱の中に `Type0` 自身を入れようとすると自己言及のループが起きるため、`K005` で拒否されます（`enum Box: Type1` と 1 段上げれば安全に定義できます）。

### ガード 2：厳密正性（`K006` — カリーのパラドックスを防ぐ）

帰納型 `Bad` のコンストラクタ引数の中で、`Bad` 自身が関数矢印 `=>` の**左辺（負の位置 / contravariant position）**に現れると、**再帰関数（`Fix`）を 1 回も使わずに `False` を証明できてしまいます（カリーのパラドックス）**。

実際に壊れる様子を見てみましょう。

```scala
// 危険な負の帰納型（Proof Samurai の Positivity.scala は K006 で即座に拒否）
enum Bad: Prop {
  case Mk(selfApply: Bad => False)
}

// もし Bad が許されたら、Fix なしで次の 2 関数が型検査を通ってしまう：
def unroll(b: Bad): False = {
  b match {
    case Bad.Mk(f) => f(b)     // b に自分自身 b を渡す（自己適用！）
  }
}

def paradox: False = {
  unroll(Bad.Mk(unroll))       // 停止せず、しかも型は False！論理体系が崩壊！
}
```

ここで **正の位置** と **負の位置** の違いを押さえておくと、なぜ `IO` や `Acc` が安全なのかも明確になります。

- **安全な厳密正（Strictly Positive）**: `case ReadNat(cont: Nat => IO[Result])` や `case Intro(cur, step: forall y => Rel(y, cur) => Acc(y))`。`IO` や `Acc` が矢印の**右辺**だけに現れ、左辺は外部の型 `Nat` や `Rel` だけです。
- **危険な負（Negative）**: `case Mk(f: Bad => False)` や、二重負 `case Mk(f: (Bad => False) => False)`。帰納型自身が矢印の左辺に現れるため、`Positivity.scala` が `K006` で拒否します（`def Not(P: Prop) = P => False` のような透過的別名も NbE で展開してから検査するため、迂回も不可能です）。

### ガード 3：停止性検査（`K020`）・整礎再帰 `Acc`・`partial def` 隔離（`K030`/`K031`）

一般再帰を無制限に許すと、次の 1 行ですべての命題が嘘の証明を持ってしまいます。

```scala
// 無限ループによる偽の証明（Termination.scala が K020 で拒否）
def loop(n: Nat): False = { loop(n) }
```

なぜなら、`loop(0)` は型 `False` を持つものの永遠に値を返さないからです。「値が存在する＝真」というカリー＝ハワード同型は、**すべての証明項が必ず有限ステップで停止する（強正規化性）**という前提の上で初めて成立します。

Proof Samurai では、停止性と表現力を両立させる 3 つの階層を用意しています。

1. **構造的再帰・相互構造的再帰（`Fix` / `MutualFix`）**: パターンマッチで取り出した真に小さい部分項に対して再帰する（例：`Nat.Succ(pred)` の `pred`、`List.Cons(_, tail)` の `tail`、`IO.ReadNat(k)` の `k(n)`）。
2. **整礎再帰（`termination_by` + `Acc`、`stdlib/WellFounded.samurai`）**: クイックソートやユークリッドの互除法 `gcd` のように単純な構造的減少では書けない関数は、到達可能性述語 `Acc` に対する構造的再帰へ自動変換されます。
   - `Acc[A, R](x)` は「`x` から関係 `R` で小さくしていく操作は必ず有限回で止まる」という帰納的命題（公理 0！）。
   - `Acc.Intro(x, step)` をパターンマッチして取り出した `step(y, hSmaller)` は `Acc` として**構造的に真に小さい部分項**になるため、カーネルの構造的再帰検査だけで任意の整礎再帰を検証できます。
   - しかも `Acc` は `Prop` の Subsingleton なので、コード抽出時には跡形もなく 0 バイトに消去されます。
3. **隔離された一般再帰（`partial def`）**: コラッツ数列など停止性が未解決の計算関数には `partial def` を書けますが、`Prop` を返せず（`K030`）、NbE で展開されず、全関数や定理からは一切参照できません（`K031`）。

### ガード 4：`Prop` と `Type` の分離、および Subsingleton 除去（`K025`）

なぜ `Type` とは別に `Prop` があるのでしょうか。次の 3 つを同時に満たすためです。

1. **0 バイト証明消去（Extraction）**: 本番コード（Scala 3 / TS / JS / Haskell / OCaml）へ抽出するとき、`Prop` をすべて安全に消去してオーバーヘッドゼロにする。
2. **証明無関係性（Proof Irrelevance）**: 同じ命題の 2 つの証明 `pf1, pf2 : P` を同一視し、依存型の中で証明の作り方の違いに悩まされないようにする。
3. **非可述性（Impredicativity）**: すべての命題にわたる量化 `forall (P: Prop) => ...` を `Prop` 内に収める。

もし「コンストラクタが 2 つある `Prop`（例：`Or[True, True]`）」から `Bool : Type` を取り出す `match` を許すと、何が起きるでしょうか。

```scala
// もし Or[True, True] から Bool への match が許されたら（Proof Samurai は K025 で拒否）
def leak(h: True \/ True): Bool = {
  h match {
    case Or.Inl(_) => true
    case Or.Inr(_) => false
  }
}
// 証明無関係性より Or.Inl(True.Intro) ≡ Or.Inr(True.Intro) なので、
// leak(Or.Inl(True.Intro)) ≡ leak(Or.Inr(True.Intro)) つまり true === false が導けてしまう！
```

証明無関係性と矛盾するだけでなく、抽出時に `h : True \/ True` を消去した瞬間 `leak` が `true` と `false` のどちらを返すべきか分からなくなります。

そこで CIC は、`Prop` から `Type` への除去を **Subsingleton（計算上の分岐情報を持たない `Prop`）** だけに限定します。

| `Prop` 帰納型 | コンストラクタ | `Prop -> Type` 除去 | 理由 |
|---|---|---|---|
| `False` | 0 個 | **許可** | 到達不能なので実行時に分岐しない |
| `True` | 1 個（引数なし） | **許可** | 分岐は常に 1 通りだけ |
| `Eq` | 1 個 `Refl` | **許可** | 分岐は常に `Refl` 1 通りだけ（`Vec` の型変換に不可欠） |
| `Acc` | 1 個 `Intro`（全フィールドが `Prop` または添字強制） | **許可** | 実行時データを持たず抽出時に完全消去できる |
| `Or`, `Exists` | 2 個、または `Type` の証人フィールドを持つ | **禁止 (`K025`)** | 実行時の分岐や値が証明に依存してしまう（代わりに `Either` / `Subset` を使う） |

---

## 第 7 部：タクティクの正体とエンドツーエンド追跡

ここまで来れば、タクティク（`by { ... }`）の裏側も完全に透明になります。

### 7.1 タクティクエンジンは「AST の穴埋め機」（LCF スタイル）

Proof Samurai の [Tactics.scala](https://github.com/kmizu/proof-samurai/blob/main/src/main/scala/samurai/tactic/Tactics.scala) が管理している証明状態 `ProofState` は、実質的に次の 2 つだけです。

1. `openGoals: List[ProofGoal]` — まだ埋まっていない穴（ゴール）の一覧。各ゴールは `(コンテキスト Γ, 目標の型 T)` を持つ。
2. `extractProof: Map[GoalId, Term] => Term` — 各穴を埋める項が揃ったら、それらを組み立てて元の定理全体の 1 本の `Term` を返す関数。

各タクティクはゴールを書き換えているだけに見えますが、裏側では **「穴を埋めるコア `Term` の断片（`Lam`, `App`, `Match`, `Fix`, `Ctor`）」を繋ぎ合わせている** だけです。

- `intro(x)` → 外側に `Lam("x", dom, ?subgoal)` を 1 枚かぶせる
- `split` → `And.Intro(?leftGoal, ?rightGoal)` の 2 つの穴を作る
- `rewrite(h)` → `Match("Eq", ..., h, [Refl => ?rewrittenGoal])` をかぶせる
- `induction(n)` → `Fix(..., Lam(n, Match("Nat", motive, n, [Zero => ?g0, Succ(pred) => ?g1])))` をかぶせる
- `omega` / `arith` / `cc` / `tauto` → 自動探索で証明手順を見つけたあと、**公理 0 の純粋な CIC `Term`** を組み上げて穴を埋める

### 7.2 エンドツーエンド完全追跡：`addZeroRight`

次の定理が入力されてから本番コードへ抽出されるまでの全行程を追ってみましょう。

#### ステップ 1：表面のタクティク証明

```scala
theorem addZeroRight(n: Nat): n + 0 === n = by {
  induction(n) {
    case Zero => { refl }
    case Succ(pred, ih) => {
      simp
      rewrite(ih)
      refl
    }
  }
}
```

#### ステップ 2：各タクティクで変化するゴール

1. 開始時：`n : Nat ⊢ n + 0 === n`
2. `induction(n)` 実行後、2 つのサブゴールが生成される：
   - ゴール #1（`Zero`）：`⊢ 0 + 0 === 0`
   - ゴール #2（`Succ`）：`pred : Nat, ih : pred + 0 === pred ⊢ Nat.Succ(pred) + 0 === Nat.Succ(pred)`
3. ゴール #1 で `refl`：`0 + 0` が NbE で `0` に簡約され `Eq.Refl[Nat, 0]` で閉じる。
4. ゴール #2 で `simp`：`Nat.Succ(pred) + 0` が `Nat.Succ(pred + 0)` へ簡約される（ゴールは `Nat.Succ(pred + 0) === Nat.Succ(pred)`）。
5. `rewrite(ih)`：`Eq` に対する `Match` を生成し、`pred + 0` を `pred` へ置換（ゴールは `Nat.Succ(pred) === Nat.Succ(pred)`）。
6. `refl`：`Eq.Refl[Nat, Nat.Succ(pred)]` で閉じ、開いているゴールが 0 個になる。

#### ステップ 3：カーネルへ渡される最終コア CIC 項（読みやすく表記）

```scala
Fix(
  name = "addZeroRight",
  recArgIdx = 0,
  ty = Pi(n: Nat, Eq[Nat, add(n, Nat.Zero)](n)),
  body = Lam(n: Nat,
    Match(
      indName = "Nat",
      motive = Lam(k: Nat, Eq[Nat, add(k, Nat.Zero)](k)),
      scrutinee = n,
      branches = [
        case Zero =>
          Eq.Refl[Nat, Nat.Zero],
        case Succ(pred) =>
          // ih = addZeroRight(pred) : Eq[Nat, add(pred, 0)](pred)
          Match(
            indName = "Eq",
            motive = Lam(y: Nat, Lam(_: Eq[Nat, add(pred, Nat.Zero)](y),
                       Eq[Nat, Nat.Succ(add(pred, Nat.Zero))](Nat.Succ(y)))),
            scrutinee = addZeroRight(pred),
            branches = [ case Refl => Eq.Refl[Nat, Nat.Succ(add(pred, Nat.Zero))] ]
          )
      ]
    )
  )
)
```

#### ステップ 4：信頼カーネルが検証する 4 項目

1. **型検査（`TypeChecker` + `NbE`）**: 各分岐と `Match` 全体の型が変換規則 `[Conv]` のもとで厳密に一致するか。
2. **網羅性（`K026`）**: `Nat` の `Zero` / `Succ`、`Eq` の `Refl` が漏れなく並んでいるか。
3. **停止性（`Termination` / `K020`）**: 再帰呼び出し `addZeroRight(pred)` の引数 `pred` が、`n` のパターンマッチから得られた真に小さい部分項か。
4. **公理追跡（`Env`）**: 依存先に `axiom` / `sorry` が 0 個であることを `KernelEnv` に記録。

#### ステップ 5：コード抽出（`Erasure`）

`addZeroRight` の返り値型 `Eq(...)` は `Prop` に属するため、`Erasure.scala` が完全に消去します。抽出先の Scala 3 / TypeScript / JavaScript / Haskell / OCaml には 1 バイトも残らず、実行時オーバーヘッドはゼロです。

---

## 第 8 部：用語ミニ辞典

| 用語 | 1 行での説明 |
|---|---|
| **TCB（Trusted Computing Base）** | 正しさを信頼する最小限の核コード。Proof Samurai では `samurai.kernel` のみ。 |
| **de Bruijn 基準** | 証明を探索する層と検証するカーネルを分離し、小さなカーネルだけを通過した項を真とみなす設計原則。 |
| **カリー＝ハワード同型** | 「命題＝型」「証明＝停止するプログラム」「証明の簡約＝プログラムの評価」という 1 対 1 の同型。 |
| **判断（Judgment）`Γ ⊢ t : A`** | コンテキスト（仮定の集合）`Γ` のもとで項 `t` が型 `A` を持つという主張。 |
| **依存積型 `Pi` (`Π(x: A). B`)** | 引数 `x` の値によって返り値の型 `B` が変わり得る関数型。通常の `=>`、ジェネリクス、`forall` をすべて統合する。 |
| **依存ペア型 `Sigma` (`Σ(x: A). B`)** | 値 `x` と、その値に関する性質 `B(x)` の組。Proof Samurai では `Exists`（`Prop`）と `Subset`（`Type`）。 |
| **宇宙 / ソート (`Sort`)** | 型の型。`Prop : Type0 : Type1 : ...` の階層によりパラドックスを防ぐ。 |
| **非可述性（Impredicativity）** | `forall (P: Prop) => ...` のように `Prop` 全体にわたる量化の結果が再び `Prop` に収まる性質。 |
| **パラメータ vs 添字（Index）** | 帰納型の引数のうち、全コンストラクタ共通のものがパラメータ、コンストラクタごとに変わるものが添字。 |
| **motive（動機関数）** | 依存 `Match` において、マッチ対象の値・添字から「その分岐で返す型」を決める関数。 |
| **定義的等価 (`≡`) vs 命題的等価 (`===`)** | 計算（NbE）だけで一致するのが定義的等価（`refl` で閉じる）、証明項 `Eq` が必要なのが命題的等価。 |
| **NbE（Normalization by Evaluation）** | 構文木をクロージャ値へ評価してから比較・読み戻しを行う高速な正規化手法。 |
| **de Bruijn インデックス** | 変数を名前ではなく「何個外側の束縛か」の番号で表す方式。変数衝突を原理的に防ぐ。 |
| **厳密正性（Strict Positivity）** | 帰納型が自身のコンストラクタ引数の `=>` の左辺に現れない制約。カリーのパラドックスを防ぐ。 |
| **Subsingleton 除去** | 実行時分岐情報を持たない `Prop`（`False`, `True`, `Eq`, `Acc`）に限り `Type` への `Match` を許す規則。 |

---

## 次に読むべきドキュメント

- カーネル各モジュールの健全性チェックリスト：[KERNEL.md](KERNEL.md)
- 通常のプログラミング構文とタクティクの対照ガイド：[PROOFS_FOR_PROGRAMMERS.md](PROOFS_FOR_PROGRAMMERS.md)
- エラーコード `K005` / `K006` / `K020` / `K025` / `K030` / `K031` の具体例と直し方：[TROUBLESHOOTING.md](TROUBLESHOOTING.md)
- 公理 0 の IO・副作用検証（高階帰納型 `IO` / `Eff` の実用例）：[IO_VERIFICATION.md](IO_VERIFICATION.md)
