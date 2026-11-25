# CoC / CIC 入門：定理証明器の正体

定理証明支援系（Coq / Rocq、Lean、Agda、Proof Samurai など）は、外から見ると「不思議な推論エンジンが数学を解いているブラックボックス」に見えがちです。しかし、その心臓部にある **CoC（Calculus of Constructions：構成の計算）** と **CIC（Calculus of Inductive Constructions：帰納的構成の計算）** の仕組みを知ると、**魔法は一切なく、極めて小さな静的型検査器そのもの**であることが分かります。

この章では、「なぜ型検査だけで数学の証明を保証できるのか」「なぜ帰納型・宇宙階層・厳密正性・停止性検査が必要なのか」を、Proof Samurai のカーネル実装（`src/main/scala/samurai/kernel/`）と対応づけながら解説します。

---

## 1. 全体像：ブラックボックスの中身は「小さな型検査器」だけ

定理証明器の設計は **de Bruijn 基準（de Bruijn criterion）** と呼ばれる原則に基づいています。

```text
  [人間 / AI が書く世界（信頼しない = Untrusted）]
    Surface 構文 / タクティク (omega, cc, tauto, simp, auto) / エラボレータ
                          |
                          |  巨大な探索や自動化の結果として
                          |  「具体的な証明項 (Core Term)」を生成
                          v
  [信頼カーネル（Trusted Computing Base = samurai.kernel）]
    Term (たった 12 種類の AST) + TypeChecker + NbE + Positivity + Termination
                          |
                          |  「この項 t は本当に型 T を持つか？」だけを検証
                          v
               OK (KernelEnv に登録) / NG (拒否)
```

ポイントは次の 2 点です。

- **タクティク（`omega`、`simp`、`induction`、`auto`）や AI エージェントは一切信頼しない。** これらは「証明項（ただの関数プログラム）」を組み立てるための便利ツールにすぎません。
- **最後に正しさを保証するのはカーネルだけ。** たとえタクティクにバグがあっても、生成された項がカーネルの型検査を通らなければ定理として認められません。

つまり定理証明器の「正体」を理解するとは、**カーネルが受け取る最小のコア言語（CIC）とその型検査規則を理解すること**に他なりません。

---

## 2. カリー＝ハワード対応：命題は型、証明はプログラム

CoC / CIC の土台は **カリー＝ハワード対応（Curry-Howard correspondence）** です。論理の概念とプログラミング言語の型は、比喩ではなく**同一のオブジェクト**として扱われます。

| 論理の世界 | プログラミング（型理論）の世界 | Proof Samurai の記述 |
|---|---|---|
| 命題 `P` | 型 `P : Prop` | `a + b === b + a` |
| 命題 `P` の証明 `pf` | 型 `P` を持つ値（式）`pf : P` | `theorem ... = by { ... }` |
| 含意 `P => Q` | 関数型 `P => Q` | `(h: P) => ...` |
| 全称量化 `∀x:A. P(x)` | **依存関数型 `Π(x: A). P(x)`** | `forall (n: Nat) => n + 0 === n` |
| 論理積 `P /\ Q` | ペア型（直積）`And[P, Q]` | `And.Intro(hp, hq)` |
| 論理和 `P \/ Q` | タグ付きユニオン（直和）`Or[P, Q]` | `Or.Left(hp)` / `Or.Right(hq)` |
| 存在量化 `∃x:A. P(x)` | 依存ペア型 `Exists[A, P]` | `Exists.Intro(w, pw)` |
| 偽（矛盾）`False` | コンストラクタが 0 個の空型 `False` | `enum False: Prop {}` |
| 否定 `~P` | `False` を返す関数型 `P => False` | `def Not(P: Prop): Prop = P => False` |

「`False` を証明できない」とは、「コンストラクタが 0 個の型 `False` の値を、停止する純粋プログラムで 1 つも作れない」ことと完全に同じです。

---

## 3. CoC（Calculus of Constructions）：すべてを 1 つの `Pi` 型に統合する

通常のプログラミング言語では「値」「型」「ジェネリクス」「型コンストラクタ」が別々の仕組みに分かれています。型理論ではこれを **ラムダキューブ（Lambda Cube）** の 4 つの軸で整理します。

1. **値から値への関数**（単純型付きラムダ計算）: `(x: Nat) => x + 1`
2. **型から値への関数**（多相・ジェネリクス / System F）: `[A: Type](x: A) => x`
3. **型から型への関数**（型コンストラクタ / F-omega）: `List : Type => Type`
4. **値から型への関数**（**依存型** / lambda-P）: `Vec : Type => Nat => Type`、`Eq : [A] => A => A => Prop`

**CoC（Thierry Coquand & Gérard Huet, 1988）** の革命的なアイデアは、これら 4 種類をすべて **たった 1 つの依存積型 `Pi(x: A, B)`（数学記号では `Π(x: A). B`）** に統一したことです。

- `B` に `x` が現れないとき：`Pi(_, A, B)` は普通の関数型 `A => B`（および論理の含意）になる。
- `A` が `Type` のとき：`Pi(A, Type, A => A)` は多相関数型（ジェネリクス）になる。
- `B` が `Type` のとき：`Pi(_, Type, Type)` は `List` のような型コンストラクタになる。
- `B` の型に値 `x` が現れるとき：`Pi(n, Nat, Eq(add(n, 0), n))` は全称命題 `∀n:Nat. n + 0 = n` や依存型 `Vec[A](n)` になる。

CoC には「値の世界」と「型の世界」の壁がありません。`Nat` も `Type` も `n + 0 === n` も、すべて同じ `Term` 型で表現されます。

---

## 4. なぜ CoC だけでは足りないのか → CIC（帰納的構成の計算）

純粋な CoC だけでもチャーチエンコーディングによって自然数を `forall [X: Type] => (X => X) => X => X` のように表現することはできます。しかし、純粋な CoC には致命的な弱点があります。

- **ペアノの公理「`0 !== 1`」すら証明できない**（追加公理なしでは、`Zero` と `Succ(Zero)` が異なることを導けない）。
- **自然数の帰納法原理**や効率的な前駆関数（`pred`）・パターンマッチが直接書けない。

そこで、CoC に **帰納型（Inductive Types）** と **依存パターンマッチ（`Match`）**、**構造的再帰（`Fix`）** を中核プリミティブとして組み込んだものが **CIC（Calculus of Inductive Constructions）** です（Coq / Rocq、Lean、そして Proof Samurai の基礎理論）。

CIC の強みは、**論理記号もデータ構造もすべて同じ `enum` 定義で構築できる**ことです。Proof Samurai の標準ライブラリでは、以下がすべて組み込み公理ゼロの帰納型として定義されています。

```scala
// 論理演算子もすべてただの帰納型 (stdlib/Prelude.samurai)
enum False: Prop {}
enum True: Prop { case Intro }
enum And[Left: Prop, Right: Prop]: Prop { case Intro(left: Left, right: Right) }
enum Or[Left: Prop, Right: Prop]: Prop { case Left(value: Left); case Right(value: Right) }
enum Eq[T: Type](lhs: T): T => Prop { case Refl }

// データ構造も同じ仕組み (stdlib/Nat.samurai, stdlib/Vec.samurai)
enum Nat: Type { case Zero; case Succ(pred: Nat) }
enum Vec[A: Type]: Nat => Type {
  case Nil: Vec[A](Nat.Zero)
  case Cons(n: Nat, head: A, tail: Vec[A](n)): Vec[A](Nat.Succ(n))
}
```

### 等式 `Eq` と `rewrite` の正体

等号 `===`（`Eq`）でさえ特別な組み込み公理ではありません。`Eq` はコンストラクタを `Refl`（反射律 `x === x`）の 1 つだけ持つ添字付き帰納型です。

`h : a === b` を使ってゴール `P(a)` を `P(b)` に書き換える `rewrite(h)` は、CIC 内部では単に **`h` に対する依存パターンマッチ（`Match`）** として展開されます。

- 対象 `h : Eq[T](a, b)` を分解すると、可能なケースは `Eq.Refl`（すなわち `b` が `a` と同一のケース）しかない。
- したがって、`P(a)` の証明があれば `P(b)` が自動的に成り立つ（ライプニッツの不可識別者同一の原理）。

### 依存パターンマッチと `motive`

普通のプログラミング言語の `match` では、すべての分岐が同じ型を返します。CIC の `Match` は **motive（動機関数）** `M` を持ち、**分岐ごとに返り値の型がコンストラクタに応じて変化**します。

例えば `n: Nat` に対して `n + 0 === n` を証明するときの motive は `M = (k: Nat) => k + 0 === k` です。

- `case Nat.Zero` 分岐で要求される型: `M(Nat.Zero)` = `0 + 0 === 0`（計算で `0 === 0` に簡約され `Eq.Refl` で完了）
- `case Nat.Succ(pred)` 分岐で要求される型: `M(Nat.Succ(pred))` = `Nat.Succ(pred) + 0 === Nat.Succ(pred)`（再帰呼び出し `ih : pred + 0 === pred` から構築）

つまり **CIC における「数学的帰納法」とは、「`Fix`（構造的再帰関数）＋ 依存 `Match`（motive 付き分岐）」の組み合わせそのもの**です。

---

## 5. 型の中の計算：変換規則（Conversion）と NbE

CIC をプログラミング言語の型システムと最も大きく分けるのが **変換規則（Conversion Rule）** です。

```text
  Γ ⊢ t : A      A ≡ B (計算すると同じになる)
  --------------------------------------------  [Conv]
                 Γ ⊢ t : B
```

普通の言語では `Vec[Nat](2 + 2)` と `Vec[Nat](4)` は別々の型になりますが、CIC ではカーネルが型の中の式を実際に計算（正規化）して比較するため、`2 + 2` と `4` は **定義的等価（definitionally equal: `≡`）** となります。だから `theorem twoPlusTwo: 2 + 2 === 4 = by { refl }` は `Eq.Refl` 一発で通ります。

Proof Samurai のカーネルでは、[NbE.scala](https://github.com/kmizu/proof-samurai/blob/main/src/main/scala/samurai/kernel/NbE.scala)（Normalization by Evaluation）が以下の簡約を自動で実行して `A ≡ B` を判定します。

| 簡約規則 | 記号 | 意味 |
|---|---|---|
| ベータ簡約 | `β` | 関数適用 `((x) => body)(arg)` を `body[x := arg]` へ計算 |
| ゼータ簡約 | `ζ` | `val x = v; body`（`Let`）を展開 |
| デルタ簡約 | `δ` | 透過的な `def` 定義を展開（`partial def` は絶対に展開しない） |
| イオタ簡約 | `ι` | コンストラクタ値に対する `Match` の該当分岐を実行 |
| 不動点展開 | `fix` | `Fix` / `MutualFix` を、**減少引数がコンストラクタ値（`VCtor`）のときに限り**展開 |
| 証明無関係性 | `PI` | 同じ `Prop` 型 `P` に属する任意の 2 つの証明項 `pf1, pf2 : P` を定義的等価とみなす |

`Fix` を「減少引数がコンストラクタ値のときだけ展開する」制約により、型検査中の正規化が無限ループに陥ることを防いでいます。

---

## 6. Proof Samurai カーネルの全体：たった 12 個の `Term`

「ブラックボックスではない」ことを最も端的に示すのが、[Term.scala](https://github.com/kmizu/proof-samurai/blob/main/src/main/scala/samurai/kernel/Term.scala) の定義です。Proof Samurai のどんな複雑な定理も関数も、最終的には以下の **12 個のコンストラクタだけ**からなる `Term` に変換されて検証されます。

```scala
enum Term {
  // --- CoC のコア（7 種）---
  case USort(sort: Sort)                                   // Prop, Type0, Type1, ...
  case Var(idx: Int)                                       // de Bruijn インデックス変数
  case Const(name: String)                                 // 定義済み関数・定理・公理への参照
  case Pi(name: String, domain: Term, codomain: Term)      // 依存積型 forall (x: A) => B
  case Lam(name: String, domain: Term, body: Term)         // ラムダ抽象 (x: A) => body
  case App(fn: Term, arg: Term)                            // 関数適用 fn(arg)
  case Let(name: String, ty: Term, value: Term, body: Term)// 局所束縛 val x: T = v; body

  // --- CIC の帰納型拡張（5 種）---
  case Ind(name: String)                                   // 帰納型名 (Nat, List, Eq, IO, ...)
  case Ctor(indName: String, ctorName: String)             // コンストラクタ (Nat.Succ, Eq.Refl, ...)
  case Match(indName: String, params: List[Term], motive: Term, scrutinee: Term, branches: List[MatchBranch])
  case Fix(name: String, recArgIdx: Int, ty: Term, body: Term)     // 構造的再帰
  case MutualFix(defs: List[MutualFixDef], selectedIndex: Int)     // 相互構造的再帰
}
```

### de Bruijn インデックスとは

変数は名前ではなく「何個外側の束縛（`Lam` / `Pi` / `Let`）を指すか」という番号 `Var(idx)` で保持されます（`Var(0)` が最も内側）。これにより変数名の衝突（capture）が原理的に起きず、アルファ同値性の比較も単純な構造比較（`Term.alphaEq`）だけで済みます。

### コア型検査規則（`TypeChecker.scala`）

カーネルが行う型推論の核は、次の 6 つの規則に集約されます。

```text
  [Sort]   Γ ⊢ Prop : Type0          Γ ⊢ Type(i) : Type(i+1)

  [Var]    (x : A) ∈ Γ  ==>  Γ ⊢ x : A

  [Pi]     Γ ⊢ A : s1      Γ, x:A ⊢ B : s2
           ----------------------------------
             Γ ⊢ Π(x: A). B : piSort(s1, s2)

  [Lam]    Γ ⊢ A : s       Γ, x:A ⊢ b : B
           ----------------------------------
             Γ ⊢ (x: A) => b : Π(x: A). B

  [App]    Γ ⊢ f : Π(x: A). B      Γ ⊢ a : A
           ----------------------------------
                Γ ⊢ f(a) : B[x := a]

  [Conv]   Γ ⊢ t : A      A ⪯ B (NbE + 累積性)
           ----------------------------------
                       Γ ⊢ t : B
```

ここで `piSort(s1, s2)` は `Sort.scala` にそのまま 3 行で実装されています。

- `piSort(_, Prop) = Prop`（`Prop` の非可述性：`forall (P: Prop) => P => P` のような全称量化が再び `Prop` に収まる）
- `piSort(Prop, Type(j)) = Type(j)`
- `piSort(Type(i), Type(j)) = Type(max(i, j))`

---

## 7. なぜ各健全性チェックが不可欠なのか（外すと起きるパラドックス）

CIC には一見すると厳しすぎる制約が 4 つあります。これらは単なる意地悪ではなく、**1 つでも外すと `False`（任意の嘘の命題）が証明できてしまい、定理証明器として破綻する**ために存在します。

### 制約 1：宇宙階層（`Type(0) : Type(1) : Type(2) : ...`）

もし `Type : Type` を許すと、集合論のラッセルのパラドックスの型理論版である **ジラールのパラドックス（Girard's paradox）** により、`False` の証明項が構成できてしまいます。

そのためカーネルは `Prop : Type0 : Type1 : ...` と階層化し、`Type0` の帰納型のフィールドに `Type0` 自身を入れようとすると `K005` で拒否します。

### 制約 2：厳密正性（Strict Positivity / `Positivity.scala`）

もし帰納型 `Bad` が自身のコンストラクタの関数引数の左辺（負の位置）に現れることを許すと、**カリーのパラドックス（Curry's paradox）** が発生します。

```scala
// 厳密正性に違反する危険な型（Proof Samurai は K006 で拒否）
enum Bad: Prop {
  case Mk(f: Bad => False)
}
// もしこれを許すと、自己適用だけで停止性検査をすり抜けて False が証明できる！
// def omega(b: Bad): False = b match { case Bad.Mk(f) => f(b) }
// def paradox: False = omega(Bad.Mk(omega))
```

`Bad` には明示的な再帰関数（`Fix`）が 1 つもないのに、自己適用 `omega(Bad.Mk(omega))` によって無限計算と `False` の証明が作れてしまいます。`Positivity.scala` は `Not(Bad)` のような透過的エイリアスも NbE で展開したうえで負の出現を完全に遮断します（`K006`）。

### 制約 3：停止性検査（`Termination.scala`）と `partial def` の隔離

もし任意の一般再帰をそのまま定理に許すと、次の 1 行ですべての命題が「証明」できてしまいます。

```scala
// 無限ループによる嘘の証明（Proof Samurai は K020 で拒否）
def loop(n: Nat): False = { loop(n) }
```

したがって CIC カーネルでは、すべての再帰関数（`Fix` / `MutualFix`）について、パターンマッチで得た**構造的に真に小さい部分項**に対してのみ再帰呼び出しを許可します（`K020`）。

- クイックソートやユークリッドの互除法のように構造的減少だけでは書けないアルゴリズムには、到達可能性述語 `Acc` に対する構造的再帰（`termination_by` / `stdlib/WellFounded.samurai`）を使うことで、**公理 0 のまま整礎再帰**を検証できます。
- 停止性証明を付けたくない計算関数には `partial def` を使えますが、`Prop` を返せず（`K030`）、全関数や定理からは一切参照できないよう隔離されています（`K031`）。

### 制約 4：`Prop` と `Type` の分離、および Subsingleton 除去

なぜ計算用の `Type` とは別に論理用の `Prop` が存在するのでしょうか。理由は 3 つあります。

1. **実行時 0 バイトの証明消去（Extraction）**: `Prop` の値は実行時に一切影響しないため、Scala 3 / TypeScript / Haskell / OCaml 抽出時に完全に削除できます。
2. **証明無関係性（Proof Irrelevance）**: 「どう証明したか」の違いで型チェックが壊れないように、同じ命題の証明同士を同一視できます。
3. **非可述性（Impredicativity）**: すべての命題にわたる全称量化 `forall (P: Prop) => ...` を `Prop` 内に閉じ込められます。

この 3 つを両立させるため、**`Prop` の値を分解して `Type`（実行時データ）を取り出す操作**には厳格な制限（Subsingleton 除去）がかかります。

- **許可される例**: `False`（コンストラクタ 0 個なので到達不能）、`Eq`（コンストラクタ 1 個 `Refl` のみで追加情報なし）、`Acc`（コンストラクタ 1 個でフィールドが `Prop` のみ）。
- **禁止される例（`K025`）**: `Or[P, Q]` や `Exists[Nat, P]` から `Nat` や `Bool` を取り出すこと。もし許すと、左か右か・証人 `x` が何かという情報に実行結果が依存してしまい、証明無関係性とも 0 バイト消去とも矛盾します（計算に使う値には `Either` や `Subset` を使います）。

---

## 8. 具体例で追跡する：タクティク証明が CIC 項になるまで

最後に、普段書くタクティク証明がカーネル内部でどう扱われるかを 1 つの例で追いかけます。

### ステップ 1：ユーザーが書くコード（Untrusted 層）

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

### ステップ 2：タクティクが組み立てるコア CIC 項

`Tactics.scala` はこのスクリプトを実行して、およそ次の構造を持つ 1 本の純粋な CIC 項を生成します（読みやすさのため名前付きで表記）。

```scala
Fix(
  name = "addZeroRight",
  recArgIdx = 0,
  ty = Pi(n: Nat, Eq[Nat](add(n, Nat.Zero), n)),
  body = Lam(n: Nat,
    Match(
      indName = "Nat",
      motive = Lam(k: Nat, Eq[Nat](add(k, Nat.Zero), k)),
      scrutinee = n,
      branches = [
        case Zero =>
          Eq.Refl[Nat](Nat.Zero),
        case Succ(pred) =>
          // ih = addZeroRight(pred) : Eq[Nat](add(pred, 0), pred)
          // Match on ih (rewrite) transports Eq.Refl(Succ(pred)) to Eq(Succ(add(pred, 0)), Succ(pred))
          Match(
            indName = "Eq",
            motive = Lam(y: Nat, Lam(_: Eq[Nat](add(pred, Nat.Zero), y),
                       Eq[Nat](Nat.Succ(add(pred, Nat.Zero)), Nat.Succ(y)))),
            scrutinee = addZeroRight(pred),
            branches = [ case Refl => Eq.Refl[Nat](Nat.Succ(add(pred, Nat.Zero))) ]
          )
      ]
    )
  )
)
```

### ステップ 3：カーネル（Trusted 層）が検証する 4 点

1. **型検査（`TypeChecker` + `NbE`）**:
   - `Zero` 分岐：`add(Nat.Zero, Nat.Zero)` が NbE で `Nat.Zero` に簡約されるため、`Eq.Refl(Nat.Zero)` が `Eq(add(0, 0), 0)` に適合。
   - `Succ(pred)` 分岐：`add(Nat.Succ(pred), Nat.Zero)` が NbE で `Nat.Succ(add(pred, Nat.Zero))` に簡約されるため、`Eq` の `Match` の結果型が `Eq(add(Succ(pred), 0), Succ(pred))` に一致。
2. **網羅性検査**: `Nat` の `Zero` / `Succ`、`Eq` の `Refl` がすべて揃っていることを確認。
3. **停止性検査（`Termination`）**: `addZeroRight(pred)` の引数 `pred` が、マッチ対象 `n` から取り出した真に小さい部分項であることを確認。
4. **公理追跡（`Env`）**: 依存先に `axiom` や `sorry` が 0 個であることを記録。

### ステップ 4：コード抽出（Extraction）

`addZeroRight` の返り値型は `Eq(...) : Prop` のため、`Erasure.scala` がこの定理を丸ごと消去し、本番出力（Scala 3 / TypeScript / JavaScript / Haskell / OCaml）には実行時コスト 0 バイトになります。

---

## 次に読むべきドキュメント

- カーネル各モジュールの正確な仕様とエラーコード対応：[KERNEL.md](KERNEL.md)
- タクティクと通常プログラミングの対応関係：[PROOFS_FOR_PROGRAMMERS.md](PROOFS_FOR_PROGRAMMERS.md)
- エラーコード `K005` / `K006` / `K020` / `K025` / `K030` / `K031` の具体例と直し方：[TROUBLESHOOTING.md](TROUBLESHOOTING.md)
