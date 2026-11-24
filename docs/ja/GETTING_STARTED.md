# はじめに

**Proof Samurai** は、Scala 3 のブレース構文（インデント非依存）で関数型プログラムを記述し、小規模な信頼カーネル（Trusted Kernel）によって性質を形式検証したうえで、すべての証明項を消去した **Scala 3 / TypeScript / JavaScript** コードを抽出できる依存型証明支援系です。

Scala、TypeScript、Rust、Haskell などの静的型付き関数型言語の基本的な知識があれば、型理論の専門知識がなくても使い始められます。

## 1. 環境構築と Studio の起動

ビルドおよび実行には JDK（Java 17 以上推奨）と `sbt` が必要です。テストスイートで動作を確認できます。

```bash
sbt test
```

対話的に試すには、組み込みのローカル Web IDE（Proof Samurai Studio）を起動します。

```bash
sbt "run studio"
```

ブラウザで `http://localhost:8080` を開くと、以下の機能が利用できます。

- Scala 3 ブレース構文エディタとカーネル検証（`Ctrl+Enter`）
- 公理使用状況の表示（公理 0 の厳密検証ステータス）
- 未完証明ホール（`?hole`）のゴール表示とタクティク候補の提示
- 分岐・バックトラック可能な対話的証明ツリー（Interactive Proof Tree）
- Scala 3 / TypeScript / JavaScript へのコード抽出パネル

## 2. データ型と関数の定義

通常の Scala 3 と同様に `enum` や `def` を記述します。ブロックはすべて `{ ... }` で明示的に囲みます。

```scala
import Prelude.*
import Nat.*

def doubleValue(number: Nat): Nat = {
  number + number
}

#eval doubleValue(3)
```

`#eval doubleValue(3)` はカーネル内蔵の正規化器（NbE: Normalization by Evaluation）で評価され、`6` を出力します。

## 3. 定理と証明の記述スタイル

Proof Samurai における `theorem` は、通常のプログラミングと別世界の記法ではありません。**仕様（`Prop`）を戻り値型とする純粋関数**そのものであり、`by { ... }` タクティクブロックはその関数本体（`match`・再帰・型変換）を組み立てて最終的にカーネルへ渡すための補助構文です。同じ定理を通常の `def` で直接書いたコードとタクティク版の見比べは、第 02 章「証明とタクティクは通常のプログラムと何の関係があるのか」を参照してください。

Proof Samurai では、定理の性質に応じて複数の証明スタイルを使い分けられます。

### 計算と自動証明（`refl`, `decide`, `arith`, `auto`）

```scala
import Prelude.*
import Nat.*

theorem twoPlusTwo: 2 + 2 === 4 = by {
  refl
}

theorem rearrange(first: Nat, second: Nat, third: Nat):
  (first + second) + (third + 0) === third + (second + first) = by {
  arith
}
```

### 等式推論ブロック（`calc { ... }`）

途中の変形ステップを明示したい場合は `calc` ブロックを使用します。

```scala
import Prelude.*
import Nat.*
import List.*

theorem lengthThreeWay[Element](first: List[Element], second: List[Element], third: List[Element]):
  length((first ++ second) ++ third) === length(third) + (length(first) + length(second)) = {
  calc {
    length((first ++ second) ++ third)
    === (length(first) + length(second)) + length(third) by { simp }
    === length(third) + (length(first) + length(second)) by { arith }
  }
}
```

### 構造的帰納法（`induction`）

```scala
import Prelude.*
import Nat.*

theorem addZeroRightDemo(value: Nat): value + 0 === value = by {
  induction(value) {
    case Zero => { refl }
    case Succ(pred, ih) => {
      rewrite(ih)
      refl
    }
  }
}
```

## 4. 証明ホール（`?hole`）によるゴール確認

証明の途中で次に書くべき手順が分からないときは、任意の場所に `?todo` のような名前付きホールを置けます。

```scala
import Prelude.*
import Nat.*

theorem helpMe(left: Nat, right: Nat): left + right === right + left = by {
  ?todo
}
```

CLI で `sbt "run goals yourfile.samurai"` を実行するか、Studio で `Ctrl+Enter` を押すと、その地点の仮定一覧、正規化されたゴール `⊢ ...`、およびタクティク候補が表示されます。

## 5. 検証済みコードの抽出

`Prop` に属する定義（定理、`===`、`Sorted`、`Le`、`And`、`Or` など）は検証専用の証拠であり、実行時コードには残りません。

```bash
sbt "run extract stdlib/Sorting.samurai --target scala3 --module VerifiedSorting --strict"
```

`--strict` オプションを指定すると、依存するすべての定義・定理において `axiom` および `sorry` が一切使われていないことを保証したうえでコードを出力します。

## 次のステップ

- タクティクと通常の関数・パターンマッチ・再帰との対応関係や本番コードへの効き方は「証明とタクティクは通常のプログラムと何の関係があるのか」を参照してください。
- 言語構文の詳細（`mutual`・`termination_by`・`partial def` を含む）については「言語リファレンス」を参照してください。
- ゴールの形からタクティクを引くには「タクティク・クックブック」が便利です。
- カーネルエラーの意味と修正例については「エラー解決ガイド」を参照してください。
- リポジトリ内の全 `.samurai` ファイルを一括検証するには `sbt "run verify-project . --strict"` を実行します。
