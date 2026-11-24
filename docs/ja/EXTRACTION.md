# 検証済みコード抽出

Proof Samurai は、計算用のデータ型（`Type`）と論理的な証拠（`Prop`）を明確に分離しています。信頼カーネルが subsingleton 除去規則を厳格に強制しているため、すべての `Prop` 値はプログラムの実行結果を変えることなく**健全に消去**できます。

## 抽出時に残る要素と消去される要素

| Proof Samurai の構成要素 | ソート | 抽出後の出力（Scala 3 / TS / JS / Haskell / OCaml） |
|---|---|---|
| `enum Nat: Type`, `enum List[A]: Type`, `enum Tree[A]: Type` | `Type` | 代数的データ型（`enum` / タグ付きユニオン / `data` / `type`）として出力 |
| `case class Queue[A](front: List[A], back: List[A])` | `Type` | Scala 3 の `final case class`、TS/JS オブジェクト、Haskell/OCaml の ADT として出力 |
| `def insertionSort`, `def enqueue`, `def vecHead` | `Type` | 通常の再帰関数として出力（OCaml では相互再帰を自動で `let rec ... and ...` 化） |
| `enum Eq`, `enum Le`, `enum Acc`, `enum And`, `enum Or`, `enum False` | `Prop` | **完全に消去**（実行時コード 0 バイト） |
| `theorem insertionSortIsSorted`, `theorem countInsertionSort` | `Prop` | **完全に消去**（抽出前にカーネル検証済み） |
| `Subset.Mk(value, proof)`（`proof: P(value)`） | `Type` + `Prop` フィールド | `proof` フィールドのみ消去され `Subset.Mk(value)`（`Subset_Mk value`）になる |
| 到達不能な添字付き分岐（例: `vecHead` における `Vec.Nil`） | 到達不能 | `throw new AssertionError(...)` / `P.error` / `failwith` へ変換 |

## 例: 検証済み挿入ソートから Scala 3 コードを生成

`stdlib/Sorting.samurai` の `sortVerified` は、ソート済みリスト本体に加えて「昇順に並んでいること（`Sorted(output)`）」および「各要素の出現回数が元のリストと一致すること（`forall target => count(target, output) === count(target, input)`）」の証明を `Subset` に包んで返します。

```scala
def sortVerified(items: List[Nat]):
  Subset[List[Nat], (output: List[Nat]) => IsSortedPermutation(items, output)]
```

次のコマンドで抽出を実行します。

```bash
sbt "run extract stdlib/Sorting.samurai --target scala3 --module VerifiedSorting --strict"
```

すべての定理が公理 0 で検証されたのち、証明フィールドが完全に消去されたスタンドアロンの Scala 3 コードが出力されます。

```scala
object VerifiedSorting {
  enum Subset[Domain] {
    case Mk(value: Domain)
  }

  def sortVerified(items: List[Nat]): Subset[List[Nat]] = {
    Subset.Mk[List[Nat]](insertionSort(items))
  }
}
```

## 出力ターゲット

### 1. Scala 3（`--target scala3`）

外部依存のないブレース構文の Scala 3 コードを生成します。そのまま `scalac` でコンパイルできます。

```bash
sbt "run extract stdlib/Sorting.samurai --target scala3 --module VerifiedSorting --out out/VerifiedSorting.scala --strict"
```

### 2. TypeScript（`--target ts`）

判別共用体（discriminated union）とジェネリック関数による型安全な ES モジュールを生成します。

```bash
sbt "run extract stdlib/Sorting.samurai --target ts --out out/sorting.ts --strict"
```

### 3. JavaScript（`--target js`）

Node.js やブラウザでそのまま実行できる、外部依存ゼロの ES モジュールを生成します。

```bash
sbt "run extract stdlib/Sorting.samurai --target js --out out/sorting.mjs --strict"
```

### 4. Haskell（`--target haskell` / `--target hs`）

`NoImplicitPrelude` + `import qualified Prelude as P` により Haskell 標準 `Prelude`（`Bool`・`Either`・`map`・`length`・`filter` 等）との名前衝突を完全に防ぎ、`Type_Ctor` 形式の衝突しないコンストラクタ（`Nat_Zero`・`List_Cons`・`Vec_Cons`・`Subset_Mk`）および一階 ADT への `deriving (P.Eq, P.Show)` を自動付与したスタンドアロンモジュールを生成します。

```bash
sbt "run extract stdlib/Sorting.samurai --target haskell --module VerifiedSorting --out out/VerifiedSorting.hs --strict"
```

### 5. OCaml（`--target ocaml` / `--target ml`）

OCaml 4.x / 5.x 向けのスタンドアロンモジュールを生成します。強連結成分（SCC）解析により相互再帰関数（`isEven` / `isOdd` 等）を自動的に `let rec ... and ...` ブロックへまとめ、コンストラクタ名を `Type_Ctor` 形式で曖昧性なく出力します。また `absurd` のような 0 引数・到達不能関数は `Stdlib.unit` でサンク化し、モジュール初期化時の即時例外や値制限を回避します。

```bash
sbt "run extract stdlib/Sorting.samurai --target ocaml --module VerifiedSorting --out out/verified_sorting.ml --strict"
```

## CI/CD 向け厳密検証ゲート（`--strict` / `--total` / `--json`）

CI パイプラインや自動エージェントから呼び出す場合は `--strict` を指定してください。依存グラフ内のどこかに `sorry` や `axiom` が含まれている場合、抽出はエラー終了します。`partial def` も禁止したい場合は `--total` を併用します。

```bash
sbt "run extract stdlib/Sorting.samurai --target scala3 --strict --total --json"
```

JSON 出力には `manifest` オブジェクトが含まれ、`extractedTypes`、`extractedFunctions`、`erasedPropositions`、`verifiedTheorems`、`axiomsUsed`、`partialFunctions`、`isAxiomFree`、`isTotal` を機械的に監査できます。
