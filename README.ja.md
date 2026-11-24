# <img src="docs/favicon.svg" alt="" width="28" height="28" align="absmiddle" /> Proof Samurai (`proof-samurai`)

[English](README.md) | [日本語](README.ja.md) | [ドキュメント (GitHub Pages / 日本語)](https://kmizu.github.io/proof-samurai/#ja/home)

インデント非依存の Scala 3 ブレース構文を採用した依存型証明支援系です。小規模な信頼カーネル（Trusted Kernel）による厳密な検証と、証明項を完全に消去する Scala 3 / TypeScript / JavaScript / Haskell / OCaml へのコード抽出機能を備えています。

---

## 概要

- **インデント非依存の Scala 3 ブレース構文**
  `enum`、`case class`、`def`、`mutual`、`termination_by` / `decreasing_by`、隔離された `partial def`、`val`、`theorem`、`[1, 2, 3]` リストリテラル、`match { case ... => ... }`、`if (...) { ... } else { ... }`、`calc { ... }` 等式推論、ドット射影（`pair.first`）、UFCS（`items.length`）、`by { ... }` タクティクブロックをサポートします。すべてのブロックは `{ ... }` で明示的に囲みます。
- **小規模な信頼カーネル（`samurai.kernel`）**
  - de Bruijn 基準に基づく De Bruijn インデックス型 Martin-Löf / CIC コア（エラボレータ、タクティク、`arith`、`auto`、AI セッションはいずれも非信頼扱いとし、最終的にカーネルが最初から型検査）
  - 累積的宇宙階層（`Prop : Type0 : Type1 : ...`）
  - NbE 正規化を伴う厳密正性検査
  - 構造的減少・相互再帰の停止性検査、公理 0 の `Acc` ベース整礎再帰（`termination_by`）、および `partial def` の健全な隔離（`K030` / `K031`）
  - Subsingleton・添字強制 `Prop` 除去規則と定義的証明無関係性（`False` / `Eq` / `Acc` の `Type` 除去を許可、`Or` / `Exists` は拒否）
  - 公理・`sorry` の推移的追跡（`--strict` で公理 0、`--total` で `partial def` 禁止を強制）
- **検証済みコード抽出（`samurai.extract`）**
  - `Prop` 型、定理、`Subset` の証明フィールド、到達不能な添字付き分岐（`vecHead` の `Vec.Nil` など）を健全に消去
  - スタンドアロンの Scala 3（ブレース構文）、TypeScript、JavaScript（ES モジュール）、Haskell（`NoImplicitPrelude`）、OCaml（SCC による `let rec ... and ...` 生成）および JSON 形式の `ExtractionManifest` を出力
- **ローカル Web IDE と AI 証明サーバ（`samurai.ui`, `samurai.ai`）**
  - **Proof Samurai Studio**（`sbt "run studio"`）: ライブカーネル検証、`?hole` 検査、分岐可能な対話的証明ツリー、コード抽出、日英ドキュメントを備えた Web IDE
  - **NDJSON 証明サーバ**（`sbt "run serve"`）: 低トークン畳み込みゴール、不変状態分岐（`stateId`）、`proveGoal`、`batchStep`、`inspectHoles`、`listSymbols`、`getProofTrace`

---

## クイックスタート

```bash
# テストスイートの実行
sbt test

# リポジトリ内の全 .samurai ファイルを公理 0 で一括検証
sbt "run verify-project . --strict"

# ローカル Web IDE の起動 (http://localhost:8080)
sbt "run studio"
```

### 主な CLI コマンド

```bash
# 単一ファイルの検証と #eval 評価
sbt "run check examples/Showcase.samurai --strict"

# 未完ホール (?hole) のゴールとタクティク候補を検査
sbt "run goals draft.samurai --json"

# 検証済み定義・定理の検索
sbt "run search stdlib/Sorting.samurai sort"

# 検証済み挿入ソートを Scala 3 / TypeScript / JavaScript / Haskell / OCaml へ抽出
sbt "run extract stdlib/Sorting.samurai --target scala3 --module VerifiedSorting --strict"
sbt "run extract stdlib/Sorting.samurai --target ts --strict"
sbt "run extract stdlib/Sorting.samurai --target js --strict"
sbt "run extract stdlib/Sorting.samurai --target haskell --module VerifiedSorting --strict"
sbt "run extract stdlib/Sorting.samurai --target ocaml --module VerifiedSorting --strict"

# 対話型 REPL / AI 向け NDJSON サーバ
sbt "run repl"
sbt "run serve"
```

---

## ドキュメント

Web 版（日本語 / English）: https://kmizu.github.io/proof-samurai/#ja/home

- [はじめに](docs/ja/GETTING_STARTED.md)
- [証明・タクティクと通常コードの関係](docs/ja/PROOFS_FOR_PROGRAMMERS.md)
- [言語リファレンス](docs/ja/LANGUAGE.md)
- [タクティク・クックブック](docs/ja/TACTICS_COOKBOOK.md)
- [検証済みコード抽出](docs/ja/EXTRACTION.md)
- [カーネル・型エラー解決ガイド](docs/ja/TROUBLESHOOTING.md)
- [信頼カーネルのアーキテクチャ](docs/ja/KERNEL.md)
- [AI エージェント連携ガイド](docs/ja/AI_AGENT_GUIDE.md)
- [JSON-RPC プロトコル仕様](docs/ja/AI_PROTOCOL.md)

---

## ディレクトリ構成

- `src/main/scala/samurai/kernel/` — 信頼カーネル（`Term`, `Env`, `NbE`, `Positivity`, `Termination`, `TypeChecker`, `Pretty`）
- `src/main/scala/samurai/syntax/` — インデント非依存 Scala 3 ブレース構文の字句解析・AST・パーサ
- `src/main/scala/samurai/elab/` — 双方向エラボレータ、メタ変数単一化、パターンマッチコンパイラ、`calc`・`termination_by` 展開
- `src/main/scala/samurai/tactic/` — LCF スタイルタクティク・コンビネータ（`<;>`, `in hyp`, `obtain`, `by_cases`, `tauto`）、証明生成型 `ArithTactic`（`arith`/`ring`）、`OmegaTactic`（`omega`/`lia`）、`CongruenceClosure`（`cc`）、`ProofSearch`（`auto`, `suggest`）
- `src/main/scala/samurai/extract/` — `Prop`・型消去 IR およびコード生成器（`Scala3Emitter`, `TsEmitter`, `JsEmitter`, `HaskellEmitter`, `OCamlEmitter`）
- `src/main/scala/samurai/ui/` & `src/main/resources/studio/` — 組み込み HTTP サーバと Proof Samurai Studio Web IDE
- `src/main/scala/samurai/ai/` — 分岐対応 NDJSON 証明サーバ（`ProofSessionServer`）と複数行 REPL
- `stdlib/` — 公理 0 で検証済みの標準ライブラリ（`Prelude`, `Nat`, `List`, `Vec`, `Tree`, `Option`, `Queue`, `Sorting`, `WellFounded`）
- `examples/` — 実行可能なサンプル（`HelloProof`, `VerifiedSort`, `SafeVec`, `Showcase`, `AdvancedRecursion`, `PracticalProving`）
- `docs/` — 英語・日本語（`docs/ja/`）ドキュメントおよび GitHub Pages サイト
