# AI エージェント連携ガイド

Proof Samurai は、人間のエンジニアだけでなく LLM プローバや探索型エージェントが扱いやすいように設計されています。トークン消費を抑えたゴール表現、コピーコストのない不変状態分岐、構造化された診断出力、そして誤った証明を一切通さない信頼カーネルを備えています。

## エージェント設計における主な特徴

1. **低トークンな畳み込みゴール表示**: 停止した再帰関数（`add`、`append`、`insertionSort` など）は生の `fix` AST を展開せず、`a + b`、`xs ++ ys`、`[0, 1, 2]` といった簡潔な表記で返します。
2. **不変状態による分岐・バックトラック**: `step(stateId, tactic)` は親状態を変更せずに新しい `stateId` を返すため、MCTS、ビーム探索、Tree-of-Thought にそのまま組み込めます。
3. **ワンショット検証・修正ループ（`proveGoal`）**: 候補のタクティク列全体を 1 往復で実行し、`kernelVerified: true` か、あるいは失敗箇所（`failedAtStep`、`goalShape`、残余ゴール、タクティク候補）を受け取れます。
4. **ファイル単位のホール一括検査（`inspectHoles` / `samurai goals --json`）**: `?hole1`, `?hole2` を含む証明スケルトンを 1 回の呼び出しで解析できます。
5. **シンボル一覧の取得（`listSymbols`）**: タクティク生成前に、利用可能なコンストラクタ・関数・定理・`@simp` 補題の正確な名前と型を確認できます。

## 推奨ワークフロー

### ステップ 1: NDJSON サーバの起動

```bash
sbt "run serve"
```

標準入力（`stdin`）へ 1 行 1 JSON オブジェクトを送信し、標準出力（`stdout`）から 1 行 1 JSON 応答を読み取ります。

### ステップ 2: コンテキスト読み込みとシンボル確認

```json
{"id": 1, "method": "loadFile", "params": {"path": "stdlib/List.samurai"}}
{"id": 2, "method": "listSymbols"}
```

### ステップ 3: ワンショット証明検証（`proveGoal`）

```json
{
  "id": 3,
  "method": "proveGoal",
  "params": {
    "name": "aiLemma",
    "statement": "forall (a: Nat, b: Nat) => (a + b) + 0 === b + a",
    "tactics": ["intros(a, b)", "arith"]
  }
}
```

応答例:

```json
{
  "id": 3,
  "ok": true,
  "result": {
    "verified": true,
    "kernelVerified": true,
    "theoremName": "aiLemma",
    "axiomsUsed": [],
    "isAxiomFree": true
  }
}
```

### ステップ 4: `batchStep` と `getProofTrace` による探索

1. `startProof` でルートの `stateId` と初期タクティク候補を取得します。
2. `batchStep` で同一の `stateId` に対し複数候補を 1 往復で評価します。
   ```json
   {"id": 4, "method": "batchStep", "params": {"stateId": 1, "tactics": ["refl", "intro(n)", "auto(5)"]}}
   ```
3. `isSolved: true` に到達した `stateId` に対し `getProofTrace` を呼び出し、そのままソースへ貼り付け可能な Scala 3 の `by { ... }` スクリプトを取得します。
   ```json
   {"id": 5, "method": "getProofTrace", "params": {"stateId": 7}}
   ```

### ステップ 5: 厳密モードでのコード抽出

```json
{"id": 6, "method": "extract", "params": {"target": "scala3", "moduleName": "VerifiedApp", "requireAxiomFree": true}}
```

## シェル型エージェント向け CLI（`--json`）

```bash
sbt "run check examples/Showcase.samurai --strict --json"
sbt "run goals draft.samurai --json"
sbt "run search stdlib/Sorting.samurai sort --json"
sbt "run verify-project . --strict --json"
```
