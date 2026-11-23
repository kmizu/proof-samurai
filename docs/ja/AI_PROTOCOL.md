# JSON-RPC プロトコル仕様（`samurai serve`）

`sbt "run serve"` は、`stdin` / `stdout` 上で動作する状態付き・分岐対応の NDJSON JSON-RPC サーバを起動します。LLM プローバ、木探索・MCTS エージェント、および自律型コーディングエージェントからの利用を想定しています。

## 基本特性

1. **不変状態による分岐・バックトラック**: すべての `step(stateId, tactic)` は元の `stateId` を変更せず新しい `stateId` を発行します。同じ親状態から複数の候補タクティクを並列に試行できます。
2. **カーネルによる健全性保証**: すべてのサブゴールが閉じた時点で、サーバは明示的な De Bruijn 証明項を再構成し、`samurai.kernel.TypeChecker` で最初から検証したうえで `kernelVerified: true`、`axiomsUsed`、`isAxiomFree` を返します。
3. **構造化されたゴール情報**: 各応答には型付き仮定一覧、生ゴール型、NbE 正規化済みゴール型、および信頼度付き `suggestions` が含まれます。

## メソッド一覧

### `loadFile` / `loadSource`

```json
{"id": 1, "method": "loadFile", "params": {"path": "stdlib/Nat.samurai"}}
```

```json
{"id": 2, "method": "loadSource", "params": {"file": "demo.samurai", "source": "def id[A](x: A): A = x"}}
```

### `startProof`

```json
{"id": 3, "method": "startProof", "params": {"name": "myTheorem", "statement": "forall (n: Nat) => n + 0 === n"}}
```

### `proveGoal`（一括検証・修正用）

候補のタクティク列全体を 1 往復で実行し、信頼カーネルで検証します。

```json
{
  "id": 4,
  "method": "proveGoal",
  "params": {
    "name": "rearrange",
    "statement": "forall (a: Nat, b: Nat) => (a + b) + 0 === b + a",
    "tactics": ["intros(a, b)", "arith"]
  }
}
```

途中で失敗した場合は `failedAtStep`、`failedTactic`、畳み込み表示済みの `remainingGoals`（`goalShape` 付き）、および次の候補 `suggestions` を返します。

### `listSymbols`

ロード済みの帰納型、コンストラクタ、関数、定理、`@simp` 補題の一覧をコンパクトな JSON で返します。

### `step` / `batchStep` / `autoSolve` / `getProofTrace`

単一ステップ実行:

```json
{"id": 4, "method": "step", "params": {"stateId": 1, "tactic": "intro(n)"}}
```

単一の親状態に対して複数候補をまとめて評価（ビーム探索・MCTS 向け）:

```json
{"id": 5, "method": "batchStep", "params": {"stateId": 1, "tactics": ["refl", "intro(n)"]}}
```

組み込み自動証明探索を実行:

```json
{"id": 6, "method": "autoSolve", "params": {"stateId": 1, "maxDepth": 6}}
```

証明完了した `stateId` から Scala 3 の `by { ... }` スクリプトを再構成:

```json
{"id": 7, "method": "getProofTrace", "params": {"stateId": 5}}
```

### `inspectHoles`

```json
{"id": 8, "method": "inspectHoles", "params": {"file": "draft.samurai", "source": "..."}}
```

### `suggest`

```json
{"id": 9, "method": "suggest", "params": {"stateId": 2}}
```

### `searchLemmas`

- キーワード検索:
  ```json
  {"id": 10, "method": "searchLemmas", "params": {"query": "addComm", "limit": 10}}
  ```
- 現在のゴールとの型単一化による関連補題検索:
  ```json
  {"id": 11, "method": "searchLemmas", "params": {"stateId": 2, "limit": 10}}
  ```

### `extract`

```json
{"id": 12, "method": "extract", "params": {"target": "scala3", "moduleName": "VerifiedApp", "requireAxiomFree": true}}
```

`"scala3"`、`"ts"`、`"js"` をサポートし、生成コードおよび `manifest`（`extractedTypes`, `extractedFunctions`, `erasedPropositions`, `verifiedTheorems`, `axiomsUsed`, `isAxiomFree`）を返します。
