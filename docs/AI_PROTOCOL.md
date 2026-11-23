# Proof Samurai AI Protocol (`samurai serve`)

Proof Samurai provides an AI-native, stateful, branching NDJSON JSON-RPC server over `stdin`/`stdout` (`sbt "run serve"`), designed specifically for LLM provers, tree-search / MCTS agents, and autonomous coding agents.

## Key Properties

1. **Zero-Cost Immutable Branching & Backtracking**: Every `step(stateId, tactic)` creates a new immutable `stateId` without mutating `stateId`. Agents can explore multiple tactic branches from the same parent state and backtrack instantaneously.
2. **Kernel-Guaranteed Soundness**: No tactic or AI action can bypass the Trusted Kernel. When all goals close, the server reconstructs the explicit De Bruijn proof term, verifies it from scratch through `samurai.kernel.TypeChecker`, and returns `kernelVerified: true` along with `axiomsUsed` and `isAxiomFree`.
3. **Structured Goal Contexts & Suggestions**: Every state response includes typed local hypotheses, raw and NbE-normalized goal types, and ranked `suggestions` with confidence scores.

## Methods

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

### `step` / `batchStep` / `autoSolve` / `getProofTrace`
```json
{"id": 4, "method": "step", "params": {"stateId": 1, "tactic": "intro(n)"}}
```
Apply multiple candidate tactics to a single parent state in one round-trip (beam search / MCTS):
```json
{"id": 5, "method": "batchStep", "params": {"stateId": 1, "tactics": ["refl", "intro(n)"]}}
```
Invoke built-in automated search on a state:
```json
{"id": 6, "method": "autoSolve", "params": {"stateId": 1, "maxDepth": 6}}
```
Reconstruct a clean, pasteable Scala 3 `by { ... }` tactic script from any solved `stateId`:
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
- By keyword:
  ```json
  {"id": 10, "method": "searchLemmas", "params": {"query": "addComm", "limit": 10}}
  ```
- By type unification against a proof state's current goal:
  ```json
  {"id": 11, "method": "searchLemmas", "params": {"stateId": 2, "limit": 10}}
  ```

### `extract`
```json
{"id": 12, "method": "extract", "params": {"target": "scala3", "moduleName": "VerifiedApp", "requireAxiomFree": true}}
```
Supports `"scala3"`, `"ts"`, and `"js"` targets, returning generated code plus a structured `manifest` (`extractedTypes`, `extractedFunctions`, `erasedPropositions`, `verifiedTheorems`, `axiomsUsed`, `isAxiomFree`).
