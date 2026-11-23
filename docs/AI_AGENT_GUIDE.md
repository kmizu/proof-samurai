# AI Agent & Automated Prover Guide

Proof Samurai is engineered from day one to be an **AI-native theorem prover** — compact token usage, zero-cost immutable branching/backtracking, structured diagnostics, and a small Trusted Kernel that guarantees no hallucinated proof can ever be accepted.

## Why AI Agents Excel with Proof Samurai

1. **Low-Token Folded Goals**: Stuck recursive functions (`add`, `append`, `insertionSort`) render cleanly as `a + b`, `xs ++ ys`, and `[0, 1, 2]` — never dumping raw 2,000-character `fix` ASTs into an LLM context window.
2. **Zero-Cost Branching & Backtracking**: Every `step(stateId, tactic)` returns a new immutable `stateId` without mutating the parent, ideal for MCTS, beam search, and LLM tree-of-thought.
3. **One-Shot Refinement (`proveGoal`)**: Test a complete candidate tactic script in one round-trip and receive either `kernelVerified: true` OR the exact `failedAtStep`, `goalShape`, folded `remainingGoals`, and ranked `suggestions`.
4. **Whole-File Hole Inspection (`inspectHoles` / `samurai goals --json`)**: Write proof skeletons with `?hole1`, `?hole2` and inspect every hole in the entire file in one pass.
5. **Symbol Grounding (`listSymbols`)**: Query exact inductive constructors, function types, and `@simp` lemmas before generating tactics.

## Recommended LLM Agent Workflow

### Step 1: Start the NDJSON Server
```bash
sbt "run serve"
```
Send one JSON object per line on `stdin`; read one JSON object per line from `stdout`.

### Step 2: Load Context & Ground Symbols
```json
{"id": 1, "method": "loadFile", "params": {"path": "stdlib/List.samurai"}}
{"id": 2, "method": "listSymbols"}
```

### Step 3: Fast One-Shot Proof Verification (`proveGoal`)
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
Response:
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

### Step 4: Beam Search / MCTS with `batchStep` & `getProofTrace`
1. `startProof` → returns root `stateId` + initial `suggestions`.
2. `batchStep` → evaluate multiple candidate tactics on `stateId` in a single round-trip:
   ```json
   {"id": 4, "method": "batchStep", "params": {"stateId": 1, "tactics": ["refl", "intro(n)", "auto(5)"]}}
   ```
3. `getProofTrace` → once a leaf `stateId` reaches `isSolved: true`, extract a clean, pasteable Scala 3 `by { ... }` block:
   ```json
   {"id": 5, "method": "getProofTrace", "params": {"stateId": 7}}
   ```

### Step 5: Verified Code Extraction Gate
```json
{"id": 6, "method": "extract", "params": {"target": "scala3", "moduleName": "VerifiedApp", "requireAxiomFree": true}}
```

## CLI `--json` Commands for Shell-Based Agents
```bash
sbt "run check examples/Showcase.samurai --strict --json"
sbt "run goals draft.samurai --json"
sbt "run search stdlib/Sorting.samurai sort --json"
sbt "run verify-project . --strict --json"
```
