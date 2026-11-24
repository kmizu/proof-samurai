# <img src="docs/favicon.svg" alt="" width="28" height="28" align="absmiddle" /> Proof Samurai (`proof-samurai`)

[English](README.md) | [日本語](README.ja.md) | [Documentation (GitHub Pages)](https://kmizu.github.io/proof-samurai/)

A dependently-typed proof assistant in whitespace-insensitive Scala 3 brace syntax, with a small trusted kernel and sound proof-erasing code extraction to Scala 3, TypeScript, and JavaScript.

---

## Overview

- **Scala 3 Brace Syntax (Whitespace-Insensitive)**
  `enum`, `case class`, `def`, `mutual`, `termination_by` / `decreasing_by`, isolated `partial def`, `val`, `theorem`, `[1, 2, 3]` list literals, `match { case ... => ... }`, `if (...) { ... } else { ... }`, `calc { ... }` equational reasoning, dot projections (`pair.first`), UFCS (`items.length`), and `by { ... }` tactic blocks. Every block uses explicit `{ ... }` braces.
- **Small Trusted Kernel (`samurai.kernel`)**
  - De Bruijn-indexed Martin-Löf / CIC core following the de Bruijn criterion (elaborator, tactics, `arith`, `auto`, and AI sessions are untrusted and re-checked from scratch by the kernel)
  - Stratified universe hierarchy (`Prop : Type0 : Type1 : ...`)
  - NbE-normalized strict positivity checker
  - Structural decreasing & mutual recursion termination checker, 0-axiom `Acc`-based well-founded recursion (`termination_by`), and sound kernel isolation for `partial def` (`K030` / `K031`)
  - Subsingleton & index-forced `Prop` elimination and definitional proof irrelevance (`False`, `Eq`, and `Acc` into `Type`; `Or` and `Exists` rejected)
  - Transitive axiom and `sorry` tracking (`--strict` enforces zero axioms; `--total` enforces zero `partial def`)
- **Verified Code Extraction (`samurai.extract`)**
  - Soundly erases `Prop` types, theorems, `Subset` proof fields, and provably unreachable indexed branches (`Vec.Nil` in `vecHead`)
  - Emits standalone Scala 3 (brace syntax), TypeScript, and JavaScript (ES module) along with a JSON `ExtractionManifest`
- **Local Web IDE & AI Proof Server (`samurai.ui`, `samurai.ai`)**
  - **Proof Samurai Studio** (`sbt "run studio"`): local Web IDE with live kernel infoview, `?hole` inspection, branching Interactive Proof Tree, code extractor, and bilingual docs
  - **NDJSON Proof Server** (`sbt "run serve"`): low-token folded goals, immutable branching/backtracking (`stateId`), `proveGoal`, `batchStep`, `inspectHoles`, `listSymbols`, and `getProofTrace`

---

## Quick Start

```bash
# Run the test suite
sbt test

# Verify every .samurai file in the repository (zero axioms)
sbt "run verify-project . --strict"

# Launch the local Web IDE at http://localhost:8080
sbt "run studio"
```

### Additional CLI Commands

```bash
# Check and evaluate a file
sbt "run check examples/Showcase.samurai --strict"

# Inspect open ?holes with folded goals and tactic suggestions
sbt "run goals draft.samurai --json"

# Search verified definitions and theorems
sbt "run search stdlib/Sorting.samurai sort"

# Extract verified Insertion Sort to Scala 3, TypeScript, or JavaScript
sbt "run extract stdlib/Sorting.samurai --target scala3 --module VerifiedSorting --strict"
sbt "run extract stdlib/Sorting.samurai --target ts --strict"
sbt "run extract stdlib/Sorting.samurai --target js --strict"

# Interactive REPL or NDJSON proof server
sbt "run repl"
sbt "run serve"
```

---

## Documentation

Browse online (English / 日本語) at https://kmizu.github.io/proof-samurai/ or read directly under `docs/` (`docs/ja/` for Japanese):

- [Getting Started](docs/GETTING_STARTED.md) / [はじめに](docs/ja/GETTING_STARTED.md)
- [Proofs, Tactics & Ordinary Code](docs/PROOFS_FOR_PROGRAMMERS.md) / [証明・タクティクと通常コードの関係](docs/ja/PROOFS_FOR_PROGRAMMERS.md)
- [Language Reference](docs/LANGUAGE.md) / [言語リファレンス](docs/ja/LANGUAGE.md)
- [Tactic Cookbook](docs/TACTICS_COOKBOOK.md) / [タクティク・クックブック](docs/ja/TACTICS_COOKBOOK.md)
- [Verified Code Extraction](docs/EXTRACTION.md) / [検証済みコード抽出](docs/ja/EXTRACTION.md)
- [Kernel & Type Error Guide](docs/TROUBLESHOOTING.md) / [カーネル・型エラー解決ガイド](docs/ja/TROUBLESHOOTING.md)
- [Trusted Kernel Architecture](docs/KERNEL.md) / [信頼カーネルのアーキテクチャ](docs/ja/KERNEL.md)
- [AI Agent Guide](docs/AI_AGENT_GUIDE.md) / [AI エージェント連携ガイド](docs/ja/AI_AGENT_GUIDE.md)
- [JSON-RPC Protocol Reference](docs/AI_PROTOCOL.md) / [JSON-RPC プロトコル仕様](docs/ja/AI_PROTOCOL.md)

---

## Project Structure

- `src/main/scala/samurai/kernel/` — Trusted Computing Base (`Term`, `Env`, `NbE`, `Positivity`, `Termination`, `TypeChecker`, `Pretty`)
- `src/main/scala/samurai/syntax/` — Whitespace-insensitive Scala 3 brace lexer, AST, and parser
- `src/main/scala/samurai/elab/` — Bidirectional elaborator, metavariable unification, pattern matrix compiler, `calc` & `termination_by` elaboration
- `src/main/scala/samurai/tactic/` — LCF-style tactics, proof-producing `ArithTactic` (`arith` / `ring`), `ProofSearch` (`auto`, `suggest`)
- `src/main/scala/samurai/extract/` — `Prop`/type erasure IR and code emitters (`Scala3Emitter`, `TsEmitter`, `JsEmitter`)
- `src/main/scala/samurai/ui/` & `src/main/resources/studio/` — Embedded HTTP server and Proof Samurai Studio Web IDE
- `src/main/scala/samurai/ai/` — Branching NDJSON proof server (`ProofSessionServer`) and multi-line REPL
- `stdlib/` — Zero-axiom verified standard library (`Prelude`, `Nat`, `List`, `Vec`, `Tree`, `Option`, `Queue`, `Sorting`, `WellFounded`)
- `examples/` — Runnable examples (`HelloProof`, `VerifiedSort`, `SafeVec`, `Showcase`, `AdvancedRecursion`)
- `docs/` — English and Japanese (`docs/ja/`) documentation and GitHub Pages site
