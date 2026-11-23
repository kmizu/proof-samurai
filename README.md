# ⚔ Proof Samurai (`proof-samurai`)

**Pragmatic, readable, AI-friendly dependently-typed proof assistant in Scala 3 brace syntax — with sound code extraction to Scala 3, TypeScript, and JavaScript.**

- 📖 **Kindful Docs (GitHub Pages)**: https://kmizu.github.io/proof-samurai/
- 🖥️ **Interactive Web IDE**: `sbt "run studio"` → http://localhost:8080
- 🛡 **100% Axiom-Free Standard Library**: 12 verified `.samurai` modules & examples checked on every build

---

## Why Proof Samurai?

- **Programmer-Friendly Scala 3 Brace Syntax (Zero Indentation Sensitivity)**
  Familiar `enum`, `case class`, `def`, `val`, `theorem`, `[1, 2, 3]` list literals, `match { case ... => ... }`, `if (...) { ... } else { ... }`, `calc { ... }` equational proofs, dot projections (`pair.first`), UFCS (`items.length`), and `by { ... }` tactic blocks. Every block uses explicit `{ ... }` braces.
- **Small, Auditable Trusted Kernel (`samurai.kernel`)**
  - De Bruijn–indexed Martin-Löf / CIC core enforcing the **de Bruijn criterion** (elaborator, tactics, `arith`, `auto`, and AI search are all untrusted and re-checked from scratch by the kernel)
  - Stratified universe hierarchy (`Prop : Type0 : Type1 : ...`, preventing Girard's paradox)
  - NbE-normalized strict positivity checker (preventing Curry's paradox)
  - Structural decreasing recursion guard checker (preventing `def loop: False = loop`)
  - Subsingleton `Prop` elimination & definitional proof irrelevance (`False` and `Eq` into `Type`; `Or` and `Exists` blocked)
  - Transitive axiom & `sorry` tracking (`--strict` enforces 0 axioms)
- **Zero-Overhead Verified Code Extraction (`samurai.extract`)**
  - Soundly erases all `Prop` types, theorems, `Subset` proof fields, and unreachable indexed match branches (`Vec.Nil` in `vecHead`)
  - Emits standalone, runnable **Scala 3 (brace syntax)**, **TypeScript**, and **JavaScript (ES module)** with a JSON `ExtractionManifest`
- **Built for Both Humans and AI Agents (`samurai.ui`, `samurai.ai`)**
  - **Proof Samurai Studio** (`sbt "run studio"`): Live syntax-highlighted editor, kernel Infoview, 1-click `?hole` tactic suggestions, visual branching **Interactive Proof Tree**, live Code Extractor, and interactive Docs Hub
  - **AI-Native NDJSON Server** (`sbt "run serve"`): Low-token folded goals, zero-cost immutable branching/backtracking (`stateId`), `proveGoal`, `batchStep`, `inspectHoles`, `listSymbols`, and `getProofTrace`

---

## Quick Start

### 1. Launch Proof Samurai Studio (Web IDE)
```bash
sbt "run studio"
```
Then open **http://localhost:8080** in your browser.

### 2. Run the Full Verification Test Suite
```bash
sbt test
```

### 3. CLI Commands
```bash
# Verify every .samurai file in the repository (100% axiom-free strict mode)
sbt "run verify-project . --strict"

# Check and evaluate a file
sbt "run check examples/Showcase.samurai --strict"

# Inspect all open ?holes with folded goals and AI tactic suggestions
sbt "run goals draft.samurai --json"

# Search verified definitions and theorems
sbt "run search stdlib/Sorting.samurai sort"

# Extract verified Insertion Sort to Scala 3, TypeScript, or JavaScript
sbt "run extract stdlib/Sorting.samurai --target scala3 --module VerifiedSorting --strict"
sbt "run extract stdlib/Sorting.samurai --target ts --strict"
sbt "run extract stdlib/Sorting.samurai --target js --strict"

# Start the interactive multi-line human REPL or AI JSON-RPC server
sbt "run repl"
sbt "run serve"
```

---

## Kindful Documentation (Published on GitHub Pages)

Browse interactively at **https://kmizu.github.io/proof-samurai/** or read locally in `docs/`:

- [Getting Started (10-Minute Tour)](docs/GETTING_STARTED.md) — Gentle introduction for Scala & FP programmers
- [Scala 3 Brace Language Guide](docs/LANGUAGE.md) — Syntax, operators, `calc`, and tactics reference
- [Friendly Tactic Cookbook](docs/TACTICS_COOKBOOK.md) — Recipes organized by *"What does my goal look like?"*
- [Verified Code Extraction](docs/EXTRACTION.md) — Proof erasure rules & Scala 3 / TS / JS targets
- [Kindful Error & Soundness Guide](docs/TROUBLESHOOTING.md) — Plain-English explanations & Before/After fixes for kernel errors (`K005`, `K006`, `K020`, `K025`, `T010`, `T015`)
- [Trusted Kernel Architecture](docs/KERNEL.md) — Deep dive into the Trusted Computing Base
- [AI Agent Playbook](docs/AI_AGENT_GUIDE.md) & [JSON-RPC Protocol Reference](docs/AI_PROTOCOL.md) — Building LLM & MCTS provers

---

## Project Structure

- `src/main/scala/samurai/kernel/` — Small Trusted Computing Base (`Term`, `Env`, `NbE`, `Positivity`, `Termination`, `TypeChecker`, `Pretty`)
- `src/main/scala/samurai/syntax/` — Whitespace-insensitive Scala 3 brace lexer, AST, and parser
- `src/main/scala/samurai/elab/` — Bidirectional elaborator, metavariable unification, decision-tree pattern matrix compiler, `calc` elaboration
- `src/main/scala/samurai/tactic/` — LCF-style tactics, proof-producing `ArithTactic` (`arith`/`ring`), automated `ProofSearch` (`auto`, `suggest`)
- `src/main/scala/samurai/extract/` — Sound `Prop`/type erasure IR and code emitters (`Scala3Emitter`, `TsEmitter`, `JsEmitter`)
- `src/main/scala/samurai/ui/` & `src/main/resources/studio/` — Proof Samurai Studio embedded HTTP server & Web IDE
- `src/main/scala/samurai/ai/` — Branching NDJSON proof server (`ProofSessionServer`) and multi-line human `Repl`
- `stdlib/` — 100% axiom-free verified standard library (`Prelude`, `Nat`, `List`, `Vec`, `Tree`, `Option`, `Queue`, `Sorting`)
- `examples/` — Runnable examples (`HelloProof`, `VerifiedSort`, `SafeVec`, `Showcase`)
- `docs/` — Kindful documentation & static GitHub Pages site
