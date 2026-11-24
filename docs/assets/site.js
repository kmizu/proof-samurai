(() => {
  const CHAPTERS = [
    { num: "01", file: "GETTING_STARTED.md", group: "manual", title: { en: "Getting Started", ja: "はじめに" }, desc: { en: "Setup, Proof Samurai Studio, first definitions, proofs, and extraction.", ja: "環境構築、Studio の起動、最初の定義・証明・コード抽出。" } },
    { num: "02", file: "PROOFS_FOR_PROGRAMMERS.md", group: "manual", title: { en: "Proofs, Tactics & Ordinary Code", ja: "証明・タクティクと通常コードの関係" }, desc: { en: "Side-by-side function vs. tactic proofs, tactic-to-code map, and how proofs connect to runnable programs.", ja: "通常の関数とタクティクの見比べ、タクティク構文対応表、本番コードへの具体的な効き方。" } },
    { num: "03", file: "LANGUAGE.md", group: "manual", title: { en: "Language Reference", ja: "言語リファレンス" }, desc: { en: "Scala 3 brace syntax, enum, case class, mutual, termination_by, partial def, calc, and tactics.", ja: "Scala 3 ブレース構文、enum、case class、mutual、termination_by、partial def、calc、タクティク一覧。" } },
    { num: "04", file: "TACTICS_COOKBOOK.md", group: "manual", title: { en: "Tactic Cookbook", ja: "タクティク・クックブック" }, desc: { en: "Tactic recipes organized by goal shape, programming equivalents, rewriting, cases, and induction.", ja: "ゴールの形・通常コード対応から引くタクティク集、書き換え、ケース分割、帰納法。" } },
    { num: "05", file: "EXTRACTION.md", group: "manual", title: { en: "Verified Code Extraction", ja: "検証済みコード抽出" }, desc: { en: "Prop erasure rules, Scala 3 / TypeScript / JavaScript / Haskell / OCaml output, and --strict / --total gates.", ja: "Prop 消去規則、Scala 3 / TypeScript / JavaScript / Haskell / OCaml 出力、--strict / --total 検証ゲート。" } },
    { num: "06", file: "TROUBLESHOOTING.md", group: "manual", title: { en: "Kernel & Type Error Guide", ja: "カーネル・型エラー解決ガイド" }, desc: { en: "Causes and fixes for K005, K006, K020, K025, K026, K030, K031, T010, and T015.", ja: "K005 / K006 / K020 / K025 / K026 / K030 / K031 / T010 / T015 の原因と修正例。" } },
    { num: "07", file: "KERNEL.md", group: "internals", title: { en: "Trusted Kernel Architecture", ja: "信頼カーネルのアーキテクチャ" }, desc: { en: "Universe stratification, strict positivity, termination, and subsingleton elimination.", ja: "宇宙階層、厳密正性、停止性検査、subsingleton 除去、公理追跡。" } },
    { num: "08", file: "AI_AGENT_GUIDE.md", group: "internals", title: { en: "AI Agent Guide", ja: "AI エージェント連携ガイド" }, desc: { en: "Using the NDJSON server for LLM proof synthesis, MCTS, and CLI verification.", ja: "NDJSON サーバによる LLM 証明合成、木探索、CLI 自動検証ワークフロー。" } },
    { num: "09", file: "AI_PROTOCOL.md", group: "internals", title: { en: "JSON-RPC Protocol Reference", ja: "JSON-RPC プロトコル仕様" }, desc: { en: "Method reference for proveGoal, step, batchStep, inspectHoles, and extract.", ja: "proveGoal / step / batchStep / inspectHoles / extract の仕様一覧。" } }
  ];

  const STDLIB_MODULES = [
    { mod: "stdlib/Prelude.samurai", en: "Core logic (Prop, Eq, And, Or, Not, Exists, Subset, Pair, Bool, Either)", ja: "基本論理（Prop, Eq, And, Or, Not, Exists, Subset, Pair, Bool, Either）" },
    { mod: "stdlib/Nat.samurai", en: "Natural numbers, +, *, -, comparison, commutative semiring & order laws", ja: "自然数、加算・乗算・減算、比較演算、可換半環と順序の諸定理" },
    { mod: "stdlib/List.samurai", en: "Polymorphic lists, append, reverse, map, length, reverseReverse, mapFusion", ja: "多相リスト、append / reverse / map / length、reverseReverse、mapFusion" },
    { mod: "stdlib/Vec.samurai", en: "Length-indexed dependent vectors and total vecHead without Option", ja: "長さ添字付き依存ベクタ、Option 不要の全関数 vecHead" },
    { mod: "stdlib/Tree.samurai", en: "Binary trees, mirror, size, and dual-IH structural induction proofs", ja: "二分木、mirror / size、複数の帰納法仮定を用いる構造的帰納法証明" },
    { mod: "stdlib/Option.samurai", en: "Verified Option functor and monad laws", ja: "Option 型のファンクタ則・モナド則の証明" },
    { mod: "stdlib/Queue.samurai", en: "Amortized two-stack functional queue with FIFO specification proofs", ja: "2 スタック関数型キューと FIFO 仕様の正当性証明" },
    { mod: "stdlib/Sorting.samurai", en: "Insertion sort with Sorted, element-count permutation, and length proofs", ja: "挿入ソートの整列性（Sorted）・多重集合置換・長さ保存の完全証明" },
    { mod: "stdlib/WellFounded.samurai", en: "0-axiom Acc, natWf, strong induction, divNat, modNat, gcd, and quickSort", ja: "公理 0 の Acc・natWf・完全帰納法、整礎再帰の divNat / modNat / gcd / quickSort" }
  ];

  const INDEX_ITEMS = [
    { kind: "tactic", name: "arith / ring", trigger: { en: "Nat equality (+, *, 0, Succ)", ja: "Nat の等式（+, *, 0, Succ）" }, desc: { en: "Proves commutative semiring Nat identities via kernel-checked terms (0 axioms).", ja: "可換半環の恒等式を公理 0 の証明項として一括証明します。" } },
    { kind: "tactic", name: "simp / simp(*)", trigger: { en: "Definitions & @simp rules", ja: "関数定義・@simp 補題" }, desc: { en: "Normalizes with NbE and rewrites with @simp lemmas (and local equalities with *).", ja: "NbE 正規化と @simp 規則（* 指定時は局所等式仮定も含む）で簡約します。" } },
    { kind: "tactic", name: "calc { ... }", trigger: { en: "Multi-step equational chains", ja: "複数段階の等式変形" }, desc: { en: "Readable chain of `=== rhs by { ... }` steps compiled to Eq transitivity.", ja: "`=== rhs by { ... }` の連鎖を推移律のカーネル証明項へ変換します。" } },
    { kind: "tactic", name: "cases(expr, eqHyp)", trigger: { en: "if (cond) / Bool / enum branching", ja: "if (cond) / Bool / enum 分岐" }, desc: { en: "Splits on `expr` while binding `eqHyp : expr === Ctor(...)` in each branch.", ja: "`expr` で分岐し、各分岐に `eqHyp : expr === Ctor(...)` を束縛します。" } },
    { kind: "tactic", name: "induction(x)", trigger: { en: "Recursive proofs on Nat, List, Tree", ja: "Nat / List / Tree に対する帰納法" }, desc: { en: "Performs structural induction with one IH per recursive constructor field.", ja: "構造的帰納法を実行し、再帰フィールドごとに帰納法の仮定を生成します。" } },
    { kind: "tactic", name: "revert(x)", trigger: { en: "Generalizing before induction / cases", ja: "帰納法・cases 前の一般化" }, desc: { en: "Moves a local variable or hypothesis back into the goal as `forall`.", ja: "局所変数や仮定をゴールの `forall` に戻します。" } },
    { kind: "tactic", name: "auto / samurai", trigger: { en: "Propositional logic & equality", ja: "命題論理・基本等式" }, desc: { en: "Bounded proof search producing a kernel-verified proof term.", ja: "有界探索を行い、カーネル検証済みの証明項を合成します。" } },
    { kind: "tactic", name: "decide", trigger: { en: "Concrete arithmetic, lists, Le(m, n)", ja: "具体的な数値・リスト・Le(m, n)" }, desc: { en: "Closes decidable concrete propositions by normalization.", ja: "決定可能な具体的命題を正規化によって閉じます。" } },
    { kind: "tactic", name: "discriminate(h)", trigger: { en: "Conflicting constructors (0 === Succ(n))", ja: "矛盾するコンストラクタ等式" }, desc: { en: "Closes any goal from an impossible constructor equality.", ja: "異なるコンストラクタ同士の等式仮定から任意のゴールを閉じます。" } },
    { kind: "tactic", name: "injection(h, eq)", trigger: { en: "Equal constructors (Succ(a) === Succ(b))", ja: "同一コンストラクタの等式" }, desc: { en: "Extracts argument equality `eq : a === b` into hypotheses.", ja: "引数同士の等式 `eq : a === b` を仮定として取り出します。" } },
    { kind: "error", name: "K020", trigger: { en: "Termination / recursive call", ja: "停止性検査 / 再帰呼び出し" }, desc: { en: "Pass a structurally smaller pattern-matched subterm (e.g. `tail`, not `Cons(h, rest)`).", ja: "再構成した値ではなく、パターンマッチで得た真に小さい部分項（例: `tail`）を渡してください。" } },
    { kind: "error", name: "K006", trigger: { en: "Strict positivity violation", ja: "厳密正性違反" }, desc: { en: "An inductive type cannot appear to the left of `=>` in its own constructor.", ja: "帰納型は自身のコンストラクタ内の `=>` の左辺に現れることができません。" } },
    { kind: "error", name: "K025", trigger: { en: "Prop -> Type elimination", ja: "Prop から Type への除去" }, desc: { en: "Cannot eliminate Or or Exists into Type; use Either or Subset for runtime data.", ja: "Or や Exists は Type へ除去できません。実行時値には Either または Subset を使用してください。" } },
    { kind: "error", name: "K005", trigger: { en: "Universe level exceeded", ja: "宇宙レベル超過" }, desc: { en: "A Type0 inductive cannot store Type0 fields; declare the enum as `: Type1`.", ja: "Type0 の帰納型に Type0 の型は格納できません。`: Type1` を明示してください。" } },
    { kind: "error", name: "K026 / E071", trigger: { en: "Non-exhaustive match", ja: "非網羅的な match" }, desc: { en: "Cover every constructor of the enum or add a `case _ => ...` fallback.", ja: "すべてのコンストラクタを網羅するか、`case _ => ...` を追加してください。" } },
    { kind: "error", name: "K030 / K031", trigger: { en: "partial def in Prop / total caller", ja: "partial def の Prop 返却・全関数からの参照" }, desc: { en: "Keep partial def in Type and isolated from total defs/theorems, or use termination_by.", ja: "partial def は Type 返却かつ全関数・定理から隔離するか、termination_by を使用してください。" } },
    { kind: "error", name: "T010 / T015", trigger: { en: "refl / rewrite failed", ja: "refl / rewrite の失敗" }, desc: { en: "Try `simp`, `arith`, `rewriteRev(...)`, or place `?help` to inspect the goal.", ja: "`simp`、`arith`、`rewriteRev(...)` を試すか、`?help` を置いてゴールを確認してください。" } }
  ];

  const UI_TEXT = {
    en: {
      pageTitle: "Proof Samurai — Documentation",
      searchPlaceholder: "Search documentation, tactics, error codes...",
      sidebarOverviewGroup: "Introduction",
      sidebarOverview: "Overview",
      sidebarManualGroup: "Manual",
      sidebarInternalsGroup: "Internals & AI",
      sidebarReferenceGroup: "Reference",
      sidebarIndex: "Tactic & Error Index",
      sidebarStudioLabel: "Local Web IDE",
      themeLight: "Light",
      themeDark: "Dark",
      copy: "Copy",
      copied: "Copied",
      onThisPage: "On this page",
      prev: "Previous",
      next: "Next",
      loading: "Loading document...",
      loadFailed: "Could not load document",
      searchResults: "Search Results",
      noMatches: (q) => `No matches found for "${q}".`,
      guideTag: "Guide",
      tacticTag: "Tactic",
      errorTag: "Error",
      allTab: "All",
      tacticsTab: "Tactics",
      errorsTab: "Errors",
      indexTitle: "Tactic & Error Index",
      indexLead: "Filter built-in tactics by goal shape or look up kernel and tactic error codes.",
      indexFilterPlaceholder: "Filter by tactic, goal shape, or error code (e.g. arith, cases, K020)...",
      colKind: "Kind",
      colItem: "Item",
      colTrigger: "Goal Shape / Condition",
      colDesc: "Description",
      footerLeft: "Proof Samurai — Scala 3 brace syntax proof assistant",
      footerRight: "Source & issue tracker on GitHub",
      homeSubtitle: "A dependently-typed proof assistant in whitespace-insensitive Scala 3 brace syntax, with a small trusted kernel and proof-erasing extraction to Scala 3, TypeScript, JavaScript, Haskell, and OCaml.",
      homeMeta: "Martin-Löf / CIC kernel · Zero-axiom standard library · Scala 3.8.4 · Zero runtime dependencies",
      homeSwitchLang: "日本語版ドキュメントを表示",
      homeQuickStartTitle: "Quick Start",
      homeQuickStartDesc: "Requires JDK (17+) and sbt. All standard library modules and examples are checked axiom-free.",
      cmdTest: "Run test suite",
      cmdVerify: "Verify all .samurai files (strict)",
      cmdStudio: "Launch Proof Samurai Studio (localhost:8080)",
      homeExampleTitle: "Source and Proof-Erased Extraction",
      homeExampleDesc: "Programs and proofs share Scala 3 brace syntax. Everything in Prop is verified by the kernel and removed completely during extraction.",
      homeDocsTitle: "Documentation",
      colSection: "Section",
      colGuide: "Document",
      colScope: "Scope",
      homeStdlibTitle: "Verified Standard Library",
      homeStdlibDesc: "All modules under stdlib/ pass strict zero-axiom verification on every build.",
      colModule: "Module",
      colSummary: "Contents"
    },
    ja: {
      pageTitle: "Proof Samurai — ドキュメント",
      searchPlaceholder: "ドキュメント・タクティク・エラーコードを検索...",
      sidebarOverviewGroup: "はじめに",
      sidebarOverview: "概要",
      sidebarManualGroup: "マニュアル",
      sidebarInternalsGroup: "内部構造と AI 連携",
      sidebarReferenceGroup: "リファレンス",
      sidebarIndex: "タクティク・エラー索引",
      sidebarStudioLabel: "ローカル Web IDE",
      themeLight: "ライト",
      themeDark: "ダーク",
      copy: "コピー",
      copied: "コピー済",
      onThisPage: "目次",
      prev: "前の章",
      next: "次の章",
      loading: "ドキュメントを読み込み中...",
      loadFailed: "ドキュメントを読み込めませんでした",
      searchResults: "検索結果",
      noMatches: (q) => `「${q}」に一致する項目は見つかりませんでした。`,
      guideTag: "ガイド",
      tacticTag: "タクティク",
      errorTag: "エラー",
      allTab: "すべて",
      tacticsTab: "タクティク",
      errorsTab: "エラー",
      indexTitle: "タクティク・エラー索引",
      indexLead: "ゴールの形からタクティクを引く、またはカーネル／タクティクのエラーコードを検索できます。",
      indexFilterPlaceholder: "タクティク名・ゴール形状・エラーコードで絞り込み（例: arith, cases, K020）...",
      colKind: "種別",
      colItem: "項目",
      colTrigger: "対象ゴール / 発生条件",
      colDesc: "説明",
      footerLeft: "Proof Samurai — Scala 3 ブレース構文による依存型証明支援系",
      footerRight: "ソースコード・Issue は GitHub にて公開",
      homeSubtitle: "インデント非依存の Scala 3 ブレース構文を採用した依存型証明支援系です。小規模な信頼カーネルによる検証と、証明項を完全に消去した Scala 3 / TypeScript / JavaScript / Haskell / OCaml へのコード抽出を提供します。",
      homeMeta: "Martin-Löf / CIC カーネル · 公理 0 の標準ライブラリ · Scala 3.8.4 · 実行時外部依存ゼロ",
      homeSwitchLang: "Switch to English documentation",
      homeQuickStartTitle: "クイックスタート",
      homeQuickStartDesc: "JDK（17 以上推奨）と sbt が必要です。標準ライブラリおよびサンプルはすべて公理 0 で検証されます。",
      cmdTest: "テストスイートの実行",
      cmdVerify: "全 .samurai ファイルの厳密検証（公理 0）",
      cmdStudio: "Proof Samurai Studio の起動 (localhost:8080)",
      homeExampleTitle: "ソースコードと証明消去後の抽出コード",
      homeExampleDesc: "プログラムと証明を同じ Scala 3 ブレース構文で記述します。Prop に属する証明項はカーネル検証後に完全に消去されます。",
      homeDocsTitle: "ドキュメント一覧",
      colSection: "章",
      colGuide: "ドキュメント",
      colScope: "内容",
      homeStdlibTitle: "検証済み標準ライブラリ",
      homeStdlibDesc: "stdlib/ 配下のすべてのモジュールは、ビルドごとに公理 0 の厳密検査を通過しています。",
      colModule: "モジュール",
      colSummary: "主な定義と証明済み性質"
    }
  };

  const SAMPLE_SOURCE = `import Prelude.*
import Nat.*
import List.*

theorem expandBinomial(left: Nat, right: Nat, factor: Nat):
  (left + right) * (factor + 1) ===
    (left * factor + right * factor) + (right + left) = by {
  arith
}

theorem calcLength[Element](a: List[Element], b: List[Element], c: List[Element]):
  length((a ++ b) ++ c) === length(c) + (length(a) + length(b)) = {
  calc {
    length((a ++ b) ++ c)
    === (length(a) + length(b)) + length(c) by { simp }
    === length(c) + (length(a) + length(b)) by { arith }
  }
}`;

  const SAMPLE_EXTRACTED = `// Generated by Proof Samurai (0 axioms used)
object VerifiedSorting {
  enum Subset[Domain] {
    case Mk(value: Domain) // Prop field erased
  }

  def insertionSort(items: List[Nat]): List[Nat] = {
    (items) match {
      case List.Nil() => List.Nil[Nat]()
      case List.Cons(head, tail) => insert(head, insertionSort(tail))
    }
  }

  def sortVerified(items: List[Nat]): Subset[List[Nat]] = {
    Subset.Mk[List[Nat]](insertionSort(items))
  }
}`;

  const docCache = new Map();
  let currentLang = "en";
  let currentPage = "home";
  let indexKindFilter = "all";

  const $ = (id) => document.getElementById(id);

  function t() {
    return UI_TEXT[currentLang] || UI_TEXT.en;
  }

  function escapeHtml(str) {
    return String(str)
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;");
  }

  function docPathFor(file, lang) {
    return lang === "ja" ? `ja/${file}` : file;
  }

  function highlightSamurai(code) {
    const escaped = escapeHtml(code);
    const tokenRe =
      /(\/\/[^\n]*|\/\*[\s\S]*?\*\/)|(\?[A-Za-z_][A-Za-z0-9_']*|\?)|\b(module|import|enum|case|class|def|partial|mutual|termination_by|decreasing_by|val|theorem|lemma|axiom|match|if|else|by|calc|forall|exists|returning|sorry|true|false|object|final)\b|\b(intro|intros|exact|apply|refl|symmetry|trans|rewrite|rewriteRev|congr|induction|cases|revert|exfalso|subst|specialize|split|left|right|contradiction|discriminate|injection|have|unfold|simp|arith|ring|trivial|decide|auto|samurai|assumption)\b|\b(Prop|Type[0-9]*|Nat|Bool|List|Vec|Tree|Option|Queue|Pair|Subset|Eq|Le|Lt|Acc|And|Or|Not|False|True|Unit|Either)\b|\b([0-9]+)\b|(===|!==|=&gt;|->|\/\\|\\\/|::|\+\+)/g;

    return escaped.replace(tokenRe, (m, comment, hole, kw, tactic, ty, num, op) => {
      if (comment) return `<span class="tok-comment">${comment}</span>`;
      if (hole) return `<span class="tok-hole">${hole}</span>`;
      if (kw) return `<span class="tok-kw">${kw}</span>`;
      if (tactic) return `<span class="tok-tactic">${tactic}</span>`;
      if (ty) return `<span class="tok-type">${ty}</span>`;
      if (num) return `<span class="tok-num">${num}</span>`;
      if (op) return `<span class="tok-op">${op}</span>`;
      return m;
    });
  }

  function slugify(text, idx) {
    const base = text
      .toLowerCase()
      .replace(/[^a-z0-9\u3040-\u30ff\u4e00-\u9faf]+/g, "-")
      .replace(/^-|-$/g, "");
    return base ? `sec-${base}-${idx}` : `sec-${idx}`;
  }

  function renderMarkdown(md) {
    const codeBlocks = [];
    const withPlaceholders = md.replace(/```(\w*)\r?\n([\s\S]*?)```/g, (_, lang, code) => {
      const idx = codeBlocks.length;
      codeBlocks.push({ lang, code: code.replace(/\r?\n$/, "") });
      return `\n@@CODEBLOCK_${idx}@@\n`;
    });

    const lines = withPlaceholders.split(/\r?\n/);
    let html = "";
    let listType = null; // "ul" | "ol" | null
    let inTable = false;
    const headings = [];

    const flushList = () => {
      if (listType) {
        html += `</${listType}>`;
        listType = null;
      }
    };
    const flushTable = () => {
      if (inTable) {
        html += "</tbody></table>";
        inTable = false;
      }
    };

    const inlineFmt = (text) =>
      escapeHtml(text)
        .replace(/\[([^\]]+)\]\((https?:\/\/[^)]+)\)/g, '<a href="$2" target="_blank" rel="noopener">$1</a>')
        .replace(/`([^`]+)`/g, "<code>$1</code>")
        .replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>")
        .replace(/\*([^*]+)\*/g, "<em>$1</em>");

    for (const line of lines) {
      const cbMatch = line.trim().match(/^@@CODEBLOCK_(\d+)@@$/);
      if (cbMatch) {
        flushList();
        flushTable();
        const block = codeBlocks[Number(cbMatch[1])];
        const isSamurai = block.lang === "scala" || block.lang === "samurai" || block.lang === "";
        const body = isSamurai ? highlightSamurai(block.code) : escapeHtml(block.code);
        html += `<div class="code-block-wrap"><button class="copy-code-btn" data-copy-code="${encodeURIComponent(block.code)}">${escapeHtml(t().copy)}</button><pre><code>${body}</code></pre></div>`;
        continue;
      }

      if (line.startsWith("|") && line.endsWith("|")) {
        flushList();
        const cells = line.slice(1, -1).split("|").map((c) => c.trim());
        if (cells.every((c) => /^[-:\s]+$/.test(c))) continue;
        if (!inTable) {
          inTable = true;
          html += `<table><thead><tr>${cells.map((c) => `<th>${inlineFmt(c)}</th>`).join("")}</tr></thead><tbody>`;
        } else {
          html += `<tr>${cells.map((c) => `<td>${inlineFmt(c)}</td>`).join("")}</tr>`;
        }
        continue;
      } else {
        flushTable();
      }

      if (line.trim() === "---") {
        flushList();
        html += "<hr />";
      } else if (line.startsWith("### ")) {
        flushList();
        html += `<h3>${inlineFmt(line.slice(4))}</h3>`;
      } else if (line.startsWith("## ")) {
        flushList();
        const rawHeading = line.slice(3).trim();
        const id = slugify(rawHeading, headings.length + 1);
        headings.push({ id, text: rawHeading.replace(/`/g, "") });
        html += `<h2 id="${id}">${inlineFmt(rawHeading)}</h2>`;
      } else if (line.startsWith("# ")) {
        flushList();
        html += `<h1>${inlineFmt(line.slice(2))}</h1>`;
      } else if (line.startsWith("> ")) {
        flushList();
        html += `<blockquote>${inlineFmt(line.slice(2))}</blockquote>`;
      } else if (/^\s*[-*]\s+/.test(line)) {
        if (listType !== "ul") {
          flushList();
          html += "<ul>";
          listType = "ul";
        }
        html += `<li>${inlineFmt(line.replace(/^\s*[-*]\s+/, ""))}</li>`;
      } else if (/^\s*\d+\.\s+/.test(line)) {
        if (listType !== "ol") {
          flushList();
          html += "<ol>";
          listType = "ol";
        }
        html += `<li>${inlineFmt(line.replace(/^\s*\d+\.\s+/, ""))}</li>`;
      } else if (line.trim() === "") {
        flushList();
      } else {
        flushList();
        html += `<p>${inlineFmt(line)}</p>`;
      }
    }

    flushList();
    flushTable();
    return { html, headings };
  }

  async function loadMarkdownFile(file, lang) {
    const path = docPathFor(file, lang);
    if (docCache.has(path)) return docCache.get(path);
    const res = await fetch(path);
    if (!res.ok) throw new Error(`HTTP ${res.status} (${path})`);
    const text = await res.text();
    docCache.set(path, text);
    return text;
  }

  function renderSidebar() {
    const manual = CHAPTERS.filter((c) => c.group === "manual");
    const internals = CHAPTERS.filter((c) => c.group === "internals");
    const ui = t();

    const chapterBtn = (c) =>
      `<button class="nav-item${currentPage === c.file ? " active" : ""}" data-page="${c.file}">
        <span class="nav-num">${c.num}</span>
        <span>${escapeHtml(c.title[currentLang])}</span>
      </button>`;

    $("sidebar-nav").innerHTML = `
      <div class="sidebar-group">
        <div class="sidebar-heading">${escapeHtml(ui.sidebarOverviewGroup)}</div>
        <button class="nav-item${currentPage === "home" ? " active" : ""}" data-page="home">
          <span>${escapeHtml(ui.sidebarOverview)}</span>
        </button>
      </div>
      <div class="sidebar-group">
        <div class="sidebar-heading">${escapeHtml(ui.sidebarManualGroup)}</div>
        ${manual.map(chapterBtn).join("")}
      </div>
      <div class="sidebar-group">
        <div class="sidebar-heading">${escapeHtml(ui.sidebarInternalsGroup)}</div>
        ${internals.map(chapterBtn).join("")}
      </div>
      <div class="sidebar-group">
        <div class="sidebar-heading">${escapeHtml(ui.sidebarReferenceGroup)}</div>
        <button class="nav-item${currentPage === "index" ? " active" : ""}" data-page="index">
          <span>${escapeHtml(ui.sidebarIndex)}</span>
        </button>
      </div>
    `;

    $("sidebar-nav").querySelectorAll("[data-page]").forEach((btn) => {
      btn.addEventListener("click", () => {
        $("sidebar").classList.remove("open");
        navigate(btn.dataset.page);
      });
    });

    document.querySelectorAll("[data-i18n='sidebarStudioLabel']").forEach((el) => {
      el.textContent = ui.sidebarStudioLabel;
    });
  }

  function renderHome() {
    const ui = t();
    const otherLang = currentLang === "en" ? "ja" : "en";

    const docRows = CHAPTERS.map(
      (c) => `<tr class="clickable-row" data-goto="${c.file}">
        <td style="width:64px"><code>${c.num}</code></td>
        <td style="width:240px"><span class="chapter-link">${escapeHtml(c.title[currentLang])}</span></td>
        <td>${escapeHtml(c.desc[currentLang])}</td>
      </tr>`
    ).join("");

    const stdlibRows = STDLIB_MODULES.map(
      (m) => `<tr>
        <td style="width:230px"><code>${escapeHtml(m.mod)}</code></td>
        <td>${escapeHtml(m[currentLang])}</td>
      </tr>`
    ).join("");

    $("home-container").innerHTML = `
      <div class="doc-intro">
        <h1>Proof Samurai</h1>
        <p class="doc-subtitle">${escapeHtml(ui.homeSubtitle)}</p>
        <div class="doc-meta-line">
          <span>${escapeHtml(ui.homeMeta)}</span>
          <span>·</span>
          <button class="inline-action-link" id="home-lang-link">${escapeHtml(ui.homeSwitchLang)}</button>
        </div>
      </div>

      <section class="section-block">
        <h2>${escapeHtml(ui.homeQuickStartTitle)}</h2>
        <p>${escapeHtml(ui.homeQuickStartDesc)}</p>
        <div class="cmd-list">
          <div class="cmd-box">
            <div class="cmd-box-head">
              <span>${escapeHtml(ui.cmdTest)}</span>
              <button class="copy-btn" data-copy="sbt test">${escapeHtml(ui.copy)}</button>
            </div>
            <code>sbt test</code>
          </div>
          <div class="cmd-box">
            <div class="cmd-box-head">
              <span>${escapeHtml(ui.cmdVerify)}</span>
              <button class="copy-btn" data-copy='sbt "run verify-project . --strict"'>${escapeHtml(ui.copy)}</button>
            </div>
            <code>sbt "run verify-project . --strict"</code>
          </div>
          <div class="cmd-box">
            <div class="cmd-box-head">
              <span>${escapeHtml(ui.cmdStudio)}</span>
              <button class="copy-btn" data-copy='sbt "run studio"'>${escapeHtml(ui.copy)}</button>
            </div>
            <code>sbt "run studio"</code>
          </div>
        </div>
      </section>

      <section class="section-block">
        <h2>${escapeHtml(ui.homeExampleTitle)}</h2>
        <p>${escapeHtml(ui.homeExampleDesc)}</p>
        <div class="code-pair">
          <div class="code-panel">
            <div class="code-panel-bar">
              <span>examples/Showcase.samurai</span>
              <button class="copy-btn" data-copy-code="${encodeURIComponent(SAMPLE_SOURCE)}">${escapeHtml(ui.copy)}</button>
            </div>
            <pre><code>${highlightSamurai(SAMPLE_SOURCE)}</code></pre>
          </div>
          <div class="code-panel">
            <div class="code-panel-bar">
              <span>VerifiedSorting.scala</span>
              <button class="copy-btn" data-copy-code="${encodeURIComponent(SAMPLE_EXTRACTED)}">${escapeHtml(ui.copy)}</button>
            </div>
            <pre><code>${highlightSamurai(SAMPLE_EXTRACTED)}</code></pre>
          </div>
        </div>
      </section>

      <section class="section-block">
        <h2>${escapeHtml(ui.homeDocsTitle)}</h2>
        <table>
          <thead>
            <tr>
              <th>${escapeHtml(ui.colSection)}</th>
              <th>${escapeHtml(ui.colGuide)}</th>
              <th>${escapeHtml(ui.colScope)}</th>
            </tr>
          </thead>
          <tbody>${docRows}</tbody>
        </table>
      </section>

      <section class="section-block">
        <h2>${escapeHtml(ui.homeStdlibTitle)}</h2>
        <p>${escapeHtml(ui.homeStdlibDesc)}</p>
        <table>
          <thead>
            <tr>
              <th>${escapeHtml(ui.colModule)}</th>
              <th>${escapeHtml(ui.colSummary)}</th>
            </tr>
          </thead>
          <tbody>${stdlibRows}</tbody>
        </table>
      </section>
    `;

    $("home-lang-link").addEventListener("click", () => setLanguage(otherLang));
    $("home-container").querySelectorAll("[data-goto]").forEach((el) => {
      el.addEventListener("click", () => navigate(el.dataset.goto));
    });
    wireCopyButtons($("home-container"));
  }

  function renderIndex() {
    const ui = t();
    $("index-header").innerHTML = `
      <h1 style="margin:0 0 8px;font-size:27px;border-bottom:1px solid var(--border);padding-bottom:10px">${escapeHtml(ui.indexTitle)}</h1>
      <p class="muted-note" style="margin:0">${escapeHtml(ui.indexLead)}</p>
    `;
    $("index-filter").placeholder = ui.indexFilterPlaceholder;

    $("index-kind-tabs").innerHTML = [
      { id: "all", label: ui.allTab },
      { id: "tactic", label: ui.tacticsTab },
      { id: "error", label: ui.errorsTab }
    ]
      .map((tab) => `<button class="filter-tab${indexKindFilter === tab.id ? " active" : ""}" data-kind="${tab.id}">${escapeHtml(tab.label)}</button>`)
      .join("");

    $("index-kind-tabs").querySelectorAll("[data-kind]").forEach((btn) => {
      btn.addEventListener("click", () => {
        indexKindFilter = btn.dataset.kind;
        renderIndex();
      });
    });

    const q = ($("index-filter").value || "").toLowerCase().trim();
    const rows = INDEX_ITEMS.filter((item) => {
      if (indexKindFilter !== "all" && item.kind !== indexKindFilter) return false;
      if (!q) return true;
      return (
        item.name.toLowerCase().includes(q) ||
        item.trigger[currentLang].toLowerCase().includes(q) ||
        item.desc[currentLang].toLowerCase().includes(q) ||
        item.trigger.en.toLowerCase().includes(q)
      );
    });

    if (rows.length === 0) {
      $("index-table-wrap").innerHTML = `<p class="muted-note">${escapeHtml(ui.noMatches(q))}</p>`;
      return;
    }

    $("index-table-wrap").innerHTML = `
      <table>
        <thead>
          <tr>
            <th style="width:90px">${escapeHtml(ui.colKind)}</th>
            <th style="width:170px">${escapeHtml(ui.colItem)}</th>
            <th style="width:230px">${escapeHtml(ui.colTrigger)}</th>
            <th>${escapeHtml(ui.colDesc)}</th>
          </tr>
        </thead>
        <tbody>
          ${rows
            .map(
              (item) => `<tr>
                <td><span class="kind-label">${escapeHtml(item.kind === "tactic" ? ui.tacticTag : ui.errorTag)}</span></td>
                <td><code>${escapeHtml(item.name)}</code></td>
                <td>${escapeHtml(item.trigger[currentLang])}</td>
                <td>${escapeHtml(item.desc[currentLang])}</td>
              </tr>`
            )
            .join("")}
        </tbody>
      </table>
    `;
  }

  function wireCopyButtons(root) {
    root.querySelectorAll("[data-copy-code]").forEach((btn) => {
      btn.addEventListener("click", () => {
        navigator.clipboard?.writeText(decodeURIComponent(btn.dataset.copyCode));
        btn.textContent = t().copied;
        setTimeout(() => (btn.textContent = t().copy), 1200);
      });
    });
    root.querySelectorAll("[data-copy]").forEach((btn) => {
      btn.addEventListener("click", () => {
        navigator.clipboard?.writeText(btn.dataset.copy);
        btn.textContent = t().copied;
        setTimeout(() => (btn.textContent = t().copy), 1200);
      });
    });
  }

  function showPageSection(sectionId) {
    document.querySelectorAll(".page").forEach((p) => p.classList.remove("active"));
    $(sectionId).classList.add("active");
    window.scrollTo({ top: 0 });
  }

  function updateHash() {
    const target = `${currentLang}/${currentPage}`;
    if (window.location.hash !== `#${target}`) {
      history.replaceState(null, "", `#${target}`);
    }
  }

  async function navigate(pageId) {
    currentPage = pageId === "finder" ? "index" : pageId || "home";
    updateHash();
    renderSidebar();

    if (currentPage === "home") {
      renderHome();
      showPageSection("page-home");
      return;
    }

    if (currentPage === "index") {
      renderIndex();
      showPageSection("page-index");
      return;
    }

    const chapter = CHAPTERS.find((c) => c.file === currentPage);
    showPageSection("page-markdown");
    $("article-breadcrumb").textContent = chapter
      ? `${chapter.num} / ${chapter.title[currentLang]}`
      : currentPage;
    $("markdown-container").innerHTML = `<p class="muted-note">${escapeHtml(t().loading)}</p>`;
    $("article-toc").innerHTML = "";
    $("chapter-nav").innerHTML = "";

    try {
      const md = await loadMarkdownFile(currentPage, currentLang);
      const { html, headings } = renderMarkdown(md);
      $("markdown-container").innerHTML = html;
      wireCopyButtons($("markdown-container"));

      if (headings.length > 0) {
        $("article-toc").innerHTML = `
          <div class="toc-title">${escapeHtml(t().onThisPage)}</div>
          <ul class="toc-list">
            ${headings.map((h) => `<li><a href="#${h.id}" data-scroll-to="${h.id}">${escapeHtml(h.text)}</a></li>`).join("")}
          </ul>
        `;
        $("article-toc").querySelectorAll("[data-scroll-to]").forEach((link) => {
          link.addEventListener("click", (e) => {
            e.preventDefault();
            const target = $(link.dataset.scrollTo);
            if (target) target.scrollIntoView({ behavior: "smooth", block: "start" });
          });
        });
      }

      const idx = CHAPTERS.findIndex((c) => c.file === currentPage);
      const prev = idx > 0 ? CHAPTERS[idx - 1] : null;
      const next = idx >= 0 && idx < CHAPTERS.length - 1 ? CHAPTERS[idx + 1] : null;
      $("chapter-nav").innerHTML = `
        <div>${
          prev
            ? `<button class="chapter-btn" data-goto="${prev.file}"><span class="chapter-btn-dir">${escapeHtml(t().prev)}</span>${prev.num} ${escapeHtml(prev.title[currentLang])}</button>`
            : ""
        }</div>
        <div>${
          next
            ? `<button class="chapter-btn" data-goto="${next.file}"><span class="chapter-btn-dir">${escapeHtml(t().next)}</span>${next.num} ${escapeHtml(next.title[currentLang])}</button>`
            : ""
        }</div>
      `;
      $("chapter-nav").querySelectorAll("[data-goto]").forEach((btn) => {
        btn.addEventListener("click", () => navigate(btn.dataset.goto));
      });
    } catch (err) {
      $("markdown-container").innerHTML = `<p>${escapeHtml(t().loadFailed)}: <code>${escapeHtml(docPathFor(currentPage, currentLang))}</code> (${escapeHtml(String(err))})</p>`;
    }
  }

  async function runGlobalSearch(query) {
    const q = (query || "").toLowerCase().trim();
    if (!q) {
      navigate(currentPage || "home");
      return;
    }
    const ui = t();
    $("search-heading").textContent = `${ui.searchResults}: "${query.trim()}"`;
    showPageSection("page-search");
    const items = [];

    for (const item of INDEX_ITEMS) {
      if (
        item.name.toLowerCase().includes(q) ||
        item.trigger[currentLang].toLowerCase().includes(q) ||
        item.desc[currentLang].toLowerCase().includes(q) ||
        item.trigger.en.toLowerCase().includes(q)
      ) {
        items.push(`<div class="search-item">
          <div class="search-item-head">
            <code>${escapeHtml(item.name)}</code>
            <span class="kind-label">${escapeHtml(item.kind === "tactic" ? ui.tacticTag : ui.errorTag)}</span>
          </div>
          <div style="font-size:13px;font-weight:600">${escapeHtml(item.trigger[currentLang])}</div>
          <p>${escapeHtml(item.desc[currentLang])}</p>
        </div>`);
      }
    }

    for (const ch of CHAPTERS) {
      try {
        const md = await loadMarkdownFile(ch.file, currentLang);
        const pos = md.toLowerCase().indexOf(q);
        if (pos >= 0) {
          const snippet = md
            .slice(Math.max(0, pos - 40), Math.min(md.length, pos + 140))
            .replace(/\s+/g, " ");
          items.push(`<div class="search-item clickable" data-goto="${ch.file}">
            <div class="search-item-head">
              <strong>${ch.num} ${escapeHtml(ch.title[currentLang])}</strong>
              <span class="kind-label">${escapeHtml(ui.guideTag)}</span>
            </div>
            <p>...${escapeHtml(snippet)}...</p>
          </div>`);
        }
      } catch (_) {}
    }

    $("search-results").innerHTML =
      items.length > 0
        ? `<div class="search-list">${items.join("")}</div>`
        : `<p class="muted-note">${escapeHtml(ui.noMatches(query.trim()))}</p>`;

    $("search-results").querySelectorAll("[data-goto]").forEach((el) => {
      el.addEventListener("click", () => {
        $("doc-search").value = "";
        navigate(el.dataset.goto);
      });
    });
  }

  function applyChromeText() {
    const ui = t();
    document.documentElement.lang = currentLang;
    document.title = ui.pageTitle;
    $("doc-search").placeholder = ui.searchPlaceholder;
    $("brand-link").href = `#${currentLang}/home`;

    document.querySelectorAll(".lang-btn").forEach((btn) => {
      const active = btn.dataset.lang === currentLang;
      btn.classList.toggle("active", active);
      btn.setAttribute("aria-pressed", String(active));
    });

    const theme = document.documentElement.dataset.theme || "light";
    $("theme-toggle").textContent = theme === "dark" ? ui.themeLight : ui.themeDark;

    $("site-footer").innerHTML = `
      <span>${escapeHtml(ui.footerLeft)}</span>
      <a href="https://github.com/kmizu/proof-samurai" target="_blank" rel="noopener">${escapeHtml(ui.footerRight)}</a>
    `;
  }

  function setLanguage(lang) {
    currentLang = lang === "ja" ? "ja" : "en";
    try {
      localStorage.setItem("proof-samurai-lang", currentLang);
    } catch (_) {}
    applyChromeText();
    navigate(currentPage);
  }

  function setTheme(theme) {
    const next = theme === "dark" ? "dark" : "light";
    document.documentElement.dataset.theme = next;
    try {
      localStorage.setItem("proof-samurai-theme", next);
    } catch (_) {}
    applyChromeText();
  }

  function parseInitialRoute() {
    const raw = window.location.hash.replace(/^#/, "");
    let savedLang = null;
    try {
      savedLang = localStorage.getItem("proof-samurai-lang");
    } catch (_) {}

    if (raw.startsWith("ja/")) {
      return { lang: "ja", page: raw.slice(3) || "home" };
    }
    if (raw.startsWith("en/")) {
      return { lang: "en", page: raw.slice(3) || "home" };
    }
    if (raw === "ja" || raw === "en") {
      return { lang: raw, page: "home" };
    }
    const defaultLang =
      savedLang === "ja" || savedLang === "en"
        ? savedLang
        : (navigator.language || "").toLowerCase().startsWith("ja")
        ? "ja"
        : "en";
    return { lang: defaultLang, page: raw || "home" };
  }

  function init() {
    let savedTheme = "light";
    try {
      savedTheme = localStorage.getItem("proof-samurai-theme") || "light";
    } catch (_) {}
    document.documentElement.dataset.theme = savedTheme === "dark" ? "dark" : "light";

    const route = parseInitialRoute();
    currentLang = route.lang;
    currentPage = route.page;

    document.querySelectorAll(".lang-btn").forEach((btn) => {
      btn.addEventListener("click", () => setLanguage(btn.dataset.lang));
    });

    $("theme-toggle").addEventListener("click", () => {
      const cur = document.documentElement.dataset.theme || "light";
      setTheme(cur === "dark" ? "light" : "dark");
    });

    $("brand-link").addEventListener("click", (e) => {
      e.preventDefault();
      navigate("home");
    });

    $("mobile-menu-btn").addEventListener("click", () => {
      const open = $("sidebar").classList.toggle("open");
      $("mobile-menu-btn").setAttribute("aria-expanded", String(open));
    });

    $("index-filter").addEventListener("input", () => renderIndex());

    let searchTimer = null;
    $("doc-search").addEventListener("input", (e) => {
      clearTimeout(searchTimer);
      searchTimer = setTimeout(() => runGlobalSearch(e.target.value), 180);
    });

    window.addEventListener("hashchange", () => {
      const next = parseInitialRoute();
      if (next.lang !== currentLang) {
        currentLang = next.lang;
        applyChromeText();
      }
      if (next.page !== currentPage) {
        navigate(next.page);
      }
    });

    applyChromeText();
    navigate(currentPage);
  }

  init();
})();
