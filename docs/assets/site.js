(() => {
  const CHAPTERS = [
    { file: "GETTING_STARTED.md", title: "10-Minute Tutorial" },
    { file: "LANGUAGE.md", title: "Scala 3 Brace Syntax" },
    { file: "TACTICS_COOKBOOK.md", title: "Friendly Tactic Cookbook" },
    { file: "EXTRACTION.md", title: "Verified Code Extraction" },
    { file: "TROUBLESHOOTING.md", title: "Kindful Error Guide" },
    { file: "KERNEL.md", title: "Trusted Kernel Soundness" },
    { file: "AI_AGENT_GUIDE.md", title: "AI Agent Playbook" },
    { file: "AI_PROTOCOL.md", title: "JSON-RPC Protocol Reference" }
  ];

  const FINDER_ITEMS = [
    { kind: "Tactic", name: "arith / ring", match: "Nat equality (+, *, 0, Succ)", desc: "Proves arbitrary Nat commutative semiring identities with 0 axioms." },
    { kind: "Tactic", name: "simp / simp(*)", match: "Definition unfolding & @simp rules", desc: "Normalizes with NbE and rewrites with @simp lemmas (and local equalities with *)." },
    { kind: "Tactic", name: "calc { ... }", match: "Multi-step equational reasoning", desc: "Readable chain of `=== rhs by { ... }` steps compiled to kernel transitivity." },
    { kind: "Tactic", name: "cases(expr, eqHyp)", match: "if (cond) / Bool / enum branching", desc: "Splits on `expr` while binding `eqHyp : expr === Ctor(...)` in each branch." },
    { kind: "Tactic", name: "induction(x)", match: "Recursive proofs on Nat, List, Tree", desc: "Generates structural induction hypotheses (even multiple IHs for binary trees!)." },
    { kind: "Tactic", name: "revert(x)", match: "Generalizing before induction / cases", desc: "Moves a local variable or hypothesis back into the goal as `forall`." },
    { kind: "Tactic", name: "auto / samurai", match: "Propositional logic & equality", desc: "Bounded automated proof search synthesizing kernel-verified proof terms." },
    { kind: "Tactic", name: "decide", match: "Concrete arithmetic, lists, Le(m, n)", desc: "Closes decidable concrete propositions by normalization & reflection." },
    { kind: "Tactic", name: "discriminate(h)", match: "Conflicting constructors (0 === Succ(n))", desc: "Closes any goal from an impossible constructor equality." },
    { kind: "Tactic", name: "injection(h, eq)", match: "Equal constructors (Succ(a) === Succ(b))", desc: "Extracts argument equality `eq : a === b` into local hypotheses." },
    { kind: "Error", name: "K020", match: "Termination / recursive call", desc: "Pass a structurally smaller pattern-matched subterm (e.g. `tail`, not `Cons(h, rest)`)." },
    { kind: "Error", name: "K006", match: "Strict positivity violation", desc: "Inductive type cannot appear to the left of `=>` in its own constructor." },
    { kind: "Error", name: "K025", match: "Prop -> Type elimination", desc: "Cannot eliminate Or/Exists into Type; use Either or Subset for runtime values." },
    { kind: "Error", name: "K005", match: "Universe level exceeded", desc: "A Type0 inductive cannot store Type0 fields; annotate the enum as `: Type1`." },
    { kind: "Error", name: "K026 / E071", match: "Non-exhaustive match", desc: "Cover every constructor of the enum or add a `case _ => ...` fallback." },
    { kind: "Error", name: "T010 / T015", match: "refl / rewrite failed", desc: "Try `simp`, `arith`, `rewriteRev(...)`, or drop `?help` to inspect the folded goal." }
  ];

  const docCache = new Map();
  const $ = (id) => document.getElementById(id);

  function escapeHtml(str) {
    return str.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
  }

  function highlightSamurai(code) {
    const escaped = escapeHtml(code);
    const tokenRe =
      /(\/\/[^\n]*|\/\*[\s\S]*?\*\/)|(\?[A-Za-z_][A-Za-z0-9_']*|\?)|\b(module|import|enum|case|class|def|val|theorem|lemma|axiom|match|if|else|by|calc|forall|exists|returning|sorry|true|false|object|final)\b|\b(intro|intros|exact|apply|refl|symmetry|trans|rewrite|rewriteRev|congr|induction|cases|revert|exfalso|subst|specialize|split|left|right|contradiction|discriminate|injection|have|unfold|simp|arith|ring|trivial|decide|auto|samurai|assumption)\b|\b(Prop|Type[0-9]*|Nat|Bool|List|Vec|Tree|Option|Queue|Pair|Subset|Eq|Le|And|Or|Not|False|True|Unit|Either)\b|\b([0-9]+)\b|(===|!==|=&gt;|->|\/\\|\\\/|::|\+\+)/g;

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

  function renderMarkdown(md) {
    const codeBlocks = [];
    const withPlaceholders = md.replace(/```(\w*)\n([\s\S]*?)```/g, (_, lang, code) => {
      const idx = codeBlocks.length;
      codeBlocks.push({ lang, code });
      return `\n@@CODEBLOCK_${idx}@@\n`;
    });

    const lines = withPlaceholders.split(/\r?\n/);
    let html = "";
    let inList = false;
    let inTable = false;

    const flushList = () => { if (inList) { html += "</ul>"; inList = false; } };
    const flushTable = () => { if (inTable) { html += "</tbody></table>"; inTable = false; } };

    const inlineFmt = (text) =>
      escapeHtml(text)
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
        html += `<pre><button class="copy-code-btn" data-copy-code="${encodeURIComponent(block.code)}">Copy</button><code>${body}</code></pre>`;
        continue;
      }

      if (line.startsWith("|") && line.endsWith("|")) {
        flushList();
        const cells = line.slice(1, -1).split("|").map((c) => c.trim());
        if (cells.every((c) => /^[-:]+$/.test(c))) continue;
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

      if (line.startsWith("### ")) { flushList(); html += `<h3>${inlineFmt(line.slice(4))}</h3>`; }
      else if (line.startsWith("## ")) { flushList(); html += `<h2>${inlineFmt(line.slice(3))}</h2>`; }
      else if (line.startsWith("# ")) { flushList(); html += `<h1>${inlineFmt(line.slice(2))}</h1>`; }
      else if (/^[-*]\s+/.test(line)) {
        if (!inList) { html += "<ul>"; inList = true; }
        html += `<li>${inlineFmt(line.replace(/^[-*]\s+/, ""))}</li>`;
      } else if (line.trim() === "") {
        flushList();
      } else {
        flushList();
        html += `<p>${inlineFmt(line)}</p>`;
      }
    }
    flushList();
    flushTable();
    return html;
  }

  async function loadMarkdownFile(file) {
    if (docCache.has(file)) return docCache.get(file);
    const res = await fetch(file);
    if (!res.ok) throw new Error(`Could not load ${file}`);
    const text = await res.text();
    docCache.set(file, text);
    return text;
  }

  function setActiveNav(pageId) {
    document.querySelectorAll(".nav-item").forEach((btn) => {
      btn.classList.toggle("active", btn.dataset.page === pageId);
    });
  }

  function showPageSection(sectionId) {
    document.querySelectorAll(".page").forEach((p) => p.classList.remove("active"));
    $(sectionId).classList.add("active");
    window.scrollTo({ top: 0, behavior: "smooth" });
  }

  async function navigate(pageId) {
    window.location.hash = pageId;
    setActiveNav(pageId);

    if (pageId === "home" || !pageId) {
      showPageSection("page-home");
      return;
    }
    if (pageId === "finder") {
      showPageSection("page-finder");
      renderFinder($("finder-input").value);
      return;
    }

    showPageSection("page-markdown");
    $("markdown-container").innerHTML = `<p class="muted-lead">Loading ${escapeHtml(pageId)}…</p>`;
    try {
      const md = await loadMarkdownFile(pageId);
      $("markdown-container").innerHTML = renderMarkdown(md);
      wireCopyButtons($("markdown-container"));

      const idx = CHAPTERS.findIndex((c) => c.file === pageId);
      const prev = idx > 0 ? CHAPTERS[idx - 1] : null;
      const next = idx >= 0 && idx < CHAPTERS.length - 1 ? CHAPTERS[idx + 1] : null;
      $("chapter-nav").innerHTML = `
        <div>${prev ? `<button class="btn btn-secondary" data-goto="${prev.file}">← ${escapeHtml(prev.title)}</button>` : ""}</div>
        <div>${next ? `<button class="btn btn-primary" data-goto="${next.file}">${escapeHtml(next.title)} →</button>` : ""}</div>
      `;
      $("chapter-nav").querySelectorAll("[data-goto]").forEach((b) => {
        b.addEventListener("click", () => navigate(b.dataset.goto));
      });
    } catch (err) {
      $("markdown-container").innerHTML = `<p>Could not load <code>${escapeHtml(pageId)}</code>: ${escapeHtml(String(err))}</p>`;
    }
  }

  function wireCopyButtons(root) {
    root.querySelectorAll("[data-copy-code]").forEach((btn) => {
      btn.addEventListener("click", () => {
        navigator.clipboard?.writeText(decodeURIComponent(btn.dataset.copyCode));
        btn.textContent = "Copied!";
        setTimeout(() => (btn.textContent = "Copy"), 1200);
      });
    });
  }

  function renderFinder(query) {
    const q = (query || "").toLowerCase().trim();
    const filtered = FINDER_ITEMS.filter(
      (item) =>
        !q ||
        item.name.toLowerCase().includes(q) ||
        item.match.toLowerCase().includes(q) ||
        item.desc.toLowerCase().includes(q) ||
        item.kind.toLowerCase().includes(q)
    );
    $("finder-results").innerHTML = filtered
      .map(
        (item) => `<div class="finder-card">
          <div class="finder-card-head">
            <code>${escapeHtml(item.name)}</code>
            <span class="finder-tag">${escapeHtml(item.kind)}</span>
          </div>
          <div style="font-size:12.5px;font-weight:600">${escapeHtml(item.match)}</div>
          <p>${escapeHtml(item.desc)}</p>
        </div>`
      )
      .join("");
  }

  async function runGlobalSearch(query) {
    const q = (query || "").toLowerCase().trim();
    if (!q) {
      navigate("home");
      return;
    }
    showPageSection("page-search");
    const cards = [];

    // Search Finder items
    for (const item of FINDER_ITEMS) {
      if (
        item.name.toLowerCase().includes(q) ||
        item.match.toLowerCase().includes(q) ||
        item.desc.toLowerCase().includes(q)
      ) {
        cards.push(`<div class="finder-card">
          <div class="finder-card-head"><code>${escapeHtml(item.name)}</code><span class="finder-tag">${escapeHtml(item.kind)}</span></div>
          <div style="font-size:12.5px;font-weight:600">${escapeHtml(item.match)}</div>
          <p>${escapeHtml(item.desc)}</p>
        </div>`);
      }
    }

    // Search Markdown guides
    for (const ch of CHAPTERS) {
      try {
        const md = await loadMarkdownFile(ch.file);
        const pos = md.toLowerCase().indexOf(q);
        if (pos >= 0) {
          const snippet = md.slice(Math.max(0, pos - 40), Math.min(md.length, pos + 130)).replace(/\s+/g, " ");
          cards.push(`<div class="finder-card" style="cursor:pointer" data-goto="${ch.file}">
            <div class="finder-card-head"><strong>${escapeHtml(ch.title)}</strong><span class="finder-tag">Guide</span></div>
            <p>…${escapeHtml(snippet)}…</p>
          </div>`);
        }
      } catch (_) {}
    }

    $("search-results").innerHTML = cards.length > 0 ? cards.join("") : `<p class="muted-lead">No matches found for "${escapeHtml(query)}".</p>`;
    $("search-results").querySelectorAll("[data-goto]").forEach((el) => {
      el.addEventListener("click", () => navigate(el.dataset.goto));
    });
  }

  function init() {
    // Highlight static home snippets
    document.querySelectorAll("code.lang-samurai").forEach((el) => {
      el.innerHTML = highlightSamurai(el.textContent);
    });

    document.querySelectorAll(".nav-item").forEach((btn) => {
      btn.addEventListener("click", () => navigate(btn.dataset.page));
    });
    document.querySelectorAll("[data-goto]").forEach((btn) => {
      btn.addEventListener("click", () => navigate(btn.dataset.goto));
    });
    $("brand-link").addEventListener("click", (e) => {
      e.preventDefault();
      navigate("home");
    });
    $("theme-toggle").addEventListener("click", () => {
      const root = document.documentElement;
      root.dataset.theme = root.dataset.theme === "dark" ? "light" : "dark";
    });
    document.querySelectorAll("[data-copy]").forEach((btn) => {
      btn.addEventListener("click", () => {
        navigator.clipboard?.writeText(btn.dataset.copy);
        btn.textContent = "Copied!";
        setTimeout(() => (btn.textContent = "Copy"), 1200);
      });
    });

    $("finder-input").addEventListener("input", (e) => renderFinder(e.target.value));
    let searchTimer = null;
    $("doc-search").addEventListener("input", (e) => {
      clearTimeout(searchTimer);
      searchTimer = setTimeout(() => runGlobalSearch(e.target.value), 180);
    });

    const initialHash = window.location.hash.replace(/^#/, "");
    navigate(initialHash || "home");
  }

  init();
})();
