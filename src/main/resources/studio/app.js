(() => {
  const state = {
    examples: [],
    docs: [],
    symbols: [],
    extractTarget: "scala3",
    lastExtractedCode: "",
    proverSessionId: null,
    proverNodes: [],
    activeProverStateId: null,
    activeFile: "Showcase.samurai"
  };

  const SNIPPETS = {
    theorem: `\ntheorem myTheorem(value: Nat): value + 0 === value = by {\n  arith\n}\n`,
    calc: `\ntheorem calcDemo(left: Nat, right: Nat): (left + right) + 0 === right + left = {\n  calc {\n    (left + right) + 0\n    === left + right by { simp }\n    === right + left by { arith }\n  }\n}\n`,
    induction: `\ninduction(value) {\n  case Zero => { refl }\n  case Succ(pred, ih) => {\n    simp\n    rewrite(ih)\n    refl\n  }\n}\n`,
    enum: `\nenum Color: Type {\n  case Red\n  case Green\n  case Blue\n}\n`,
    hole: `\n?nextStep\n`
  };

  const $ = (id) => document.getElementById(id);

  function escapeHtml(str) {
    return str
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;");
  }

  function highlightSamurai(code) {
    const escaped = escapeHtml(code);
    const tokenRe =
      /(\/\/[^\n]*|\/\*[\s\S]*?\*\/)|(\?[A-Za-z_][A-Za-z0-9_']*|\?)|\b(module|import|enum|case|class|def|val|theorem|lemma|axiom|match|if|else|by|calc|forall|exists|returning|sorry|true|false)\b|\b(intro|intros|exact|apply|refl|symmetry|trans|rewrite|rewriteRev|congr|induction|cases|revert|exfalso|subst|specialize|split|left|right|contradiction|discriminate|injection|have|unfold|simp|arith|ring|trivial|decide|auto|samurai|assumption)\b|\b(Prop|Type[0-9]*|Nat|Bool|List|Vec|Tree|Option|Queue|Pair|Subset|Eq|Le|And|Or|Not|False|True|Unit|Either)\b|\b([0-9]+)\b|(===|!==|=&gt;|->|\/\\|\\\/|::|\+\+)/g;

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

  function syncEditorVisuals() {
    const editor = $("code-editor");
    const code = editor.value;
    $("highlight-code").innerHTML = highlightSamurai(code) + "\n";
    const lineCount = Math.max(1, code.split("\n").length);
    let nums = "";
    for (let i = 1; i <= lineCount; i++) nums += i + "\n";
    $("line-numbers").textContent = nums;
    updateCursorPos();
  }

  function updateCursorPos() {
    const editor = $("code-editor");
    const before = editor.value.slice(0, editor.selectionStart);
    const lines = before.split("\n");
    $("cursor-pos").textContent = `Ln ${lines.length}, Col ${lines[lines.length - 1].length + 1}`;
  }

  function syncScroll() {
    const editor = $("code-editor");
    $("highlight-layer").scrollTop = editor.scrollTop;
    $("highlight-layer").scrollLeft = editor.scrollLeft;
    $("line-numbers").scrollTop = editor.scrollTop;
  }

  function switchMode(mode) {
    document.querySelectorAll(".mode-tab").forEach((b) => {
      const isActive = b.dataset.mode === mode;
      b.classList.toggle("active", isActive);
      b.setAttribute("aria-selected", String(isActive));
    });
    document.querySelectorAll(".workspace").forEach((w) => w.classList.remove("active"));
    $(`view-${mode}`).classList.add("active");
  }

  function switchSubPanel(panel) {
    document.querySelectorAll(".sub-tab").forEach((b) => {
      b.classList.toggle("active", b.dataset.panel === panel);
    });
    document.querySelectorAll("#view-editor .panel-body").forEach((p) => p.classList.remove("active"));
    $(`panel-${panel}`).classList.add("active");
  }

  async function apiPost(url, payload) {
    const res = await fetch(url, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(payload)
    });
    return res.json();
  }

  // =========================================================================
  // Check / Infoview
  // =========================================================================

  async function runVerify() {
    const source = $("code-editor").value;
    const badge = $("trust-badge");
    badge.className = "badge badge-neutral";
    badge.textContent = "Checking…";
    $("status-line").textContent = "Verifying through Trusted Kernel…";

    try {
      const data = await apiPost("/api/check", {
        file: state.activeFile,
        source,
        collectHoles: true
      });
      renderCheckResult(data);
    } catch (err) {
      badge.className = "badge badge-crimson";
      badge.textContent = "Connection Error";
      $("verify-banner").className = "card banner banner-crimson";
      $("verify-banner").textContent = String(err);
    }
  }

  function renderCheckResult(data) {
    const badge = $("trust-badge");
    const banner = $("verify-banner");
    $("directives-section").classList.add("hidden");
    $("holes-section").classList.add("hidden");
    $("errors-section").classList.add("hidden");

    if (data.diagnostics && data.diagnostics.length > 0) {
      badge.className = "badge badge-crimson";
      badge.textContent = "✗ Kernel Rejected";
      banner.className = "card banner banner-crimson";
      banner.innerHTML = `<strong>Verification failed</strong> (${data.elapsedMs}ms) — Trusted Kernel rejected an invalid step.`;

      $("errors-section").classList.remove("hidden");
      const diag = data.diagnostics[0];
      $("errors-list").innerHTML = `
        <div class="card">
          <pre class="error-pre">${escapeHtml(data.formattedError || diag.message)}</pre>
          ${data.kindHint ? `<div class="kind-hint"><strong>💡 Kindful Hint:</strong> ${escapeHtml(data.kindHint)}</div>` : ""}
        </div>`;
      $("status-line").textContent = `Error [${diag.code}] at line ${diag.span?.startLine || "?"}`;
      return;
    }

    const stats = data.stats || { inductives: 0, functions: 0, theorems: 0 };
    $("stats-line").textContent = `${stats.inductives} types · ${stats.functions} functions · ${stats.theorems} theorems · ${data.elapsedMs}ms`;

    if (data.hasHoles) {
      badge.className = "badge badge-amber";
      badge.textContent = `⚠ ${data.holes.length} Open Hole(s)`;
      banner.className = "card banner banner-amber";
      banner.innerHTML = `<strong>Proof in progress:</strong> Found ${data.holes.length} open <code>?hole(s)</code>. Click any suggested tactic below to copy it into your proof!`;
    } else if (data.isAxiomFree) {
      badge.className = "badge badge-jade";
      badge.textContent = "🛡 100% Axiom-Free";
      banner.className = "card banner banner-jade";
      banner.innerHTML = `<strong>Verified 100% Axiom-Free!</strong> All ${stats.theorems} theorem(s) and ${stats.functions} function(s) passed the Trusted Kernel in ${data.elapsedMs}ms.`;
    } else {
      badge.className = "badge badge-amber";
      badge.textContent = "⚠ Uses Axioms";
      banner.className = "card banner banner-amber";
      banner.innerHTML = `<strong>Type-checked with axioms:</strong> <code>${escapeHtml((data.axiomsUsed || []).join(", "))}</code>. Replace <code>sorry</code> before strict extraction.`;
    }

    // Directives (#eval / #axioms / #check)
    if (data.directives && data.directives.length > 0) {
      $("directives-section").classList.remove("hidden");
      $("directives-list").innerHTML = data.directives
        .map(
          (d) => `<div class="card directive-card">
            <span class="directive-tag">#${escapeHtml(d.directive)}</span>
            <span>${escapeHtml(d.output)}</span>
          </div>`
        )
        .join("");
    }

    // Holes
    if (data.holes && data.holes.length > 0) {
      $("holes-section").classList.remove("hidden");
      $("holes-list").innerHTML = data.holes
        .map((item) => {
          const h = item.hole;
          const hyps = (h.hypotheses || []).map((hp) => `${hp.name} : ${hp.type}`).join("\n");
          const pills = (item.suggestions || [])
            .slice(0, 6)
            .map(
              (s) => `<button class="sug-pill" data-copy-tactic="${escapeHtml(s.tactic)}" title="${escapeHtml(s.rationale)}">${escapeHtml(s.tactic)} (${Math.round(s.confidence * 100)}%)</button>`
            )
            .join("");
          return `<div class="goal-card">
            <div class="goal-header">
              <strong>?${escapeHtml(h.name || "hole")} <span class="muted">(line ${h.span?.startLine || "?"})</span></strong>
              <span class="badge badge-neutral">${escapeHtml(item.goalShape || "goal")}</span>
            </div>
            ${hyps ? `<div class="goal-hyps">${escapeHtml(hyps)}</div>` : ""}
            <div class="goal-turnstile">⊢ ${escapeHtml(h.expectedType)}</div>
            <div class="suggestion-pills">${pills}</div>
          </div>`;
        })
        .join("");

      $("holes-list").querySelectorAll("[data-copy-tactic]").forEach((btn) => {
        btn.addEventListener("click", () => {
          navigator.clipboard?.writeText(btn.dataset.copyTactic);
          $("status-line").textContent = `Copied tactic '${btn.dataset.copyTactic}' to clipboard!`;
        });
      });
    }

    // Symbols outline
    state.symbols = data.symbols || [];
    renderSymbols();
    $("status-line").textContent = `Verified '${state.activeFile}' in ${data.elapsedMs}ms.`;
  }

  function renderSymbols() {
    const q = ($("symbol-filter").value || "").toLowerCase();
    const filtered = state.symbols.filter(
      (s) => !q || s.name.toLowerCase().includes(q) || s.type.toLowerCase().includes(q)
    );
    $("symbols-list").innerHTML = filtered
      .map(
        (s) => `<div class="symbol-row">
          <div class="symbol-top">
            <span class="symbol-name"><span class="tok-kw">${escapeHtml(s.kind)}</span> ${escapeHtml(s.name)}</span>
            <div>
              ${s.isSimp ? `<span class="chip">@simp</span>` : ""}
              ${s.kind === "theorem" ? (s.isAxiomFree ? `<span class="badge badge-jade">0 axioms</span>` : `<span class="badge badge-amber">axiom</span>`) : ""}
            </div>
          </div>
          <div class="symbol-type">${escapeHtml(s.type)}</div>
        </div>`
      )
      .join("");
  }

  // =========================================================================
  // Code Extraction
  // =========================================================================

  async function runExtract() {
    const source = $("code-editor").value;
    const strict = $("extract-strict").checked;
    $("extract-code").textContent = "// Extracting verified code…";
    const data = await apiPost("/api/extract", {
      source,
      target: state.extractTarget,
      moduleName: "VerifiedSamuraiApp",
      strict
    });
    if (!data.ok) {
      $("extract-manifest").innerHTML = `<div class="card banner banner-crimson" style="grid-column: 1 / -1;">${escapeHtml(data.error)}</div>`;
      $("extract-code").textContent = "// Fix verification errors or uncheck Strict mode to extract.";
      return;
    }
    const m = data.manifest;
    state.lastExtractedCode = data.code;
    $("extract-manifest").innerHTML = `
      <div class="manifest-stat"><div class="manifest-stat-value" style="color:var(--jade)">${m.verifiedTheorems.length}</div><div class="manifest-stat-label">Theorems Verified &amp; Erased</div></div>
      <div class="manifest-stat"><div class="manifest-stat-value">${m.erasedPropositions.length}</div><div class="manifest-stat-label">Prop Types Erased</div></div>
      <div class="manifest-stat"><div class="manifest-stat-value">${m.extractedFunctions.length}</div><div class="manifest-stat-label">Extracted Functions</div></div>
      <div class="manifest-stat"><div class="manifest-stat-value" style="color:${m.isAxiomFree ? "var(--jade)" : "var(--amber)"}">${m.isAxiomFree ? "0" : m.axiomsUsed.length}</div><div class="manifest-stat-label">Axioms Used</div></div>
    `;
    $("extract-code").textContent = data.code;
  }

  // =========================================================================
  // Interactive Proof Tree Mode
  // =========================================================================

  async function proverRpc(method, params) {
    const res = await apiPost("/api/proof", {
      sessionId: state.proverSessionId,
      method,
      params
    });
    state.proverSessionId = res.sessionId;
    return res.rpc;
  }

  async function startInteractiveProof() {
    const statement = $("prover-statement").value.trim();
    const theoremName = "interactive_" + Math.floor(Math.random() * 10000);
    const rpc = await proverRpc("startProof", { name: theoremName, statement });
    if (!rpc.ok) {
      $("prover-feedback").className = "card banner banner-crimson";
      $("prover-feedback").textContent = rpc.error.message;
      return;
    }
    const r = rpc.result;
    state.proverNodes = [
      {
        stateId: r.stateId,
        parentStateId: null,
        tactic: "Initial Goal",
        isSolved: r.isSolved,
        openGoals: r.openGoals,
        suggestions: r.suggestions || []
      }
    ];
    state.activeProverStateId = r.stateId;
    $("prover-feedback").className = "card banner banner-neutral";
    $("prover-feedback").textContent = "Proof started! Click a suggested tactic pill or type a tactic below.";
    $("trace-box").classList.add("hidden");
    renderProverState();
  }

  async function stepInteractiveProof(tacticText) {
    if (!state.activeProverStateId) return;
    const rpc = await proverRpc("step", {
      stateId: state.activeProverStateId,
      tactic: tacticText
    });
    if (!rpc.ok) {
      $("prover-feedback").className = "card banner banner-crimson";
      $("prover-feedback").textContent = `Tactic '${tacticText}' failed: ${rpc.error.message}`;
      return;
    }
    const r = rpc.result;
    state.proverNodes.push({
      stateId: r.stateId,
      parentStateId: state.activeProverStateId,
      tactic: tacticText,
      isSolved: r.isSolved,
      kernelVerified: r.kernelVerified,
      openGoals: r.openGoals || [],
      suggestions: r.suggestions || []
    });
    state.activeProverStateId = r.stateId;

    if (r.isSolved) {
      $("prover-feedback").className = "card banner banner-jade";
      $("prover-feedback").innerHTML = `<strong>🛡 Q.E.D. — Kernel Verified (100% Axiom-Free)!</strong> Copy the generated script on the right.`;
      await fetchProofTrace(r.stateId);
    } else {
      $("prover-feedback").className = "card banner banner-neutral";
      $("prover-feedback").textContent = `Applied '${tacticText}' → ${r.openGoals.length} open goal(s) remaining.`;
    }
    renderProverState();
  }

  async function fetchProofTrace(stateId) {
    const rpc = await proverRpc("getProofTrace", { stateId });
    if (rpc.ok) {
      $("trace-box").classList.remove("hidden");
      $("trace-code").textContent = rpc.result.script;
    }
  }

  function renderProverState() {
    const node = state.proverNodes.find((n) => n.stateId === state.activeProverStateId);
    if (!node) return;

    if (node.isSolved) {
      $("prover-goal-box").classList.add("hidden");
      $("prover-tactic-box").classList.add("hidden");
    } else {
      $("prover-goal-box").classList.remove("hidden");
      $("prover-tactic-box").classList.remove("hidden");
      const g = node.openGoals[0];
      const hyps = (g.hypotheses || []).map((h) => `${h.name} : ${h.type}`).join("\n");
      $("prover-goal-card").innerHTML = `
        <div class="goal-header">
          <strong>State #${node.stateId} · ${escapeHtml(g.label)}</strong>
          <span class="badge badge-neutral">${escapeHtml(g.goalShape || "goal")}</span>
        </div>
        ${hyps ? `<div class="goal-hyps">${escapeHtml(hyps)}</div>` : ""}
        <div class="goal-turnstile">⊢ ${escapeHtml(g.normalizedTarget)}</div>
      `;
      $("prover-suggestions").innerHTML = (node.suggestions || [])
        .slice(0, 7)
        .map(
          (s) => `<button class="sug-pill" data-step-tactic="${escapeHtml(s.tactic)}" title="${escapeHtml(s.rationale)}">${escapeHtml(s.tactic)}</button>`
        )
        .join("");
      $("prover-suggestions").querySelectorAll("[data-step-tactic]").forEach((btn) => {
        btn.addEventListener("click", () => stepInteractiveProof(btn.dataset.stepTactic));
      });
    }

    // Render branching proof exploration tree
    const depthOf = (n) => {
      let d = 0;
      let cur = n;
      while (cur && cur.parentStateId != null) {
        d++;
        cur = state.proverNodes.find((x) => x.stateId === cur.parentStateId);
      }
      return d;
    };

    $("proof-tree").innerHTML = state.proverNodes
      .map((n) => {
        const indent = Math.min(depthOf(n), 8) * 18;
        const cls = ["tree-node", n.stateId === state.activeProverStateId ? "active" : "", n.isSolved ? "solved" : ""].join(" ");
        const status = n.isSolved ? "🛡 Q.E.D." : `${n.openGoals.length} goal(s)`;
        return `<div class="${cls}" data-select-state="${n.stateId}" style="margin-left:${indent}px">
          <div style="display:flex;justify-content:space-between;align-items:center">
            <span class="mono"><strong>#${n.stateId}</strong> ${escapeHtml(n.tactic)}</span>
            <span class="muted">${status}</span>
          </div>
        </div>`;
      })
      .join("");

    $("proof-tree").querySelectorAll("[data-select-state]").forEach((el) => {
      el.addEventListener("click", () => {
        state.activeProverStateId = Number(el.dataset.selectState);
        $("prover-feedback").className = "card banner banner-neutral";
        $("prover-feedback").textContent = `Switched to state #${state.activeProverStateId} (branching / backtracking ready).`;
        renderProverState();
      });
    });
  }

  // =========================================================================
  // Lightweight Markdown Renderer for Kindful Docs
  // =========================================================================

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

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      const cbMatch = line.trim().match(/^@@CODEBLOCK_(\d+)@@$/);
      if (cbMatch) {
        flushList();
        flushTable();
        const block = codeBlocks[Number(cbMatch[1])];
        const canTry = block.lang === "scala" || block.lang === "samurai" || block.lang === "";
        const highlighted = canTry ? highlightSamurai(block.code) : escapeHtml(block.code);
        html += `<pre>${canTry ? `<button class="try-btn" data-try-code="${encodeURIComponent(block.code)}">Load in Editor ▶</button>` : ""}<code>${highlighted}</code></pre>`;
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

  function showDoc(docId) {
    const doc = state.docs.find((d) => d.id === docId) || state.docs[0];
    if (!doc) return;
    document.querySelectorAll(".doc-nav-btn").forEach((b) => b.classList.toggle("active", b.dataset.docId === doc.id));
    $("docs-title").textContent = doc.title;
    $("docs-body").innerHTML = renderMarkdown(doc.markdown);
    $("docs-body").querySelectorAll("[data-try-code]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const snippet = decodeURIComponent(btn.dataset.tryCode);
        const needsImports = !snippet.includes("import ") && !snippet.includes("module ");
        $("code-editor").value = needsImports
          ? `import Prelude.*\nimport Nat.*\nimport List.*\n\n${snippet}`
          : snippet;
        state.activeFile = "Tutorial.samurai";
        $("current-filename").textContent = state.activeFile;
        syncEditorVisuals();
        switchMode("editor");
        runVerify();
      });
    });
  }

  // =========================================================================
  // Initialization & Event Wiring
  // =========================================================================

  async function init() {
    // Mode tabs
    document.querySelectorAll(".mode-tab").forEach((btn) => {
      btn.addEventListener("click", () => switchMode(btn.dataset.mode));
    });
    // Sub tabs
    document.querySelectorAll(".sub-tab").forEach((btn) => {
      btn.addEventListener("click", () => {
        switchSubPanel(btn.dataset.panel);
        if (btn.dataset.panel === "extract") runExtract();
      });
    });
    // Theme toggle
    $("btn-theme").addEventListener("click", () => {
      const root = document.documentElement;
      root.dataset.theme = root.dataset.theme === "dark" ? "light" : "dark";
    });
    // Editor events
    const editor = $("code-editor");
    editor.addEventListener("input", syncEditorVisuals);
    editor.addEventListener("scroll", syncScroll);
    editor.addEventListener("click", updateCursorPos);
    editor.addEventListener("keyup", updateCursorPos);
    editor.addEventListener("keydown", (e) => {
      if ((e.ctrlKey || e.metaKey) && e.key === "Enter") {
        e.preventDefault();
        runVerify();
      } else if (e.key === "Tab") {
        e.preventDefault();
        const start = editor.selectionStart;
        const end = editor.selectionEnd;
        editor.value = editor.value.substring(0, start) + "  " + editor.value.substring(end);
        editor.selectionStart = editor.selectionEnd = start + 2;
        syncEditorVisuals();
      }
    });

    // Snippet chips
    document.querySelectorAll("[data-snippet]").forEach((chip) => {
      chip.addEventListener("click", () => {
        const text = SNIPPETS[chip.dataset.snippet] || "";
        const start = editor.selectionStart;
        editor.value = editor.value.slice(0, start) + text + editor.value.slice(editor.selectionEnd);
        editor.selectionStart = editor.selectionEnd = start + text.length;
        syncEditorVisuals();
        editor.focus();
      });
    });

    $("btn-verify").addEventListener("click", runVerify);
    $("symbol-filter").addEventListener("input", renderSymbols);

    // Extraction controls
    document.querySelectorAll(".target-btn").forEach((btn) => {
      btn.addEventListener("click", () => {
        document.querySelectorAll(".target-btn").forEach((b) => b.classList.remove("active"));
        btn.classList.add("active");
        state.extractTarget = btn.dataset.target;
        runExtract();
      });
    });
    $("btn-run-extract").addEventListener("click", runExtract);
    $("btn-copy-extract").addEventListener("click", () => {
      navigator.clipboard?.writeText(state.lastExtractedCode);
      $("status-line").textContent = "Copied extracted code to clipboard!";
    });
    $("btn-download-extract").addEventListener("click", () => {
      if (!state.lastExtractedCode) return;
      const ext = state.extractTarget === "ts" ? "ts" : state.extractTarget === "js" ? "mjs" : "scala";
      const blob = new Blob([state.lastExtractedCode], { type: "text/plain" });
      const a = document.createElement("a");
      a.href = URL.createObjectURL(blob);
      a.download = `VerifiedSamuraiApp.${ext}`;
      a.click();
    });

    // Interactive Prover controls
    $("prover-preset").addEventListener("change", (e) => {
      $("prover-statement").value = e.target.value;
    });
    $("btn-start-proof").addEventListener("click", startInteractiveProof);
    $("btn-apply-tactic").addEventListener("click", () => {
      const val = $("prover-tactic-input").value.trim();
      if (val) {
        $("prover-tactic-input").value = "";
        stepInteractiveProof(val);
      }
    });
    $("prover-tactic-input").addEventListener("keydown", (e) => {
      if (e.key === "Enter") $("btn-apply-tactic").click();
    });
    $("btn-auto-solve").addEventListener("click", () => stepInteractiveProof("auto(6)"));
    $("btn-copy-trace").addEventListener("click", () => {
      navigator.clipboard?.writeText($("trace-code").textContent);
    });

    // Load examples
    const exRes = await fetch("/api/examples").then((r) => r.json());
    state.examples = exRes.examples || [];
    const sel = $("example-select");
    sel.innerHTML = state.examples
      .map((ex) => `<option value="${ex.id}">[${ex.category}] ${escapeHtml(ex.title)}</option>`)
      .join("");
    sel.addEventListener("change", () => {
      const found = state.examples.find((x) => x.id === sel.value);
      if (found) {
        state.activeFile = found.path;
        $("current-filename").textContent = found.path;
        editor.value = found.code;
        syncEditorVisuals();
        runVerify();
      }
    });

    if (state.examples.length > 0) {
      const first = state.examples[0];
      state.activeFile = first.path;
      $("current-filename").textContent = first.path;
      editor.value = first.code;
      syncEditorVisuals();
      runVerify();
    }

    // Load kindful docs
    const docsRes = await fetch("/api/docs").then((r) => r.json());
    state.docs = docsRes.docs || [];
    $("docs-nav").innerHTML = state.docs
      .map((d) => `<button class="doc-nav-btn" data-doc-id="${d.id}">${escapeHtml(d.title)}</button>`)
      .join("");
    $("docs-nav").querySelectorAll(".doc-nav-btn").forEach((btn) => {
      btn.addEventListener("click", () => showDoc(btn.dataset.docId));
    });
    if (state.docs.length > 0) showDoc(state.docs[0].id);
  }

  init();
})();
