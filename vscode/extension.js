const fs = require('fs');
const path = require('path');
const cp = require('child_process');
const vscode = require('vscode');

const NO_FILE_MESSAGE = 'Open a .batt file to see its output.';

class BattOutputViewProvider {
  constructor(context) {
    this.context = context;
    this.view = undefined;
    this.lastModel = undefined;   // parsed checker output (see parseOutput)
    this.lastMessage = '';        // plain status message, when there is no model
    this.lastDocUri = undefined;  // document the model belongs to
    this.openState = {};          // which <details> sections the user opened
    this.bunchMode = 'auto';      // bunch display: auto | boxes | outline | raw
    this.isRunning = false;
    this.refreshTimer = undefined;
    this.cursorTimer = undefined;
    this.lastCursorKey = undefined;
  }

  resolveWebviewView(webviewView) {
    this.view = webviewView;
    webviewView.webview.options = {
      enableScripts: true,
      localResourceRoots: []
    };
    webviewView.webview.onDidReceiveMessage((message) => this.onMessage(message));
    this.render();
    this.refresh();

    webviewView.onDidDispose(() => {
      if (this.view === webviewView) {
        this.view = undefined;
      }
    });
  }

  async refresh() {
    const editor = vscode.window.activeTextEditor;
    const document = editor && editor.document;

    if (!document || document.languageId !== 'batt') {
      this.update(NO_FILE_MESSAGE);
      return;
    }

    if (!document.fileName) {
      this.update('This document has no file on disk yet.');
      return;
    }

    const workspaceFolder = vscode.workspace.getWorkspaceFolder(document.uri);
    if (!workspaceFolder) {
      this.update('Open the workspace root that contains the BATT project.');
      return;
    }

    if (this.isRunning) {
      return;
    }

    this.isRunning = true;
    // keep the previous output on screen while the checker runs, only flag it as stale
    if (this.lastDocUri && this.lastDocUri.toString() !== document.uri.toString()) {
      this.lastModel = undefined;
      this.lastMessage = `Running batt on ${path.basename(document.fileName)}...`;
    }
    this.render(document.isDirty ? 'checking unsaved changes…' : 'checking…');
    try {
      const source = await this.materializeDocument(document, workspaceFolder.uri.fsPath);
      try {
        const result = await runBatt(workspaceFolder.uri.fsPath, source.filePath);
        const shownName = path.relative(workspaceFolder.uri.fsPath, document.fileName);
        if (result.stopped) {
          this.update(stoppedMessage(result, shownName));
          return;
        }
        this.lastModel = parseOutput(result, source.filePath, shownName);
        this.lastDocUri = document.uri;
        this.render();
      } finally {
        try {
          await source.dispose();
        } catch (error) {
          void error;
        }
      }
    } catch (error) {
      const message = error && error.message ? error.message : String(error);
      this.update(`Failed to run batt.\n\n${message}`);
    } finally {
      this.isRunning = false;
    }
  }

  scheduleRefresh() {
    if (this.refreshTimer) {
      clearTimeout(this.refreshTimer);
    }
    this.refreshTimer = setTimeout(() => {
      this.refreshTimer = undefined;
      this.refresh();
    }, 300);
  }

  // the cursor moved: re-render (to change the current goal) without re-running the checker
  scheduleCursorRender() {
    if (this.cursorTimer) {
      clearTimeout(this.cursorTimer);
    }
    this.cursorTimer = setTimeout(() => {
      this.cursorTimer = undefined;
      if (!this.isRunning && this.lastModel && cursorKey(this.lastModel, this.cursorLine()) !== this.lastCursorKey) {
        this.render();
      }
    }, 100);
  }

  async materializeDocument(document, workspaceRoot) {
    if (!document.isDirty) {
      return {
        filePath: document.fileName,
        dispose: async () => {}
      };
    }

    const tempDir = document.uri.scheme === 'untitled' ? workspaceRoot : path.dirname(document.fileName);
    const tempName = `.batt-live-${process.pid}-${Date.now()}-${Math.random().toString(16).slice(2)}.batt`;
    const tempPath = path.join(tempDir, tempName);
    await fs.promises.writeFile(tempPath, document.getText(), 'utf8');

    return {
      filePath: tempPath,
      dispose: async () => {
        try {
          await fs.promises.unlink(tempPath);
        } catch (error) {
          if (!error || error.code !== 'ENOENT') {
            throw error;
          }
        }
      }
    };
  }

  // plain status message
  update(text) {
    this.lastModel = undefined;
    this.lastMessage = text;
    this.render();
  }

  // 1-based line of the cursor in the document the model belongs to, if visible
  cursorLine() {
    if (!this.lastDocUri) {
      return undefined;
    }
    const editor = vscode.window.visibleTextEditors.find((e) => e.document.uri.toString() === this.lastDocUri.toString());
    return editor ? editor.selection.active.line + 1 : undefined;
  }

  render(runningHint) {
    if (!this.view) {
      return;
    }
    const cursorLine = this.cursorLine();
    this.lastCursorKey = this.lastModel ? cursorKey(this.lastModel, cursorLine) : undefined;
    const body = this.lastModel
      ? renderModel(this.lastModel, cursorLine, this.openState, this.bunchMode)
      : messageHtml(this.lastMessage || NO_FILE_MESSAGE);
    this.view.webview.html = this.renderHtml(body, runningHint);
  }

  async onMessage(message) {
    if (!message) {
      return;
    }
    if (message.type === 'toggle') {
      const wasOpen = Boolean(this.openState[message.key]);
      this.openState[message.key] = message.open;
      if (message.open && !wasOpen) {
        this.render();
      }
    } else if (message.type === 'bunchMode') {
      this.bunchMode = message.mode;
      this.render();
    } else if (message.type === 'reveal' && this.lastDocUri) {
      await revealPosition(this.lastDocUri, message.line, message.col);
    }
  }

  renderHtml(body, runningHint) {
    const nonce = Math.random().toString(36).slice(2) + Math.random().toString(36).slice(2);
    const hint = runningHint
      ? `<div class="hint running">${escapeHtml(runningHint)}</div>`
      : '<div class="hint">Updates on save and editor change</div>';
    return `<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline'; script-src 'nonce-${nonce}';">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <style>
    :root {
      /* theme-aware colours, with fallbacks for themes that do not define them */
      --c-kw: var(--vscode-terminal-ansiMagenta, #c678dd);
      --c-type: var(--vscode-terminal-ansiBlue, #61afef);
      --c-const: var(--vscode-terminal-ansiGreen, #98c379);
      --c-op: var(--vscode-terminal-ansiCyan, #56b6c2);
      --c-num: var(--vscode-debugTokenExpression-number, #b5cea8);
      --c-name: var(--vscode-textLink-foreground, #3794ff);
      --c-post: var(--vscode-terminal-ansiYellow, #e5c07b);
      --c-hole: var(--vscode-charts-orange, #d18616);
      --c-err: var(--vscode-errorForeground, #f48771);
      --c-ok: var(--vscode-terminal-ansiGreen, #89d185);
      --c-warn: var(--vscode-terminal-ansiBrightMagenta, #d670d6);
      --c-dim: var(--vscode-descriptionForeground, #999);
      --c-box: var(--vscode-editor-inactiveSelectionBackground, rgba(128,128,128,0.15));
      --c-hover: var(--vscode-list-hoverBackground, rgba(128,128,128,0.2));
    }
    body {
      padding: 0.75rem 0.9rem;
      font-family: var(--vscode-font-family);
      color: var(--vscode-foreground);
      background: var(--vscode-editor-background);
      line-height: 1.5;
    }
    .header { display: flex; align-items: center; justify-content: space-between; margin-bottom: 0.5rem; gap: 0.75rem; }
    .title { font-size: 0.9rem; font-weight: 600; }
    .hint { font-size: 0.75rem; color: var(--c-dim); }
    .hint.running { color: var(--c-hole); font-style: italic; }
    .summary { display: flex; flex-wrap: wrap; gap: 0.35rem; margin-bottom: 0.7rem; }
    .chip { font-size: 0.75rem; padding: 0.05rem 0.5rem; border-radius: 999px; border: 1px solid currentColor; white-space: nowrap; }
    .chip.ok { color: var(--c-ok); }
    .chip.bad { color: var(--c-err); font-weight: 600; }
    .chip.holey { color: var(--c-hole); font-weight: 600; }
    .chip.post { color: var(--c-post); }
    .chip.hole { color: var(--c-hole); }
    .chip.decl { color: var(--c-name); }
    .chip.warn { color: var(--c-warn); }
    .code, pre.msg {
      font-family: var(--vscode-editor-font-family);
      font-size: var(--vscode-editor-font-size);
      white-space: pre-wrap;
      word-break: break-word;
    }
    pre.msg { margin: 0; padding: 0.6rem 0.75rem; border-radius: 6px; background: var(--c-box); }
    .card { border-left: 3px solid; border-radius: 4px; background: var(--c-box); padding: 0.45rem 0.7rem; margin: 0 0 0.6rem; }
    .card.goal { border-color: var(--c-hole); }
    .card.error { border-color: var(--c-err); }
    .card-head { display: flex; align-items: baseline; gap: 0.5rem; flex-wrap: wrap; margin-bottom: 0.25rem; }
    .tag { font-size: 0.72em; font-weight: 700; letter-spacing: 0.04em; padding: 0 0.35em; border-radius: 3px; border: 1px solid currentColor; }
    .goal .tag, .meta .tag { color: var(--c-hole); }
    .error .tag { color: var(--c-err); }
    .error .msgtext { color: var(--c-err); font-weight: 600; }
    .at-cursor { font-size: 0.75em; color: var(--c-hole); font-style: italic; }
    .goaltype { font-size: 1.15em; margin: 0.2rem 0 0.4rem; }
    .label { font-size: 0.72em; text-transform: uppercase; letter-spacing: 0.06em; color: var(--c-dim); margin-top: 0.35rem; }
    .ctx-entry { padding-left: 0.6rem; }
    .ctx-entry .var { font-weight: 700; }
    .bunch { padding-left: 0.6rem; }
    .modes { font-size: 0.72em; text-transform: none; letter-spacing: 0; margin-left: 0.5rem; }
    .modes span { cursor: pointer; margin-left: 0.4rem; }
    .modes span.on { color: var(--c-hole); font-weight: 700; cursor: default; }
    /* (b) nested boxes: ⊗ lays its children out left to right, "," stacks them */
    .b-tens { display: flex; flex-direction: row; align-items: center; flex-wrap: wrap; gap: 0.25rem; }
    .b-prod { display: flex; flex-direction: column; align-items: flex-start; gap: 0.1rem;
              border: 1px solid var(--c-dim); border-radius: 5px; padding: 0.15rem 0.4rem; }
    .b-tens > .b-prod { border-style: solid; }
    .b-sep { color: var(--c-op); font-weight: 700; padding: 0 0.1rem; }
    .b-leaf { white-space: nowrap; }
    .bunch-root { padding: 0.2rem 0 0.2rem 0.6rem; }
    /* (c) outline */
    .b-outline { padding-left: 0.6rem; white-space: pre; }
    .b-outline .b-op { color: var(--c-op); font-weight: 700; }
    .b-outline .guide { color: var(--c-dim); }
    /* hover relations. These styles must NEVER change the size or position of
       anything (no ::before/::after content, no padding/border/font changes, no
       resizing status line): if the hovered variable moves out from under the
       mouse, mouseout/mouseover fire in an endless loop and the webview freezes. */
    .bv { cursor: default; border-radius: 3px; padding: 0 0.15em; font-weight: 700; }
    .bv.rel-self { outline: 2px solid var(--c-hole); }
    .bv.rel-left { background: color-mix(in srgb, var(--c-type) 30%, transparent); box-shadow: inset 0 -2px 0 var(--c-type); }
    .bv.rel-right { background: color-mix(in srgb, var(--c-const) 30%, transparent); box-shadow: inset 0 -2px 0 var(--c-const); }
    .bv.rel-cart { opacity: 0.45; text-decoration: line-through; }
    .bv.rel-free { background: color-mix(in srgb, var(--c-post) 25%, transparent); }
    .bunch-status { font-size: 0.8em; color: var(--c-dim); margin-top: 0.25rem; height: 2.6em; overflow: hidden; line-height: 1.3em; }
    .bunch-status .l { color: var(--c-type); } .bunch-status .r { color: var(--c-const); } .bunch-status .f { color: var(--c-post); }
    .muted { color: var(--c-dim); font-size: 0.85em; }
    .link { cursor: pointer; color: var(--c-dim); text-decoration: underline dotted; }
    .link:hover { color: var(--c-name); }
    .row { cursor: pointer; padding: 0.1rem 0.4rem; border-radius: 3px; }
    .row:hover { background: var(--c-hover); }
    .row .where { color: var(--c-dim); margin-right: 0.5rem; }
    .section-title { font-size: 0.8rem; font-weight: 600; color: var(--c-dim); margin: 0.6rem 0 0.2rem; }
    .nogoal { color: var(--c-ok); margin-bottom: 0.6rem; }
    .warning { color: var(--c-warn); }
    details { margin: 0.35rem 0; }
    details > summary { cursor: pointer; font-size: 0.85rem; font-weight: 600; color: var(--c-dim); }
    details > summary:hover { color: var(--vscode-foreground); }
    details .inner { padding: 0.2rem 0 0.2rem 0.8rem; }
    details.trace { color: var(--c-dim); font-size: 0.85em; }
    details.trace > summary { font-weight: normal; }
    .decl { margin: 0.1rem 0; }
    .decl .name { color: var(--c-name); font-weight: 700; }
    .postulate .name { color: var(--c-post); font-weight: 700; }
    .t-kw { color: var(--c-kw); font-weight: 600; }
    .t-type { color: var(--c-type); }
    .t-const { color: var(--c-const); }
    .t-op { color: var(--c-op); }
    .t-num { color: var(--c-num); }
    .t-hole { color: var(--c-hole); font-weight: 700; }
  </style>
</head>
<body>
  <div class="header">
    <div class="title">BATT Output</div>
    ${hint}
  </div>
  ${body}
  <script nonce="${nonce}">
    const vscode = acquireVsCodeApi();
    document.addEventListener('click', (event) => {
      const target = event.target.closest('[data-line]');
      if (target) {
        vscode.postMessage({ type: 'reveal', line: Number(target.dataset.line), col: Number(target.dataset.col || 0) });
      }
    });
    // bunch display mode
    document.addEventListener('click', (event) => {
      const m = event.target.closest('[data-bunch-mode]');
      if (m) {
        vscode.postMessage({ type: 'bunchMode', mode: m.dataset.bunchMode });
      }
    });
    // hover a variable: colour every other one by where it can go relative to it.
    // Paths are "id:kind:index/..." from the root (kind t = ⊗, p = ","); the first
    // step where two paths differ is their lowest common ancestor.
    const relation = (p, q) => {
      const a = p.split('/');
      const b = q.split('/');
      let k = 0;
      while (k < a.length && k < b.length && a[k] === b[k]) {
        k++;
      }
      const [, kind, ia] = a[k].split(':');
      const ib = b[k].split(':')[2];
      return kind === 't' ? (Number(ib) < Number(ia) ? 'left' : 'right') : 'cart';
    };
    let pivot;
    const clearRel = () => {
      for (const v of document.querySelectorAll('.bv')) {
        v.classList.remove('rel-self', 'rel-left', 'rel-right', 'rel-cart', 'rel-free');
      }
      const status = document.querySelector('.bunch-status');
      if (status) {
        status.innerHTML = status.dataset.idle || '';
      }
      pivot = undefined;
    };
    document.addEventListener('mouseover', (event) => {
      const v = event.target.closest('.bv');
      if (!v || v === pivot) {
        return;
      }
      clearRel();
      pivot = v;
      const groups = { left: [], right: [], cart: [], free: [] };
      for (const w of document.querySelectorAll('.bv')) {
        if (w.dataset.name === v.dataset.name) {
          w.classList.add('rel-self');
          continue;
        }
        const r = (v.dataset.crisp || w.dataset.crisp) ? 'free' : relation(v.dataset.path, w.dataset.path);
        w.classList.add('rel-' + r);
        if (!groups[r].includes(w.dataset.name)) {
          groups[r].push(w.dataset.name);
        }
      }
      const status = document.querySelector('.bunch-status');
      if (status) {
        const esc = (t) => t.replace(/&/g, '&amp;').replace(/</g, '&lt;');
        const part = (cls, label, names) => names.length ? '<span class="' + cls + '">' + label + '</span> ' + names.map(esc).join(', ') : '';
        const name = esc(v.dataset.name);
        status.innerHTML = v.dataset.crisp
          ? name + ' is crisp: it can be used on either side of any split'
          : [part('l', '◀ left of ' + name + ':', groups.left), part('r', '▶ right of ' + name + ':', groups.right),
             part('', 'cartesian with ' + name + ':', groups.cart), part('f', 'crisp (anywhere):', groups.free)]
              .filter((x) => x).join(' · ') || name + ' is alone in the bunch';
      }
    });
    document.addEventListener('mouseout', (event) => {
      const v = event.target.closest('.bv');
      if (v && !(event.relatedTarget && event.relatedTarget.closest && event.relatedTarget.closest('.bv') === v)) {
        clearRel();
      }
    });
    for (const d of document.querySelectorAll('details[data-key]')) {
      d.addEventListener('toggle', () => vscode.postMessage({ type: 'toggle', key: d.dataset.key, open: d.open }));
    }
  </script>
</body>
</html>`;
  }
}

function activate(context) {
  const provider = new BattOutputViewProvider(context);
  context.subscriptions.push(
    vscode.window.registerWebviewViewProvider('batt.output', provider),
    vscode.commands.registerCommand('batt.refresh', () => provider.refresh()),
    vscode.window.onDidChangeActiveTextEditor((editor) => {
      // focus moving to the panel itself leaves no active editor: keep the output
      if (editor) {
        provider.refresh();
      }
    }),
    vscode.window.onDidChangeTextEditorSelection((event) => {
      if (event.textEditor.document.languageId === 'batt') {
        provider.scheduleCursorRender();
      }
    }),
    vscode.workspace.onDidChangeTextDocument((event) => {
      const editor = vscode.window.activeTextEditor;
      if (!editor || editor.document.uri.toString() !== event.document.uri.toString()) {
        return;
      }
      if (event.document.languageId === 'batt') {
        provider.scheduleRefresh();
      }
    }),
    vscode.workspace.onDidSaveTextDocument((document) => {
      if (document.languageId === 'batt') {
        provider.refresh();
      }
    })
  );
}

function deactivate() {
  for (const pid of runningGroups) {
    killGroup(pid);
  }
  runningGroups.clear();
}

// Move the cursor to a checker position (1-based line, column in code points).
async function revealPosition(uri, line, col) {
  const existing = vscode.window.visibleTextEditors.find((e) => e.document.uri.toString() === uri.toString());
  const document = existing ? existing.document : await vscode.workspace.openTextDocument(uri);
  const lineIndex = Math.max(0, Math.min(document.lineCount - 1, line - 1));
  // the checker counts code points, VS Code counts UTF-16 units (𝕀 is two of them)
  let character = 0;
  let seen = 0;
  for (const ch of document.lineAt(lineIndex).text) {
    if (seen >= col) {
      break;
    }
    character += ch.length;
    seen++;
  }
  const position = new vscode.Position(lineIndex, character);
  await vscode.window.showTextDocument(document, {
    viewColumn: existing ? existing.viewColumn : undefined,
    selection: new vscode.Range(position, position),
    preserveFocus: false
  });
}

function messageHtml(text) {
  return `<pre class="msg">${escapeHtml(text)}</pre>`;
}

// Syntax highlighting of printed terms. Mirrors src/lexer.ml (and the editor
// grammar): identifiers may contain - ' _ digits → ⁻ ₗ ᵣ 𝕀, so they are consumed
// whole before being classified. The printer writes Bool / Unit / Empty for the
// builtin types, and `_` for anonymous binders (not metas, which print as ?n).
const TOKEN_RE = /(𝕀∨|𝕀∧)|(_≃_|(?:[A-Za-z]|𝕀)(?:[A-Za-z0-9'_\-→⁻ₗᵣ]|𝕀)*)|(→ₗ|→ᵣ|⇀|⇁|→)|(⊗|⨂|×|Σ|♭|𝄫|≡|≃|∘|¬|∷)|(λ)|(\?\d*)|(\d+)/gu;
const KEYWORDS = new Set(['let', 'in', 'fun', 'postulate', 'import', 'open']);
const TYPES = new Set(['Type', 'TYPE', 'U', 'Bool', 'Unit', 'Empty', 'bool', 'unit', 'empty', '𝕀']);
const CONSTANTS = new Set(['tt', 'true', 'false', 'refl', '𝕀0', '𝕀1']);
// names the checker always puts in the crisp context
const BUILTIN_NAMES = new Set(['TYPE', 'empty', 'unit', 'bool', 'false', 'true']);

function highlight(text) {
  let out = '';
  let last = 0;
  TOKEN_RE.lastIndex = 0;
  let m;
  while ((m = TOKEN_RE.exec(text)) !== null) {
    out += escapeHtml(text.slice(last, m.index));
    const tok = escapeHtml(m[0]);
    let cls;
    if (m[1] || m[3] || m[4]) {
      cls = 't-op';
    } else if (m[2]) {
      cls = KEYWORDS.has(m[0]) ? 't-kw' : TYPES.has(m[0]) ? 't-type' : CONSTANTS.has(m[0]) ? 't-const' : undefined;
    } else if (m[5]) {
      cls = 't-kw';
    } else if (m[6]) {
      cls = 't-hole';
    } else if (m[7]) {
      cls = 't-num';
    }
    out += cls ? `<span class="${cls}">${tok}</span>` : tok;
    last = m.index + m[0].length;
  }
  return out + escapeHtml(text.slice(last));
}

// "in file F line L characters A-B" → { file, line, col, text }
function parsePos(text) {
  const m = /in file (.*?) line (\d+) characters (\d+)-(\d+)/.exec(text);
  return m ? { file: m[1], line: Number(m[2]), col: Number(m[3]), text: m[0] } : undefined;
}

// Parse the checker's output into errors, goals, metas, postulates and declarations.
function parseOutput(result, runPath, shownName) {
  let text = result.stdout + (result.stderr ? '\n' + result.stderr : '');
  if (runPath) {
    // show the real file name instead of the temporary .batt-live-… copy
    text = text.split(runPath).join(shownName);
  }
  const lines = text.replace(/\r/g, '').split('\n');

  const model = {
    code: result.code,
    file: shownName,
    errors: [],
    holes: [],
    metas: [],
    warnings: [],
    notes: [],
    postulates: [],
    ownDecls: [],
    importedDecls: [],
    other: []
  };
  const globals = new Set(BUILTIN_NAMES);
  // `M = import M` opens M's own output, which ends with M's re-exports `x = M.x`
  const importStack = [];
  let lastDecl;
  let i = 0;

  const readBlock = () => {
    const block = [];
    while (i < lines.length && lines[i].trim() !== '') {
      block.push(lines[i++]);
    }
    return block;
  };

  while (i < lines.length) {
    const line = lines[i++];
    let m;
    if (line.trim() === '' || line === 'Welcome to BATT!' || /^Checking .*\.\.\.$/.test(line)) {
      continue;
    }
    if ((m = /^DECL  (\S+) = (.*)$/.exec(line))) {
      const name = m[1];
      const body = m[2];
      globals.add(name);
      const reexportOf = /^([A-Z][A-Za-z_-]*)\.(\S+)$/.exec(body.split(' ')[0]);
      const decl = { name, body };
      if (body.startsWith('import ')) {
        importStack.push(name);
        model.importedDecls.push(decl);
      } else if (reexportOf && reexportOf[2] === name && importStack.includes(reexportOf[1])) {
        // the re-exports of M close M's block (and anything left open inside it)
        while (importStack.length && importStack.pop() !== reexportOf[1]) {
          // unwind
        }
        model.importedDecls.push(decl);
      } else if (reexportOf && reexportOf[2] === name) {
        model.importedDecls.push(decl);
      } else {
        decl.own = importStack.length === 0;
        (decl.own ? model.ownDecls : model.importedDecls).push(decl);
      }
      lastDecl = decl;
    } else if ((m = /^POSTULATE (\d+) (.*)$/.exec(line))) {
      // the postulate's name is on the DECL line just before
      model.postulates.push({
        n: m[1],
        type: m[2],
        name: lastDecl && lastDecl.body.startsWith('postulate') ? lastDecl.name : undefined,
        own: importStack.length === 0
      });
    } else if ((m = /^HOLE (.*?) : (.*) IN$/.exec(line))) {
      const context = readBlock();
      // the last line is the bunch; the crisp context lists globals first, then locals
      const bunch = context.length && context[context.length - 1].startsWith('(') ? context.pop() : undefined;
      const entries = context.map((l) => {
        const k = l.indexOf(' : ');
        return k < 0 ? { name: '', type: l } : { name: l.slice(0, k), type: l.slice(k + 3) };
      });
      let firstLocal = 0;
      while (firstLocal < entries.length && globals.has(entries[firstLocal].name)) {
        firstLocal++;
      }
      model.holes.push({
        pos: parsePos(m[1]),
        posText: m[1],
        goal: m[2],
        locals: entries.slice(firstLocal),
        hiddenGlobals: firstLocal,
        bunch
      });
    } else if (line === 'UNSOLVED META') {
      for (const l of readBlock()) {
        const mm = /^- (\?\d+)/.exec(l);
        model.metas.push({ name: mm ? mm[1] : l, pos: parsePos(l), text: l });
      }
    } else if ((m = /^Error: (.*)$/.exec(line))) {
      const error = { message: m[1], pos: parsePos(m[1]), trace: [] };
      while (i < lines.length && (lines[i].trim() === '' || /^(Raised at|Called from|Re-raised at|Raised by primitive operation at) /.test(lines[i]))) {
        if (lines[i].trim() !== '') {
          error.trace.push(lines[i]);
        }
        i++;
      }
      model.errors.push(error);
    } else if (/^\d+ unsolved unification problems:$/.test(line)) {
      model.warnings.push([line].concat(readBlock()).join('\n'));
    } else if (/apparently already imported/.test(line) || /^Include .*\.\.\.$/.test(line)) {
      // routine messages when importing (e.g. the diamond imports of Stdlib)
      model.notes.push(line);
    } else {
      model.other.push(line);
    }
  }
  return model;
}

function pluralise(n, word) {
  return `${n} ${word}${n === 1 ? '' : 's'}`;
}

// data-line/data-col make an element clickable (the script sends a "reveal" message)
function jumpAttrs(pos) {
  return pos ? ` data-line="${pos.line}" data-col="${pos.col}" title="Go to line ${pos.line}"` : '';
}

// `inner` is a function, only called when the section is open: large sections
// (thousands of imported declarations) cost nothing while folded
function details(key, title, inner, openState, extraClass) {
  const open = openState[key];
  return `<details data-key="${escapeHtml(key)}"${open ? ' open' : ''}${extraClass ? ` class="${extraClass}"` : ''}><summary>${title}</summary><div class="inner">${open ? inner() : ''}</div></details>`;
}

function renderDecl(d, cls) {
  return `<div class="${cls || 'decl'} code"><span class="name">${escapeHtml(d.name)}</span> = ${highlight(d.body)}</div>`;
}

// Parse a bunch as printed by Bunch.to_string (src/lang.ml):
//   ()  |  x:A  |  (l,r)  |  (l⊗r)
// Separators are printed without spaces and types keep their own brackets, so a
// leaf's type ends at the first `,` `⊗` or `)` outside brackets. Returns null on
// anything unexpected (the caller then shows the raw string).
function parseBunch(text) {
  let i = 0;
  const fail = () => {
    throw new Error('bunch');
  };
  const parse = () => {
    if (text.startsWith('()', i)) {
      i += 2;
      return { kind: 'empty' };
    }
    if (text[i] === '(') {
      i++;
      const left = parse();
      const sep = text[i];
      if (sep !== ',' && sep !== '⊗') {
        fail();
      }
      i++;
      const right = parse();
      if (text[i] !== ')') {
        fail();
      }
      i++;
      return { kind: sep === '⊗' ? 't' : 'p', children: [left, right] };
    }
    const colon = text.indexOf(':', i);
    if (colon < 0) {
      fail();
    }
    const name = text.slice(i, colon);
    if (!/^\S+$/.test(name) || /[(),⊗]/.test(name)) {
      fail();
    }
    let j = colon + 1;
    let depth = 0;
    for (; j < text.length; j++) {
      const c = text[j];
      if (c === '(' || c === '[' || c === '{') {
        depth++;
      } else if (c === ')' || c === ']' || c === '}') {
        if (depth === 0) {
          break;
        }
        depth--;
      } else if (depth === 0 && (c === ',' || c === '⊗')) {
        break;
      }
    }
    const type = text.slice(colon + 1, j);
    if (!type) {
      fail();
    }
    i = j;
    return { kind: 'var', name, type };
  };
  try {
    const tree = parse();
    return i === text.length ? tree : null;
  } catch (error) {
    return null;
  }
}

// Up to the unit and associativity laws of ⪯: drop ⋄ and flatten nested nodes of
// the same kind. Order is kept (⊗ has no exchange). Returns null for an empty bunch.
function normaliseBunch(node) {
  if (node.kind === 'empty') {
    return null;
  }
  if (node.kind === 'var') {
    return node;
  }
  const children = [];
  for (const c of node.children.map(normaliseBunch)) {
    if (!c) {
      continue;
    }
    if (c.kind === node.kind) {
      children.push(...c.children);
    } else {
      children.push(c);
    }
  }
  if (children.length === 0) {
    return null;
  }
  return children.length === 1 ? children[0] : { kind: node.kind, children };
}

function bunchStats(node) {
  if (node.kind === 'var') {
    return { depth: 0, leaves: 1 };
  }
  const stats = node.children.map(bunchStats);
  return {
    depth: 1 + Math.max(...stats.map((x) => x.depth)),
    leaves: stats.reduce((n, x) => n + x.leaves, 0)
  };
}

// label every node with an id, and every leaf with its path from the root
function annotateBunch(node) {
  let next = 0;
  const walk = (n, pathSoFar) => {
    if (n.kind === 'var') {
      n.path = pathSoFar.join('/');
      return;
    }
    n.id = next++;
    n.children.forEach((c, k) => walk(c, pathSoFar.concat(`${n.id}:${n.kind}:${k}`)));
  };
  walk(node, []);
}

function renderLeaf(n) {
  return `<span class="bv" data-name="${escapeHtml(n.name)}" data-path="${escapeHtml(n.path)}">${escapeHtml(n.name)}</span> : ${highlight(n.type)}`;
}

// (b): ⊗ = row, left to right; "," = stacked box
function renderBoxes(n) {
  if (n.kind === 'var') {
    return `<div class="b-leaf code">${renderLeaf(n)}</div>`;
  }
  if (n.kind === 't') {
    return `<div class="b-tens">${n.children.map(renderBoxes).join('<span class="b-sep">⊗</span>')}</div>`;
  }
  return `<div class="b-prod">${n.children.map(renderBoxes).join('')}</div>`;
}

// (c): indented outline
function renderOutline(n) {
  const lines = [];
  const walk = (node, prefix, isLast, isRoot) => {
    const branch = isRoot ? '' : (isLast ? '└ ' : '├ ');
    const head = node.kind === 'var' ? renderLeaf(node) : `<span class="b-op">${node.kind === 't' ? '⊗' : ','}</span>`;
    lines.push(`<span class="guide">${escapeHtml(prefix + branch)}</span>${head}`);
    if (node.kind !== 'var') {
      const childPrefix = isRoot ? '' : prefix + (isLast ? '  ' : '│ ');
      node.children.forEach((c, k) => walk(c, childPrefix, k === node.children.length - 1, false));
    }
  };
  walk(n, '', true, true);
  return `<div class="b-outline code">${lines.join('\n')}</div>`;
}

// boxes get hard to read when deeply nested or large: switch to the outline then
const BOXES_MAX_DEPTH = 4;
const BOXES_MAX_LEAVES = 16;

function renderBunchSection(raw, mode) {
  const tree = parseBunch(raw);
  const norm = tree && normaliseBunch(tree);
  const modes = ['auto', 'boxes', 'outline', 'raw'];
  let shown = mode || 'auto';
  let body;
  if (!tree) {
    shown = 'raw';
    body = `<div class="bunch code">${highlight(raw)}</div><div class="muted">(could not parse the bunch, shown as printed)</div>`;
  } else if (shown === 'raw') {
    body = `<div class="bunch code">${highlight(raw)}</div>`;
  } else if (!norm) {
    body = '<div class="bunch muted">empty (⋄)</div>';
  } else {
    annotateBunch(norm);
    const stats = bunchStats(norm);
    const useOutline = shown === 'outline' || (shown === 'auto' && (stats.depth > BOXES_MAX_DEPTH || stats.leaves > BOXES_MAX_LEAVES));
    body = `<div class="bunch-root">${useOutline ? renderOutline(norm) : renderBoxes(norm)}</div>`;
  }
  const switcher = modes
    .map((m) => `<span class="${m === (mode || 'auto') ? 'on' : ''}" data-bunch-mode="${m}">${m}</span>`)
    .join('');
  const idle = norm ? 'hover a variable to see where it can go relative to the others' : '';
  return `<div class="label">Bunch<span class="modes">${switcher}</span></div>${body}` +
    (norm && shown !== 'raw' ? `<div class="bunch-status" data-idle="${escapeHtml(idle)}">${escapeHtml(idle)}</div>` : '');
}

// the current goal: the hole on the cursor's line, else the nearest one above it,
// else the first one (holes of imported files come last)
function currentHole(model, cursorLine) {
  const here = model.holes.filter((h) => h.pos && h.pos.file === model.file).sort((a, b) => a.pos.line - b.pos.line || a.pos.col - b.pos.col);
  if (!here.length) {
    return model.holes[0];
  }
  let current = here[0];
  if (cursorLine !== undefined) {
    for (const h of here) {
      if (h.pos.line <= cursorLine) {
        current = h;
      }
    }
  }
  return current;
}

// what a cursor move can change in the rendering
function cursorKey(model, cursorLine) {
  const h = currentHole(model, cursorLine);
  return h ? `${model.holes.indexOf(h)}:${h.pos && h.pos.line === cursorLine}` : '';
}

function renderModel(model, cursorLine, openState, bunchMode) {
  const inFile = (pos) => pos && pos.file === model.file;
  const holesHere = model.holes.filter((h) => inFile(h.pos)).sort((a, b) => a.pos.line - b.pos.line || a.pos.col - b.pos.col);
  const holesElsewhere = model.holes.filter((h) => !inFile(h.pos));
  const out = [];

  // summary chips
  const chips = [];
  if (model.code !== 0) {
    chips.push(`<span class="chip bad">✗ failed (exit ${model.code})</span>`);
  } else if (model.holes.length || model.metas.length) {
    chips.push('<span class="chip holey">◐ checked, incomplete</span>');
  } else {
    chips.push('<span class="chip ok">✓ checked</span>');
  }
  if (model.holes.length) {
    chips.push(`<span class="chip hole">${pluralise(model.holes.length, 'goal')}</span>`);
  }
  if (model.metas.length) {
    chips.push(`<span class="chip hole">${pluralise(model.metas.length, 'unsolved meta')}</span>`);
  }
  if (model.postulates.length) {
    const own = model.postulates.filter((p) => p.own).length;
    chips.push(`<span class="chip post">${pluralise(model.postulates.length, 'postulate')}${own ? ` (${own} here)` : ''}</span>`);
  }
  chips.push(`<span class="chip decl">${pluralise(model.ownDecls.length, 'declaration')}</span>`);
  if (model.warnings.length) {
    chips.push(`<span class="chip warn">${pluralise(model.warnings.length, 'warning')}</span>`);
  }
  out.push(`<div class="summary">${chips.join('')}</div>`);

  // errors first
  model.errors.forEach((error, k) => {
    const where = error.pos ? `<span class="link"${jumpAttrs(error.pos)}>line ${error.pos.line}</span>` : '';
    const trace = error.trace.length
      ? details(`trace-${k}`, `OCaml backtrace (${error.trace.length} lines)`, () => `<div class="code">${error.trace.map(escapeHtml).join('\n')}</div>`, openState, 'trace')
      : '';
    out.push(`<div class="card error"><div class="card-head"><span class="tag">ERROR</span>${where}</div><div class="code msgtext">${highlight(error.message)}</div>${trace}</div>`);
  });

  const current = currentHole(model, cursorLine);

  if (current) {
    const atCursor = current.pos && current.pos.line === cursorLine && inFile(current.pos) ? '<span class="at-cursor">at cursor</span>' : '';
    const where = inFile(current.pos)
      ? `<span class="link"${jumpAttrs(current.pos)}>line ${current.pos.line}</span>`
      : `<span class="muted">${escapeHtml(current.posText)}</span>`;
    const locals = current.locals.map((e) => `<div class="ctx-entry code"><span class="var bv" data-crisp="1" data-name="${escapeHtml(e.name)}">${escapeHtml(e.name)}</span> : ${highlight(e.type)}</div>`).join('');
    const hidden = current.hiddenGlobals ? `<div class="muted">+ ${pluralise(current.hiddenGlobals, 'global name')} in scope (hidden)</div>` : '';
    out.push(`<div class="card goal">
      <div class="card-head"><span class="tag">GOAL</span>${where}${atCursor}</div>
      <div class="goaltype code">${highlight(current.goal)}</div>
      ${locals ? `<div class="label">Crisp context</div>${locals}` : ''}
      ${current.bunch ? renderBunchSection(current.bunch, bunchMode) : ''}
      ${hidden}
    </div>`);
  } else if (!model.errors.length) {
    out.push(model.metas.length ? '' : '<div class="nogoal">✓ No open goals.</div>');
  }

  const others = holesHere.filter((h) => h !== current);
  if (others.length) {
    out.push(`<div class="section-title">Other goals</div>`);
    for (const h of others) {
      out.push(`<div class="row code"${jumpAttrs(h.pos)}><span class="where">line ${h.pos.line}</span>${highlight(h.goal)}</div>`);
    }
  }
  const elsewhere = holesElsewhere.filter((h) => h !== current);
  if (elsewhere.length) {
    out.push(`<div class="section-title">Goals in imported files</div>`);
    for (const h of elsewhere) {
      out.push(`<div class="row code"><span class="where">${escapeHtml(h.posText)}</span>${highlight(h.goal)}</div>`);
    }
  }

  if (model.metas.length) {
    out.push(`<div class="section-title">Unsolved metas</div>`);
    for (const meta of model.metas) {
      const where = meta.pos ? (inFile(meta.pos) ? `line ${meta.pos.line}` : escapeHtml(meta.pos.text)) : '';
      out.push(`<div class="row code meta"${inFile(meta.pos) ? jumpAttrs(meta.pos) : ''}><span class="where">${where}</span><span class="t-hole">${escapeHtml(meta.name)}</span></div>`);
    }
  }

  for (const w of model.warnings) {
    out.push(`<div class="warning code">⚠ ${escapeHtml(w)}</div>`);
  }
  if (model.other.length) {
    out.push(`<div class="code">${model.other.map(highlight).join('\n')}</div>`);
  }

  // folded sections
  if (model.postulates.length) {
    const rows = () => model.postulates
      .slice()
      .sort((a, b) => (b.own ? 1 : 0) - (a.own ? 1 : 0))
      .map((p) => `<div class="postulate code"><span class="name">${escapeHtml(p.name || `#${p.n}`)}</span>${p.own ? ' <span class="muted">(this file)</span>' : ''} : ${highlight(p.type)}</div>`)
      .join('');
    out.push(details('postulates', `Postulates (${model.postulates.length})`, rows, openState));
  }
  if (model.ownDecls.length) {
    out.push(details('own-decls', `Declarations in this file (${model.ownDecls.length})`, () => model.ownDecls.map((d) => renderDecl(d)).join(''), openState));
  }
  if (model.importedDecls.length) {
    out.push(details('imported-decls', `From imports (${model.importedDecls.length})`, () => model.importedDecls.map((d) => renderDecl(d)).join(''), openState));
  }

  if (model.notes.length) {
    out.push(details('notes', `Checker notes (${model.notes.length})`, () => `<div class="code muted">${model.notes.map(escapeHtml).join('\n')}</div>`, openState));
  }

  return out.join('\n');
}

// Process groups of checker runs still alive, killed on deactivation.
const runningGroups = new Set();

function killGroup(pid) {
  try {
    process.kill(-pid, 'SIGKILL');
  } catch (error) {
    void error; // already gone
  }
}

// Run the checker with hard limits. A checker bug (for instance a unification that
// never terminates and keeps allocating) must never be able to take the machine
// down: the memory and CPU caps are enforced by the kernel (they hold even if VS Code
// dies), the wall-clock and output caps by us, and the checker runs in its own
// process group so that the whole chain (batt wrapper, dune exec, batt.exe) is killed.
function runBatt(workspaceRoot, fileName) {
  const config = vscode.workspace.getConfiguration('batt');
  const timeoutSeconds = Math.max(1, config.get('timeoutSeconds', 60));
  const memoryLimitMB = Math.max(0, config.get('memoryLimitMB', 4096));
  const maxOutputBytes = Math.max(1, config.get('maxOutputMB', 64)) * 1024 * 1024;
  const limits = [`ulimit -t ${Math.ceil(timeoutSeconds * 2)}`];
  if (memoryLimitMB > 0) {
    limits.push(`ulimit -v ${Math.floor(memoryLimitMB) * 1024}`);
  }
  const script = `${limits.map((l) => `${l} 2>/dev/null`).join('; ')}; exec batt --no-colors "$1"`;

  return new Promise((resolve, reject) => {
    const child = cp.spawn('/bin/sh', ['-c', script, 'batt', fileName], {
      cwd: workspaceRoot,
      detached: true,
      stdio: ['ignore', 'pipe', 'pipe']
    });
    runningGroups.add(child.pid);
    const stdout = [];
    const stderr = [];
    let size = 0;
    let stopped;
    const stop = (reason) => {
      if (!stopped) {
        stopped = reason;
        killGroup(child.pid);
      }
    };
    const collect = (chunks) => (chunk) => {
      size += chunk.length;
      if (size > maxOutputBytes) {
        stop('output');
        return;
      }
      chunks.push(chunk);
    };
    child.stdout.on('data', collect(stdout));
    child.stderr.on('data', collect(stderr));
    const timer = setTimeout(() => stop('timeout'), timeoutSeconds * 1000);

    child.on('error', (error) => {
      clearTimeout(timer);
      runningGroups.delete(child.pid);
      reject(error);
    });
    child.on('close', (code, signal) => {
      clearTimeout(timer);
      killGroup(child.pid); // no stragglers
      runningGroups.delete(child.pid);
      const out = Buffer.concat(stdout).toString('utf8');
      const err = Buffer.concat(stderr).toString('utf8');
      if (!stopped && code !== 0 && /allocation failure|Out of memory|Stack overflow/i.test(out + err)) {
        stopped = 'memory';
      } else if (!stopped && signal === 'SIGXCPU') {
        stopped = 'timeout';
      }
      resolve({
        code: typeof code === 'number' ? code : 1,
        stdout: out,
        stderr: err,
        stopped,
        limits: { timeoutSeconds, memoryLimitMB, maxOutputMB: maxOutputBytes / (1024 * 1024) }
      });
    });
  });
}

function stoppedMessage(result, name) {
  const l = result.limits;
  const why = {
    memory: `it ran out of memory (limit: ${l.memoryLimitMB} MB)`,
    timeout: `it did not finish within ${l.timeoutSeconds} s`,
    output: `it produced more than ${l.maxOutputMB} MB of output`
  }[result.stopped];
  return `batt was stopped on ${name}: ${why}.\n\n` +
    'This usually means the checker is looping, for instance while unifying a term that is stuck on a hole ' +
    '(a definition used by a later `refl` whose body is `?`). Your machine is protected: the run was killed.\n\n' +
    'The limits can be changed in the settings batt.memoryLimitMB, batt.timeoutSeconds and batt.maxOutputMB.';
}

function escapeHtml(value) {
  return value
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

module.exports = {
  activate,
  deactivate
};
