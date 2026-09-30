// Go to definition for BATT files (Ctrl+hover preview, Ctrl+click jump).
//
// This is a purely syntactic approximation of name resolution, independent of the
// checker: a tokenizer mirroring src/lexer.ml, top-level items split on unindented
// lines, a scope analysis of local binders, and top-level names followed through
// `import M` / `open import M` / `open M` (a module exports its own definitions and,
// transitively, the fields of the modules it opens), as in `check_decls`.

const fs = require('fs');
const path = require('path');

// ---------------------------------------------------------------- tokenizer

// Literal tokens of src/lexer.ml, in rule order (on equal length the first one wins,
// and every literal wins against an identifier of the same length).
const LITERALS = [
  ['Type', 'KW'], ['U', 'KW'], ['⊥', 'KW'], ['\\bot', 'KW'], ['⊤', 'KW'], ['\\top', 'KW'],
  ['tt', 'KW'], ['false', 'KW'], ['true', 'KW'],
  ['∷', 'CCOLON'], ['::', 'CCOLON'], [':', 'COLON'], ['=', 'EQ'], ['?', 'KW'],
  ['()', 'LRPAR'], ['(', 'LPAR'], [')', 'RPAR'], ['{', 'LACC'], ['}', 'RACC'],
  [',', 'COMMA'], ['.', 'DOT'],
  ['→', 'TO'], ['->', 'TO'], ['\\to', 'TO'],
  ['→ₗ', 'TO'], ['⇀', 'TO'], ['->l', 'TO'], ['\\tol', 'TO'],
  ['→ᵣ', 'TO'], ['⇁', 'TO'], ['->r', 'TO'], ['\\tor', 'TO'],
  ['λ', 'FUN'], ['fun', 'FUN'], ['ρ', 'FUN'], ['∂', 'FUN'],
  ['Σ', 'SIGMA'], ['\\Sigma', 'SIGMA'], ['×', 'KW'], ['\\times', 'KW'],
  ['⨂', 'KW'], ['\\bigotimes', 'KW'], ['⊗', 'KW'], ['\\otimes', 'KW'],
  ['♭', 'KW'], ['\\flat', 'KW'], ['𝄫', 'KW'], ['\\fflat', 'KW'],
  ['≡', 'KW'], ['\\equiv', 'KW'],
  // infix sugar: the operator stands for the named identifier
  ['≃', 'OP', '_≃_'], ['\\simeq', 'OP', '_≃_'], ['≤', 'OP', 'leq'], ['≥', 'OP', 'geq'],
  ['∘', 'OP', 'circ'], ['\\circ', 'OP', 'circ'], ['∨', 'OP', 'or'], ['¬', 'OP', 'not'],
  ['ℕ', 'KW'], ['Nat', 'KW'], ['zero', 'KW'], ['succ', 'KW'],
  ['𝕀0', 'KW'], ['II0', 'KW'], ['𝕀1', 'KW'], ['II1', 'KW'], ['𝕀∨', 'KW'], ['IIv', 'KW'],
  ['𝕀∧', 'KW'], ['IIw', 'KW'], ['𝕀', 'KW'], ['II', 'KW'],
  ['_', 'KW'], ['refl', 'KW'], ['let', 'LET'], ['in', 'IN'],
  ['postulate', 'POSTULATE'], ['open', 'OPEN']
];

const isGreek = (c) => (c >= 0x391 && c <= 0x3A1) || (c >= 0x3A3 && c <= 0x3A9)
  || (c >= 0x3B1 && c <= 0x3BA) || (c >= 0x3BC && c <= 0x3C9);
const isLetter = (c) => (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || isGreek(c);
const isDigit = (c) => c >= 48 && c <= 57;
const IDENT_EXTRA = new Set(['\'', '-', '_', '→', '⁻', 'ₗ', 'ᵣ', '𝕀', '≡'].map((s) => s.codePointAt(0)));
const DOUBLE_STRUCK_I = '𝕀'.codePointAt(0);

// Length (in UTF-16 units) of the identifier starting at `pos` (0 if none), following
// the IDENT rule of src/lexer.ml.
function matchIdent(text, pos) {
  const first = text.codePointAt(pos);
  if (first === undefined || !(isLetter(first) || first === DOUBLE_STRUCK_I)) {
    return 0;
  }
  let i = pos + (first > 0xFFFF ? 2 : 1);
  while (i < text.length) {
    const c = text.codePointAt(i);
    if (!(isLetter(c) || isDigit(c) || IDENT_EXTRA.has(c))) {
      break;
    }
    i += c > 0xFFFF ? 2 : 1;
  }
  return i - pos;
}

function matchImport(text, pos) {
  if (!text.startsWith('import ', pos)) {
    return 0;
  }
  let i = pos + 7;
  while (i < text.length) {
    const c = text.codePointAt(i);
    if (!(isLetter(c) || c === 45 || c === 95)) {
      break;
    }
    i += c > 0xFFFF ? 2 : 1;
  }
  return i - pos;
}

// Tokens carry their line and UTF-16 columns (what VS Code positions use).
// Newlines followed by a space are continuations (skipped, as in the lexer);
// other newlines become NL tokens, which end top-level items.
function tokenize(text) {
  const tokens = [];
  let pos = 0;
  let line = 0;
  let lineStart = 0;
  const push = (type, len, extra) => {
    tokens.push(Object.assign({ type, text: text.substr(pos, len), line, col: pos - lineStart, end: pos - lineStart + len }, extra));
  };
  while (pos < text.length) {
    const ch = text[pos];
    if (ch === '\n') {
      if (text[pos + 1] !== ' ') {
        push('NL', 1);
      }
      pos++;
      line++;
      lineStart = pos;
      continue;
    }
    if (ch === ' ' || ch === '\t' || ch === '\r') {
      pos++;
      continue;
    }
    if (text.startsWith('--', pos)) {
      const nl = text.indexOf('\n', pos);
      pos = nl < 0 ? text.length : nl;
      continue;
    }
    // longest match; ties go to the earlier rule
    let best = { len: 0 };
    const imp = matchImport(text, pos);
    if (imp > best.len) {
      best = { len: imp, type: 'IMPORT' };
    }
    for (const [lit, type, name] of LITERALS) {
      if (lit.length > best.len && text.startsWith(lit, pos)) {
        best = { len: lit.length, type, name };
      }
    }
    let digits = 0;
    while (isDigit(text.charCodeAt(pos + digits))) {
      digits++;
    }
    if (digits > best.len) {
      best = { len: digits, type: 'INT' };
    }
    const id = text.startsWith('_≃_', pos) ? 3 : matchIdent(text, pos);
    if (id > best.len) {
      best = { len: id, type: 'IDENT' };
    }
    if (best.len === 0) {
      const c = text.codePointAt(pos);
      best = { len: c > 0xFFFF ? 2 : 1, type: 'OTHER' };
    }
    if (best.type === 'IMPORT') {
      push('IMPORT', best.len, { module: text.substr(pos + 7, best.len - 7) });
    } else if (best.type === 'OP') {
      push('OP', best.len, { name: best.name });
    } else {
      push(best.type, best.len);
    }
    pos += best.len;
  }
  return tokens;
}

// ---------------------------------------------------------------- parsing

const isColon = (t) => t && (t.type === 'COLON' || t.type === 'CCOLON');
const OPENERS = { LPAR: 'RPAR', LACC: 'RACC' };

// Split into top-level items, find definitions (signature, then its clauses) and
// module-level imports / opens.
function parseModule(text, file) {
  const tokens = tokenize(text);
  const lines = text.split('\n');
  const items = [];
  let start = 0;
  for (let i = 0; i <= tokens.length; i++) {
    if (i === tokens.length || tokens[i].type === 'NL') {
      if (i > start) {
        items.push({ start, end: i });
      }
      start = i + 1;
    }
  }

  let current;   // definition whose clauses are being read
  for (const item of items) {
    const t = (k) => tokens[item.start + k];
    item.firstLine = t(0).line;
    item.lastLine = tokens[item.end - 1].line;
    if (t(0).type === 'POSTULATE' && t(1) && t(1).type === 'IDENT' && isColon(t(2))) {
      item.def = current = newDef(tokens, file, lines, item, item.start + 1, 'postulate');
    } else if (t(0).type === 'IDENT' && isColon(t(1))) {
      item.def = current = newDef(tokens, file, lines, item, item.start, 'definition');
    } else if (t(0).type === 'IDENT') {
      // a clause: continues the definition above, or defines the name on its own
      if (current && current.name === t(0).text) {
        current.lastLine = item.lastLine;
      } else {
        item.def = current = newDef(tokens, file, lines, item, item.start, 'definition');
      }
      item.clause = true;
    } else if (t(0).type === 'IMPORT') {
      item.imports = t(0).module;
      current = undefined;
    } else if (t(0).type === 'OPEN' && t(1) && t(1).type === 'IMPORT') {
      item.imports = t(1).module;
      item.opens = { module: t(1).module };
      current = undefined;
    } else if (t(0).type === 'OPEN' && t(1) && t(1).type === 'IDENT') {
      item.opens = { qualified: item.start + 1 };
      current = undefined;
    } else {
      current = undefined;
    }
  }
  return { file, text, lines, tokens, items };
}

function newDef(tokens, file, lines, item, nameIndex, kind) {
  // comment lines right above the item document it
  let docLine = item.firstLine;
  while (docLine > 0 && /^--/.test(lines[docLine - 1])) {
    docLine--;
  }
  return { kind, file, name: tokens[nameIndex].text, nameIndex, docLine, firstLine: item.firstLine, sigLastLine: item.lastLine, lastLine: item.lastLine };
}

// Local binders of an item: clause patterns, λ-patterns, (x y : A) / {x ∷ A}
// groups (Π, Σ) and let. Each binder gets a scope [from, to] of token indices.
function localBinders(mod, item) {
  const { tokens } = mod;
  const { start, end } = item;
  // innermost enclosing bracket group of every token: its closing index
  const closing = new Array(end).fill(end - 1);
  const stack = [];
  const matching = {};
  for (let i = start; i < end; i++) {
    const t = tokens[i];
    closing[i] = stack.length ? stack[stack.length - 1].close : end - 1;
    if (OPENERS[t.type]) {
      // find where it closes (for the scope of the binders inside)
      let depth = 0;
      let j = i;
      for (; j < end; j++) {
        if (OPENERS[tokens[j].type]) depth++;
        else if (tokens[j].type === 'RPAR' || tokens[j].type === 'RACC') {
          if (--depth === 0) break;
        }
      }
      matching[i] = Math.min(j, end - 1);
      stack.push({ close: matching[i] });
    } else if ((t.type === 'RPAR' || t.type === 'RACC') && stack.length) {
      stack.pop();
    }
  }
  const binders = [];
  const bind = (i, from, to) => binders.push({ index: i, name: tokens[i].text, from, to });

  // clause patterns scope over the body
  if (item.clause) {
    let eq = start + 1;
    while (eq < end && tokens[eq].type !== 'EQ') eq++;
    for (let i = start + 1; i < eq; i++) {
      if (tokens[i].type === 'IDENT') bind(i, eq, end - 1);
    }
  }
  for (let i = start; i < end; i++) {
    const t = tokens[i];
    if (t.type === 'FUN') {
      // patterns up to `.` or `→` at the same depth
      let depth = 0;
      let j = i + 1;
      const idents = [];
      for (; j < end; j++) {
        const u = tokens[j];
        if (OPENERS[u.type]) depth++;
        else if (u.type === 'RPAR' || u.type === 'RACC') { if (--depth < 0) break; }
        else if (depth === 0 && (u.type === 'DOT' || u.type === 'TO')) break;
        else if (u.type === 'IDENT') idents.push(j);
      }
      idents.forEach((k) => bind(k, j, closing[i]));
    } else if (OPENERS[t.type]) {
      let j = i + 1;
      while (j < end && tokens[j].type === 'IDENT') j++;
      if (j > i + 1 && isColon(tokens[j])) {
        for (let k = i + 1; k < j; k++) bind(k, j, closing[i]);
      }
    } else if (t.type === 'LET' && tokens[i + 1] && tokens[i + 1].type === 'IDENT') {
      bind(i + 1, i + 2, closing[i]);
    }
  }
  return binders;
}

// ---------------------------------------------------------------- resolution

class Resolver {
  // `readFile(file)` returns the current text of a file (open editor or disk), or undefined.
  constructor(root, readFile) {
    this.root = root;
    this.readFile = readFile;
    this.cache = new Map();     // file -> { text, mod }
    this.memo = new Map();      // per request: `${file}\0${name}` -> result
  }

  module(file) {
    const text = this.readFile(file);
    if (text === undefined) {
      return undefined;
    }
    const cached = this.cache.get(file);
    if (cached && cached.text === text) {
      return cached.mod;
    }
    const mod = parseModule(text, file);
    this.cache.set(file, { text, mod });
    return mod;
  }

  // same search path as the checker run from the workspace root: ., graytt, stdlib
  findModule(name) {
    for (const dir of [this.root, path.join(this.root, 'graytt'), path.join(this.root, 'stdlib')]) {
      const file = path.join(dir, name + '.batt');
      if (fs.existsSync(file)) {
        return file;
      }
    }
    return undefined;
  }

  // What `name` denotes at item `itemIndex` (inclusive) of `mod`, looking backwards
  // through the definitions and the opened modules.
  lookupAt(mod, itemIndex, name) {
    for (let k = itemIndex; k >= 0; k--) {
      const item = mod.items[k];
      if (item.def && item.def.name === name) {
        return { kind: 'def', mod, def: item.def };
      }
      if (item.opens) {
        const target = item.opens.module !== undefined
          ? this.findModule(item.opens.module)
          : this.moduleOf(this.qualified(mod, k, item.opens.qualified));
        if (target) {
          const found = this.lookupExport(target, name);
          if (found) {
            return found;
          }
        }
      }
      if (item.imports === name) {
        const file = this.findModule(name);
        return file ? { kind: 'module', file, name } : undefined;
      }
    }
    return undefined;
  }

  lookupExport(file, name) {
    const key = `${file}\0${name}`;
    if (this.memo.has(key)) {
      return this.memo.get(key);
    }
    this.memo.set(key, undefined);   // guards against import cycles
    const mod = this.module(file);
    const found = mod ? this.lookupAt(mod, mod.items.length - 1, name) : undefined;
    this.memo.set(key, found);
    return found;
  }

  moduleOf(found) {
    return found && found.kind === 'module' ? found.file : undefined;
  }

  // Resolve the identifier at token `index` of item `itemIndex`, following `A.B.x`.
  qualified(mod, itemIndex, index) {
    const { tokens } = mod;
    const t = tokens[index];
    const dot = tokens[index - 1];
    const prev = tokens[index - 2];
    if (dot && dot.type === 'DOT' && prev && prev.type === 'IDENT'
        && dot.line === t.line && dot.end === t.col && prev.end === dot.col && prev.line === t.line) {
      const container = this.moduleOf(this.qualified(mod, itemIndex, index - 2));
      if (container) {
        return this.lookupExport(container, t.text);
      }
    }
    return this.lookupAt(mod, itemIndex, t.text);
  }

  // Entry point: definition of the name under (line, character) in `file`.
  // Returns { origin, target } with ranges as {line, col, endLine?, endCol}.
  definition(file, line, character) {
    this.memo = new Map();
    const mod = this.module(file);
    if (!mod) {
      return undefined;
    }
    const { tokens } = mod;
    const index = tokens.findIndex((t) => t.line === line && t.col <= character && character < t.end);
    if (index < 0) {
      return undefined;
    }
    const tok = tokens[index];
    const itemIndex = mod.items.findIndex((it) => it.start <= index && index < it.end);
    const item = mod.items[itemIndex];

    if (tok.type === 'IMPORT') {
      const target = this.findModule(tok.module);
      return target && {
        origin: { line, col: tok.col + 7, endCol: tok.end },
        target: this.moduleTarget(target)
      };
    }
    const origin = { line, col: tok.col, endCol: tok.end };
    if (tok.type === 'OP') {
      const found = this.lookupAt(mod, itemIndex, tok.name);
      return found && { origin, target: this.target(found) };
    }
    if (tok.type !== 'IDENT') {
      return undefined;
    }

    // local binders: the closest enclosing one
    let local;
    for (const b of localBinders(mod, item)) {
      if (b.index === index) {
        local = b;
        break;
      }
      if (b.name === tok.text && b.index < index && b.from <= index && index <= b.to
          && (!local || b.index > local.index)) {
        local = b;
      }
    }
    if (local) {
      const bt = tokens[local.index];
      return {
        origin,
        target: {
          file,
          selection: { line: bt.line, col: bt.col, endCol: bt.end },
          range: { line: bt.line, col: 0, endLine: bt.line, endCol: mod.lines[bt.line].length }
        }
      };
    }
    let found = this.qualified(mod, itemIndex, index);
    if (!found) {
      // an imported module is checked in its importer's scope, so a module may use names
      // it does not import itself (e.g. Path.batt): fall back to the standard library
      const stdlib = this.findModule('Stdlib');
      found = stdlib && stdlib !== file ? this.lookupExport(stdlib, tok.text) : undefined;
    }
    return found && { origin, target: this.target(found) };
  }

  moduleTarget(file) {
    const mod = this.module(file);
    const last = mod ? Math.min(mod.lines.length - 1, 5) : 0;
    return {
      file,
      selection: { line: 0, col: 0, endCol: 0 },
      range: { line: 0, col: 0, endLine: last, endCol: mod ? mod.lines[last].length : 0 }
    };
  }

  target(found) {
    if (found.kind === 'module') {
      return this.moduleTarget(found.file);
    }
    const { mod, def } = found;
    const nameTok = mod.tokens[def.nameIndex];
    // The Ctrl+hover preview falls back to an indentation heuristic for ranges of 8
    // lines or more: keep the signature, then add clauses and doc comments while it fits.
    const MAX = 7;
    let first = def.firstLine;
    let last = Math.min(def.lastLine, Math.max(def.sigLastLine, first + MAX));
    while (first > def.docLine && last - first < MAX) {
      first--;
    }
    return {
      file: mod.file,
      selection: { line: nameTok.line, col: nameTok.col, endCol: nameTok.end },
      range: { line: first, col: 0, endLine: last, endCol: mod.lines[last].length }
    };
  }
}

// ---------------------------------------------------------------- VS Code glue

// Root used to find modules: the workspace folder, else the closest ancestor with a stdlib/.
function projectRoot(vscode, uri) {
  const folder = vscode.workspace.getWorkspaceFolder(uri);
  if (folder) {
    return folder.uri.fsPath;
  }
  let dir = path.dirname(uri.fsPath);
  for (;;) {
    if (fs.existsSync(path.join(dir, 'stdlib', 'Stdlib.batt'))) {
      return dir;
    }
    const parent = path.dirname(dir);
    if (parent === dir) {
      return path.dirname(uri.fsPath);
    }
    dir = parent;
  }
}

function registerNavigation(vscode, context) {
  const resolvers = new Map();   // root -> Resolver (keeps the parse cache)
  const diskCache = new Map();   // file -> { mtimeMs, text }

  const readFile = (file) => {
    const open = vscode.workspace.textDocuments.find((d) => d.uri.scheme === 'file' && d.uri.fsPath === file);
    if (open) {
      return open.getText();
    }
    try {
      const { mtimeMs } = fs.statSync(file);
      const cached = diskCache.get(file);
      if (cached && cached.mtimeMs === mtimeMs) {
        return cached.text;
      }
      const text = fs.readFileSync(file, 'utf8');
      diskCache.set(file, { mtimeMs, text });
      return text;
    } catch (e) {
      return undefined;
    }
  };

  const toRange = (r) => new vscode.Range(r.line, r.col, r.endLine === undefined ? r.line : r.endLine, r.endCol);

  const provider = {
    provideDefinition(document, position) {
      if (document.uri.scheme !== 'file') {
        return undefined;
      }
      const root = projectRoot(vscode, document.uri);
      if (!resolvers.has(root)) {
        resolvers.set(root, new Resolver(root, readFile));
      }
      const result = resolvers.get(root).definition(document.uri.fsPath, position.line, position.character);
      if (!result) {
        return undefined;
      }
      return [{
        originSelectionRange: toRange(result.origin),
        targetUri: vscode.Uri.file(result.target.file),
        targetRange: toRange(result.target.range),
        targetSelectionRange: toRange(result.target.selection)
      }];
    }
  };

  context.subscriptions.push(vscode.languages.registerDefinitionProvider({ language: 'batt' }, provider));
}

module.exports = { registerNavigation, tokenize, parseModule, Resolver };
