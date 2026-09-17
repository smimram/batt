function ku(event) {
  if (event.keyCode == 13)
    document.getElementById("send").click();
}

function esc(s) {
  return s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}

const keywords = new Set(["Type", "U", "let", "in", "fun", "postulate", "open", "import", "refl", "tt", "true", "false", "bool_ind"]);

// One combined regex: matching is done on raw text, pieces are escaped afterwards.
const rules = [
  ["comment", /--[^\n]*/],
  ["ident",   /\p{L}[\p{L}\p{N}'\-_→]*/],
  ["symbol",  /\\(?:bigotimes|otimes|Sigma|times|fflat|flat|equiv|simeq|circ|top|bot|tol|tor|to)|->[lr]?|→[ₗᵣ]?|::|[λρ∂Σ×⨂⊗♭𝄫≡≃∘⊥⊤∷]/],
  ["hole",    /\?|_/],
];

const re = new RegExp(rules.map(([_, r]) => "(" + r.source + ")").join("|"), "gu");

function highlight() {
  const input = document.getElementById("input");
  const hl = document.getElementById("highlight");
  const src = input.value;
  let out = "", last = 0;
  for (const m of src.matchAll(re)) {
    out += esc(src.slice(last, m.index));
    let cls = rules[m.slice(1).findIndex(g => g !== undefined)][0];
    if (cls == "ident") cls = keywords.has(m[0]) ? "keyword" : null;
    out += cls ? '<span class="' + cls + '">' + esc(m[0]) + "</span>" : esc(m[0]);
    last = m.index + m[0].length;
  }
  // Trailing newline so that a final empty line has height.
  hl.innerHTML = out + esc(src.slice(last)) + "\n";
  hl.scrollTop = input.scrollTop;
  hl.scrollLeft = input.scrollLeft;
}

// LaTeX-like shortcuts, replaced when followed by a non-letter character.
const symbols = {
  to: "→", tol: "⇀", tor: "⇁", Sigma: "Σ", times: "×", bigotimes: "⨂", Otimes: "⨂",
  otimes: "⊗", flat: "♭", fflat: "𝄫", equiv: "≡", simeq: "≃", circ: "∘",
  top: "⊤", bot: "⊥", lambda: "λ", rho: "ρ", partial: "∂",
};

function replaceSymbols(event) {
  if (event.inputType != "insertText" && event.inputType != "insertLineBreak") return;
  const input = event.target;
  const pos = input.selectionStart;
  const m = input.value.slice(0, pos).match(/\\([A-Za-z]+)([^A-Za-z])$/);
  if (!m || !(m[1] in symbols)) return;
  const start = pos - m[0].length;
  input.setRangeText(symbols[m[1]] + m[2], start, pos, "end");
}

function init() {
  const input = document.getElementById("input");
  input.onkeyup = ku;
  input.addEventListener("input", replaceSymbols);
  input.addEventListener("input", highlight);
  input.addEventListener("scroll", highlight);
  highlight();
}
