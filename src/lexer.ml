open Parser

(* Greek letters, except λ which is used for abstractions *)
let greek = [%sedlex.regexp? 0x391 .. 0x3A1 | 0x3A3 .. 0x3A9 | 0x3B1 .. 0x3BA | 0x3BC .. 0x3C9]
let letter = [%sedlex.regexp? 'A'..'Z' | 'a'..'z' | greek]
let space = [%sedlex.regexp? ' ' | '\t' | '\r']

let rec token lexbuf =
  match%sedlex lexbuf with
  | "Type" -> TYPE
  | "U" -> TYPE
  | Utf8 "⊥" | "\\bot" -> EMPTY
  | Utf8 "⊤" | "\\top" -> UNIT
  | "tt" -> TT
  | "false" -> FALSE
  | "true" -> TRUE
  | Utf8 "∷" | "::" -> CCOLON
  | ":" -> COLON
  | "=" -> EQ
  | "?" -> HOLE
  | "()" -> LRPAR
  | "(" -> LPAR
  | ")" -> RPAR
  | "{" -> LACC
  | "}" -> RACC
  | "," -> COMMA
  | "." -> DOT
  | Utf8 "→" | "->" | "\\to" -> TO
  | Utf8 "→ₗ" | Utf8 "⇀" | "->l" | "\\tol" -> TOL
  | Utf8 "→ᵣ" | Utf8 "⇁" | "->r" | "\\tor" -> TOR
  | Utf8 "λ" | "fun" -> FUN
  | Utf8 "ρ" -> FUN
  | Utf8 "∂" -> FUN
  | Utf8 "Σ" | "\\Sigma" -> SIGMA
  | Utf8 "×" | "\\times" -> TIMES
  | Utf8 "⨂" | "\\bigotimes" -> TENS
  | Utf8 "⊗" | "\\otimes" -> TENSP
  | Utf8 "♭" | "\\flat" -> FLAT
  | Utf8 "𝄫" | "\\fflat" -> FLATTEN
  | Utf8 "≡" | "\\equiv" -> IDEQ
  | Utf8 "≃" | "\\simeq" -> INFIX0 "_≃_"
  | Utf8 "≤" -> INFIX0 "leq"
  | Utf8 "≥" -> INFIX0 "geq"
  | Utf8 "∘" | "\\circ" -> INFIX1 "circ"
  | Utf8 "∨" -> INFIX1 "or"
  | Utf8 "¬" -> IDENT "not"
  | Utf8 "ℕ" | "Nat" -> NAT
  | "zero" -> ZERO
  | "succ" -> SUCC
  | Utf8 "𝕀0" | "II0" -> I0
  | Utf8 "𝕀1" | "II1" -> I1
  | Utf8 "𝕀∨" | "IIv" -> Iv
  | Utf8 "𝕀∧" | "IIw" -> Iw
  | Utf8 "𝕀" | "II" -> I
  | "_" -> META
  | "refl" -> REFL
  | "let" -> LET
  | "in" -> IN
  | "postulate" -> POSTULATE
  | "open" -> OPEN
  | "import ", Star (letter | '-' | '_') ->
    let s = Sedlexing.Utf8.lexeme lexbuf in
    IMPORT (String.sub s 7 (String.length s - 7))
  | Plus ('0'..'9') -> INT (int_of_string @@ Sedlexing.Utf8.lexeme lexbuf)
  | ((letter | Utf8 "𝕀"), Star (letter | '0'..'9' | '\'' | '-' | '_' | Utf8 "→" | Utf8 "⁻" | Utf8 "ₗ" | Utf8 "ᵣ" | Utf8 "𝕀")) | Utf8 "_≃_" -> IDENT (Sedlexing.Utf8.lexeme lexbuf)
  | "--", Star (Compl '\n') -> token lexbuf
  | Plus space -> token lexbuf
  | "\n " -> token lexbuf (* quick hack, we should properly handle indentation *)
  | '\n' -> N
  | eof -> EOF
  | _ ->
    let s = Sedlexing.Utf8.lexeme lexbuf in
    failwith (Printf.sprintf "unexpected character: %s" s)
