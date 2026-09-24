open Parser

let letter = [%sedlex.regexp? 'A'..'Z' | 'a'..'z']
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
  | "bool_ind" -> BOOL_IND
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
  | Utf8 "≃" | "\\simeq" -> EQUIV
  | Utf8 "∘" | "\\circ" -> CIRC
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
  | (letter, Star (letter | '0'..'9' | '\'' | '-' | '_' | Utf8 "→" | Utf8 "⁻" | Utf8 "ₗ" | Utf8 "ᵣ")) | Utf8 "_≃_" -> IDENT (Sedlexing.Utf8.lexeme lexbuf)
  | "--", Star (Compl '\n') -> token lexbuf
  | Plus space -> token lexbuf
  | "\n " -> token lexbuf (* quick hack, we should properly handle indentation *)
  | '\n' -> N
  | eof -> EOF
  | _ ->
    let s = Sedlexing.Utf8.lexeme lexbuf in
    failwith (Printf.sprintf "unexpected character: %s" s)
