open Parser

let letter = [%sedlex.regexp? 'A'..'Z' | 'a'..'z']
let space = [%sedlex.regexp? ' ' | '\t' | '\r']

let rec token lexbuf =
  match%sedlex lexbuf with
  | "Type" -> TYPE
  | "TYPE" -> LARGETYPE
  | "U" -> TYPE
  | "Empty" -> EMPTY
  | Utf8 "⊥" -> EMPTY
  | "Unit" -> UNIT
  | Utf8 "⊤" -> UNIT
  | "tt" -> TT
  | "Bool" -> BOOL
  | "false" -> FALSE
  | "true" -> TRUE
  | "Bool_ind" -> BOOL_IND
  | "::" -> CCOLON
  | Utf8 "∷" -> CCOLON
  | ":" -> COLON
  | "=" -> EQ
  | "?" -> HOLE
  | "()" -> LRPAR
  | "(" -> LPAR
  | ")" -> RPAR
  | "{" -> LACC
  | "}" -> RACC
  | "," -> COMMA
  | "->" -> TO
  | Utf8 "→" -> TO
  | Utf8 "ₗ" -> LEFT
  | Utf8 "ᵣ" -> RIGHT
  | "." -> DOT
  | "fun" -> FUN
  | Utf8 "λ" -> FUN
  | Utf8 "ρ" -> FUN
  | Utf8 "∂" -> FUN
  | Utf8 "Σ" -> SIGMA
  | Utf8 "×" -> TIMES
  | Utf8 "⨂" -> TENS
  | Utf8 "⊗" -> TENSP
  | Utf8 "♭" -> FLAT
  | Utf8 "𝄫" -> FLATTEN
  | Utf8 "≡" -> IDEQ
  | Utf8 "≃" -> EQUIV
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
  | (letter, Star (letter | '0'..'9' | '\'' | '-' | '_' | Utf8 "→")) | Utf8 "_≃_" -> IDENT (Sedlexing.Utf8.lexeme lexbuf)
  | "--", Star (Compl '\n') -> token lexbuf
  | Plus space -> token lexbuf
  | "\n " -> token lexbuf (* quick hack, we should properly handle indentation *)
  | '\n' -> N
  | eof -> EOF
  | _ ->
    let s = Sedlexing.Utf8.lexeme lexbuf in
    failwith (Printf.sprintf "unexpected character: %s" s)
