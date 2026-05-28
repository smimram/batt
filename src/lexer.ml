open Parser

let letter = [%sedlex.regexp? 'A'..'Z' | 'a'..'z']
let ident_tail = [%sedlex.regexp? letter | '0'..'9' | '\'' | '-' | '_' | Utf8 "→"]

let rec token lexbuf =
  match%sedlex lexbuf with
  | "Type" -> TYPE
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
  | "_" -> META
  | "refl" -> REFL
  | "let" -> LET
  | "in" -> IN
  | "postulate" -> POSTULATE
  | "open import ", Star (letter | '-' | '_') ->
    let s = Sedlexing.Utf8.lexeme lexbuf in
    INCLUDE (String.sub s 12 (String.length s - 12))
  | letter, Star ident_tail ->
    IDENT (Sedlexing.Utf8.lexeme lexbuf)
  | "--", Star (Compl '\n') -> token lexbuf
  | Plus (' ' | '\t' | '\r') -> token lexbuf
  | '\n', ' ' ->
    Sedlexing.new_line lexbuf;
    token lexbuf
  | '\n' ->
    Sedlexing.new_line lexbuf;
    N
  | eof -> EOF
  | _ ->
    let s = Sedlexing.Utf8.lexeme lexbuf in
    failwith (Printf.sprintf "unexpected character: %s" s)
