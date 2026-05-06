{
open Lexing
open Parser

let utf8 ?(n=1) lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { pos with pos_bol = pos.pos_bol + n }
}

let space = ' ' | '\t' | '\r'

rule token = parse
  | "U" { TYPE }
  | "Type" { TYPE }
  | "Empty" { EMPTY }
  | "⊥" { utf8 ~n:2 lexbuf; EMPTY }
  | "Empty_ind" { EMPTY_IND }
  | "Unit" { UNIT }
  | "⊤" { utf8 ~n:2 lexbuf; UNIT }
  | "tt" { TT }
  | "Unit_ind" { UNIT_IND }
  | "Bool" { BOOL }
  | "false" { FALSE }
  | "true" { TRUE }
  | "Bool_ind" { BOOL_IND }
  | "::" { CCOLON }
  | ":" { COLON }
  | "=" { EQ }
  | "()" { LRPAR }
  | "(" { LPAR }
  | ")" { RPAR }
  | "," { COMMA }
  | "->" { TO }
  | "→"  { utf8 ~n:2 lexbuf; TO }
  | "ₗ" { utf8 ~n:2 lexbuf; LEFT }
  | "ᵣ" { utf8 ~n:2 lexbuf; RIGHT }
  | "." { DOT }
  | "fun" { FUN }
  | "λ" { utf8 lexbuf; FUN }
  | "@" { AT }
  | "Σ" { utf8 lexbuf; SIGMA }
  | "×"  { utf8 lexbuf; TIMES }
  | "⨂"  { utf8 ~n:2 lexbuf; TENS }
  | "⊗"  { utf8 ~n:2 lexbuf; TENSP }
  | "♭" { utf8 ~n:2 lexbuf; FLAT }
  | "♭_ind" { utf8 ~n:2 lexbuf; FLAT_IND }
  | "𝄫" { utf8 ~n:3 lexbuf; FLATTEN }
  | "≡" { utf8 ~n:2 lexbuf; IDEQ }
  | "refl" { REFL }
  | "in" { IN }
  | (['A'-'Z''a'-'z''0'-'9''\'']+ as s) { IDENT s }
  | "--"[^'\n']* { token lexbuf }
  | space+ { token lexbuf }
  | "\n" { new_line lexbuf; N }
  | eof { EOF }

(* Local Variables: *)
(* mode: tuareg *)
(* End: *)
