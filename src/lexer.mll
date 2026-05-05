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
  | "Bool" { BOOL }
  | "false" { FALSE }
  | "true" { TRUE }
  | ":" { COLON }
  | "=" { EQ }
  | "(" { LPAR }
  | ")" { RPAR }
  | "," { COMMA }
  | "->" { TO }
  | "→"  { utf8 ~n:2 lexbuf; TO }
  | "->l" { ARR Left }
  | "->r" { ARR Right }
  | "." { DOT }
  | "fun" { FUN }
  | "λ" { utf8 lexbuf; FUN }
  | "Σ" { utf8 lexbuf; SIGMA }
  | "×"  { utf8 lexbuf; TIMES }
  | "⨂"  { utf8 ~n:2 lexbuf; TENS }
  | "⊗"  { utf8 ~n:2 lexbuf; TENSP }
  | "♭" { utf8 ~n:2 lexbuf; FLAT }
  | (['A'-'Z''a'-'z''0'-'9''\'']+ as s) { IDENT s }
  | "--"[^'\n']* { token lexbuf }
  | space+ { token lexbuf }
  | "\n" { new_line lexbuf; N }
  | eof { EOF }

(* Local Variables: *)
(* mode: tuareg *)
(* End: *)
