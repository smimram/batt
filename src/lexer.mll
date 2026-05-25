{
open Lexing
open Parser

let utf8 ?(n=1) lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { pos with pos_bol = pos.pos_bol + n }
}

let letter = ['A'-'Z''a'-'z']
let space = [' ''\t''\r']

rule token = parse
  | "U" { TYPE }
  | "Type" { TYPE }
  | "Empty" { EMPTY }
  | "⊥" { utf8 ~n:2 lexbuf; EMPTY }
  | "Unit" { UNIT }
  | "⊤" { utf8 ~n:2 lexbuf; UNIT }
  | "tt" { TT }
  | "Bool" { BOOL }
  | "false" { FALSE }
  | "true" { TRUE }
  | "Bool_ind" { BOOL_IND }
  | ":" { COLON }
  | "::" { CCOLON }
  | "∷" { utf8 ~n:2 lexbuf; CCOLON }
  | "=" { EQ }
  | "?" { HOLE }
  | "()" { LRPAR }
  | "(" { LPAR }
  | ")" { RPAR }
  | "{" { LACC }
  | "}" { RACC }
  | "," { COMMA }
  | "->" { TO }
  | "→"  { utf8 ~n:2 lexbuf; TO }
  | "ₗ" { utf8 ~n:2 lexbuf; LEFT }
  | "ᵣ" { utf8 ~n:2 lexbuf; RIGHT }
  | "." { DOT }
  | "fun" { FUN }
  | "λ" { utf8 lexbuf; FUN }
  | "ρ" { utf8 lexbuf; FUN }
  | "∂" { utf8 ~n:2 lexbuf; FUN }
  | "Σ" { utf8 lexbuf; SIGMA }
  | "×"  { utf8 lexbuf; TIMES }
  | "⨂"  { utf8 ~n:2 lexbuf; TENS }
  | "⊗"  { utf8 ~n:2 lexbuf; TENSP }
  | "♭" { utf8 ~n:2 lexbuf; FLAT }
  | "𝄫" { utf8 ~n:3 lexbuf; FLATTEN }
  | "≡" { utf8 ~n:2 lexbuf; IDEQ }
  | "_" { META }
  | "refl" { REFL }
  | "let" { LET }
  | "in" { IN }
  | "postulate" { POSTULATE }
  | "open import "((letter|['-''_'])* as s) { INCLUDE s }
  | letter(letter|['0'-'9''\'''-''_'])* as s { IDENT s }
  | "--"[^'\n']* { token lexbuf }
  | space+ { token lexbuf }
  | "\n " { new_line lexbuf; token lexbuf } (* quick hack, we should properly handle indentation *)
  | "\n" { new_line lexbuf; N }
  | eof { EOF }

(* Local Variables: *)
(* mode: tuareg *)
(* End: *)
