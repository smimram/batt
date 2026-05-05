%{
open Lang
%}

%token COLON EQ LPAR RPAR COMMA N EOF
%token TYPE
%token BOOL FALSE TRUE
%token TO FUN DOT SIGMA TIMES TENS TENSP
%token FLAT FLATTEN
%token<string> IDENT
%token<Lang.side> ARR

%start main
%type<Lang.decls> main
%%

main:
  | decls EOF { $1 }

decls:
  | { [] }
  | N decls { $2 }
  | decl decls { $1::$2 }

decl:
  | IDENT COLON term N IDENT EQ term N { assert ($1 = $5); ($1, $3, $7) }

simple_term:
  | TYPE { TType }
  | BOOL { TIndType `Bool }
  | FALSE { TIndTerm (`Bool false) }
  | TRUE { TIndTerm (`Bool true) }
  | IDENT { TVar $1 }
  | LPAR term RPAR { $2 }
  | FLAT simple_term { TFlat $2 }

term:
  | simple_term { $1 }
  | simple_term TO term { TPi ("_", $1, $3) }
  | simple_term TIMES term { TSigma ("_", $1, $3) }
  | simple_term TENS term { TTens ($1, $3) }
  | simple_term TENSP term { TTensPair ($1, $3) }
  | LPAR IDENT COLON term RPAR TO term { TPi ($2, $4, $7) }
  | FUN IDENT TODOT term { TAbs ($2, $4) }
  | LPAR term COMMA term RPAR { TPair ($2, $4) }

TODOT:
  | TO | DOT { () }
