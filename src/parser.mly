%{
open Lang
%}

%token COLON CCOLON EQ LPAR RPAR COMMA IN N EOF
%token TYPE
%token UNIT TT UNIT_IND
%token BOOL FALSE TRUE BOOL_IND
%token TO FUN DOT SIGMA TIMES TENS TENSP
%token FLAT FLATTEN LETFLAT
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
  | UNIT { TIndType `Unit }
  | TT { TIndTerm `Unit }
  | UNIT_IND LPAR x = IDENT a = term COMMA t = term COMMA u = term RPAR { TIndType_ind (`Unit, x, a, t, u) }
  | BOOL { TIndType `Bool }
  | FALSE { TIndTerm (`Bool false) }
  | BOOL_IND LPAR x = IDENT a = term COMMA tf = term COMMA tt = term COMMA t = term RPAR { TIndType_ind (`Bool, x, a, TPair (tf, tt), t) }
  | TRUE { TIndTerm (`Bool true) }
  | IDENT { TVar $1 }
  | LPAR term RPAR { $2 }
  | FLAT simple_term { TFlat $2 }
  | FLATTEN simple_term { TFlatten $2 }

term:
  | simple_term { $1 }
  | LPAR simple_term simple_term RPAR { TApp ($2, $3) }
  | simple_term TO term { TPi (false, "_", $1, $3) }
  | simple_term TIMES term { TSigma ("_", $1, $3) }
  | simple_term TENS term { TTens ($1, $3) }
  | simple_term TENSP term { TTensPair ($1, $3) }
  | LPAR IDENT  COLON term RPAR TO term { TPi (false, $2, $4, $7) }
  | LPAR IDENT CCOLON term RPAR TO term { TPi (true, $2, $4, $7) }
  | FUN IDENT TODOT term { TAbs ($2, $4) }
  | LPAR term COMMA term RPAR { TPair ($2, $4) }
  | LETFLAT IDENT EQ term IN term { TFlat_ind ($2, $4, $6) }

TODOT:
  | TO | DOT { () }
