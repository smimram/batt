%{
open Lang
%}

%token COLON CCOLON EQ LPAR RPAR COMMA IN N EOF
%token TYPE
%token UNIT TT UNIT_IND
%token BOOL FALSE TRUE BOOL_IND
%token TO FUN DOT AT SIGMA TIMES TENS TENSP
%token FLAT FLATTEN FLAT_IND
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
  | UNIT_IND LPAR t=term RPAR { TIndType_ind (`Unit, t) }
  | BOOL { TIndType `Bool }
  | FALSE { TIndTerm (`Bool false) }
  | BOOL_IND LPAR tf=term COMMA tt=term RPAR { TIndType_ind (`Bool, TPair (tf, tt)) }
  | TRUE { TIndTerm (`Bool true) }
  | IDENT { TVar $1 }
  | LPAR term RPAR { $2 }
  | FLAT simple_term { TFlat $2 }
  | FLATTEN simple_term { TFlatten $2 }

term:
  | simple_term { $1 }
  | t=simple_term AT u=simple_term { TApp (t, u) }
  | simple_term TO term { TPi (false, "_", $1, $3) }
  | simple_term TIMES term { TSigma ("_", $1, $3) }
  | simple_term TENS term { TTens ($1, $3) }
  | simple_term TENSP term { TTensPair ($1, $3) }
  | LPAR nonempty_list(IDENT)  COLON term RPAR TO term { tpis false $2 $4 $7 }
  | LPAR nonempty_list(IDENT) CCOLON term RPAR TO term { tpis true  $2 $4 $7 }
  | FUN nonempty_list(IDENT) TODOT term { tabss $2 $4 }
  | LPAR term COMMA term RPAR { TPair ($2, $4) }
  | FLAT_IND LPAR x=IDENT COMMA a=term COMMA t=term COMMA u=term RPAR { TFlat_ind (x, a, t, u) }

TODOT:
  | TO | DOT { () }
