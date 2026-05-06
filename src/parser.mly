%{
open Lang
open Helper
%}

%token COLON CCOLON EQ LPAR RPAR COMMA IN N EOF
%token TYPE
%token EMPTY EMPTY_IND
%token UNIT TT UNIT_IND
%token BOOL FALSE TRUE BOOL_IND
%token TO FUN DOT AT SIGMA TIMES TENS TENSP
%token FLAT FLATTEN FLAT_IND
%token IDEQ REFL
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
  | x=IDENT COLON a=term N y=IDENT args=list(IDENT) EQ t=term N { assert (x = y); (x, a, abss args t) }

simple_term:
  | TYPE { TType }
  | EMPTY { TIndType `Empty }
  | EMPTY_IND { TIndType_ind (`Empty, []) }
  | UNIT { TIndType `Unit }
  | TT { TIndTerm `Unit }
  | UNIT_IND LPAR t=term RPAR { TIndType_ind (`Unit, [t]) }
  | BOOL { TIndType `Bool }
  | FALSE { TIndTerm (`Bool false) }
  | BOOL_IND LPAR tf=term COMMA tt=term RPAR { TIndType_ind (`Bool, [tf;tt]) }
  | TRUE { TIndTerm (`Bool true) }
  | IDENT { TVar $1 }
  | FLAT simple_term { TFlat $2 }
  | FLATTEN simple_term { TFlatten $2 }
  | FLAT_IND LPAR x=IDENT COMMA t=term RPAR { TFlat_ind (x, t) }
  | REFL { TRefl }
  | LPAR term RPAR { $2 }

term:
  | simple_term { $1 }
  | t=simple_term IDEQ u=simple_term { TEq (t, u) }
  | t=simple_term AT u=simple_term { TApp (t, u) }
  | simple_term TO term { TPi (false, "_", $1, $3) }
  | simple_term TIMES term { TSigma ("_", $1, $3) }
  | simple_term TENS term { TTens ($1, $3) }
  | simple_term TENSP term { TTensPair ($1, $3) }
  | abs=nonempty_list(piabs) TO b=term { pis abs b }
  | FUN nonempty_list(IDENT) TODOT term { abss $2 $4 }
  | LPAR term COMMA term RPAR { TPair ($2, $4) }

piabs:
  | LPAR x=nonempty_list(IDENT) c=ccolon a=term RPAR { c,x,a }

ccolon:
  | COLON { false }
  | CCOLON { true }

TODOT:
  | TO | DOT { () }
