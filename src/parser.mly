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

%nonassoc FUN
%right TO
%right TIMES
%right TENSP
%right TENS

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
  | x=IDENT COLON a=term N y=IDENT args=list(pattern) EQ t=term N { assert (x = y); (x, a, abss_pattern args t) }

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
  | term TO term { TPi (false, "_", $1, $3) }
  | term TIMES term { TSigma ("_", $1, $3) }
  | term TENS term { TTens ($1, $3) }
  | term TENSP term { TTensPair ($1, $3) }
  | abs=nonempty_list(piabs) TO b=term { pis abs b }
  | FUN x=nonempty_list(pattern) to_dot t=term { abss_pattern x t }
  | LPAR term COMMA term RPAR { TPair ($2, $4) }

pattern:
  | x=IDENT { `Var x }
  | TT { `Unit }
  | LPAR x=IDENT COMMA y=IDENT RPAR { `Pair (x,y) }
  | LPAR x=IDENT TENSP y=IDENT RPAR { `Tens (x,y) }
  | FLATTEN x=IDENT { `Flatten x }

piabs:
  | LPAR x=nonempty_list(IDENT) c=ccolon a=term RPAR { c,x,a }

ccolon:
  | COLON { false }
  | CCOLON { true }

to_dot:
  | TO | DOT { () }
