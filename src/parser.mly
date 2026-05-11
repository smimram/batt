%{
open Lang
open Helper
%}

%token COLON CCOLON EQ LPAR RPAR LRPAR COMMA LET IN N EOF
%token TYPE
%token EMPTY
%token UNIT TT
%token BOOL FALSE TRUE BOOL_IND
%token TO FUN DOT AT SIGMA TIMES TENS TENSP
%token FLAT FLATTEN
%token IDEQ REFL
%token LEFT RIGHT
%token<string> IDENT

%nonassoc IN
%nonassoc DOT
%nonassoc FUN
%right TO
%nonassoc IDEQ
%right TIMES
%right TENSP
%right TENS
%left AT

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
  | x=IDENT c=ccolon a=term N def=def N { let y, t = def in assert (x = y); (x, c, a, t) }

def:
  | y=IDENT args=list(pattern) EQ t=term { y, abss_pattern args t }
  | y=IDENT args=list(pattern) LRPAR { y, abss_pattern args (TIndType_ind (`Empty, [])) }

simple_term:
  | TYPE { TType }
  | EMPTY { TIndType `Empty }
  | UNIT { TIndType `Unit }
  | TT { TIndTerm `Unit }
  | BOOL { TIndType `Bool }
  | FALSE { TIndTerm (`Bool false) }
  | BOOL_IND LPAR tf=term COMMA tt=term RPAR { TIndType_ind (`Bool, [tf;tt]) }
  | TRUE { TIndTerm (`Bool true) }
  | IDENT { TVar $1 }
  | FLAT simple_term { TFlat $2 }
  | FLATTEN simple_term { TFlatten $2 }
  | REFL { TRefl }
  | LPAR term RPAR { $2 }
  | LPAR term COMMA term RPAR { TPair ($2, $4) }

term:
  | simple_term { $1 }
  | t=term IDEQ u=term { TEq (t, u) }
  | t=term AT s=option(dir) u=term { TApp (s, t, u) }
  /* | t=term u=term { TApp (None, t, u) } */
  | a=term TO s=option(dir) b=term { match s with None -> TPi (Normal, "_", a, b) | Some s -> TArr (s, a, b) }
  | term TIMES term { TSigma ("_", $1, $3) }
  | term TENS term { TTens ($1, $3) }
  | term TENSP term { TTensPair ($1, $3) }
  | abs=nonempty_list(piabs) TO b=term { pis abs b }
  | SIGMA LPAR x=IDENT COLON a=term RPAR DOT b=term { TSigma (x, a, b) }
  | FUN x=nonempty_list(pattern) to_dot t=term { abss_pattern x t }
  | LET x=IDENT c=ccolon a=term EQ t=term IN u=term { TLet (c, x, a, t, u) }

pattern:
  | x=IDENT d=option(dir) { `Var (x,d) }
  | TT { `Unit }
  | LPAR x=IDENT COMMA y=IDENT RPAR { `Pair (x,y) }
  | LPAR x=IDENT TENSP y=IDENT RPAR { `Tens (x,y) }
  | FLATTEN x=IDENT { `Flatten x }
  | REFL { `Refl }

piabs:
  | LPAR x=nonempty_list(IDENT) c=ccolon a=term RPAR { c,x,a }

dir:
  | LEFT { Left }
  | RIGHT { Right }

ccolon:
  | COLON { Normal }
  | CCOLON { Crisp }

to_dot:
  | TO | DOT { () }
