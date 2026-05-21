%{
open Lang
open Helper
%}

%token COLON CCOLON EQ LPAR RPAR LRPAR LACC RACC COMMA LET IN POSTULATE META HOLE N EOF
%token TYPE
%token EMPTY
%token UNIT TT
%token BOOL FALSE TRUE BOOL_IND
%token TO FUN DOT SIGMA TIMES TENS TENSP
%token FLAT FLATTEN
%token IDEQ REFL
%token LEFT RIGHT
%token<string> IDENT
%token<string> INCLUDE

%nonassoc IDEQ
%right TIMES
%right TENSP
%right TENS
%nonassoc VAR
%nonassoc IDENT

%start main
%type<Lang.decls> main
%%

main:
  | decls EOF { $1 }

decls:
  | { [] }
  | decl { [$1] }
  | N decls { $2 }
  | decl N decls { $1::$3 }

decl:
  | x=IDENT c=ccolon a=term N def=def { let y, t = def in assert (x = y); (x, c, a, t) }
  | POSTULATE x=IDENT c=ccolon a=term { (x, c, a, TPostulate) }

def:
  | y=IDENT args=list(pattern) EQ t=term { y, abss_pattern args t }
  | y=IDENT args=list(pattern) LRPAR { y, abss_pattern args (TIndType_ind (`Empty, [])) }

atom:
  | TYPE { TType }
  | EMPTY { TIndType `Empty }
  | UNIT { TIndType `Unit }
  | TT { TIndTerm `Unit }
  | BOOL { TIndType `Bool }
  | FALSE { TIndTerm (`Bool false) }
  | BOOL_IND LPAR tf=fun_term COMMA tt=term RPAR { TIndType_ind (`Bool, [tf;tt]) }
  | TRUE { TIndTerm (`Bool true) }
  | IDENT %prec VAR { TVar $1 }
  | REFL { TRefl }
  | HOLE { THole $loc }
  | META { TMeta None }
  | LPAR t=term RPAR { t }

prefix_term:
  | atom { $1 }
  | FLAT t=prefix_term { TFlat t }
  | FLATTEN t=prefix_term { TFlatten t }

app_term:
  | prefix_term { $1 }
  | t=app_term u=prefix_term { app t u }
  | t=app_term LACC u=term RACC { app ~icit:Implicit t u }

prod_term:
  | app_term { $1 }
  | a=prod_term TENS b=prod_term { TTens (a, b) }
  | a=prod_term TENSP b=prod_term { TTensPair (a, b) }
  | a=prod_term TIMES b=prod_term { TSigma ("_", a, b) }
  | t=prod_term IDEQ u=prod_term { TEq (t, u) }

fun_term:
  | prod_term { $1 }
  | a=prod_term TO s=option(dir) b=fun_term { match s with None -> TPi (Explicit, Normal, "_", a, b) | Some s -> TArr (s, a, b) }
  | abs=nonempty_list(piabs) TO b=fun_term { pis abs b }
  | abs=nonempty_list(piabs_implicit) TO b=fun_term { pis ~icit:Implicit abs b }
  | SIGMA LPAR x=IDENT COLON a=term RPAR DOT b=fun_term { TSigma (x, a, b) }
  | FUN x=nonempty_list(pattern) to_dot t=fun_term { abss_pattern x t }
  | LET x=IDENT c=ccolon a=term EQ t=term IN u=fun_term { TLet (c, x, a, t, u) }
  /* | LET x=pattern EQ t=term IN u=term { app (abs_pattern x u) t } */

term:
  | t=fun_term { t }
  | t=fun_term COMMA u=term { TPair (t, u) }

pattern:
  | x=identm d=option(dir) { `Var (x,d) }
  | TT { `Unit }
  | LPAR x=identm COMMA y=identm RPAR { `Pair (x,y) }
  | LPAR x=identm TENSP y=identm RPAR { `Tens (x,y) }
  | FLATTEN x=identm { `Flatten x }
  | REFL { `Refl }

identm:
  | IDENT { $1 }
  | META { "_" }

piabs:
  | LPAR x=nonempty_list(IDENT) c=ccolon a=term RPAR { c,x,a }

piabs_implicit:
  | LACC x=nonempty_list(IDENT) c=ccolon a=term RACC { c,x,a }

dir:
  | LEFT { Left }
  | RIGHT { Right }

ccolon:
  | COLON { Normal }
  | CCOLON { Crisp }

to_dot:
  | TO | DOT { () }
