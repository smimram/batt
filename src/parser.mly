%{
open Lang
open Helper
%}

%token COLON CCOLON EQ LPAR RPAR LRPAR COMMA LET IN HOLE N EOF
%token TYPE
%token EMPTY
%token UNIT TT
%token BOOL FALSE TRUE BOOL_IND
%token TO FUN DOT SIGMA TIMES TENS TENSP
%token FLAT FLATTEN
%token IDEQ REFL
%token LEFT RIGHT
%token<string> IDENT

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
  | BOOL_IND LPAR tf=term COMMA tt=term RPAR { TIndType_ind (`Bool, [tf;tt]) }
  | TRUE { TIndTerm (`Bool true) }
  | IDENT %prec VAR { TVar $1 }
  | REFL { TRefl }
  | HOLE { THole $loc }
  | LPAR term RPAR { $2 }
  | LPAR term COMMA term RPAR { TPair ($2, $4) }

prefix_term:
  | atom { $1 }
  | FLAT prefix_term { TFlat $2 }
  | FLATTEN prefix_term { TFlatten $2 }

app_term:
  | prefix_term { $1 }
  | t=app_term u=prefix_term { TApp (t, u) }

expr:
  | app_term { $1 }
  | a=expr TENS b=expr { TTens (a, b) }
  | a=expr TENSP b=expr { TTensPair (a, b) }
  | a=expr TIMES b=expr { TSigma ("_", a, b) }
  | t=expr IDEQ u=expr { TEq (t, u) }

term:
  | expr { $1 }
  | a=expr TO s=option(dir) b=term { match s with None -> TPi (Normal, "_", a, b) | Some s -> TArr (s, a, b) }
  | abs=nonempty_list(piabs) TO b=term { pis abs b }
  | SIGMA LPAR x=IDENT COLON a=term RPAR DOT b=term { TSigma (x, a, b) }
  | FUN x=nonempty_list(pattern) to_dot t=term { abss_pattern x t }
  | LET x=IDENT c=ccolon a=term EQ t=term IN u=term { TLet (c, x, a, t, u) }
  /* | LET x=pattern EQ t=term IN u=term { app () () } */

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
