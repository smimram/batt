%{
open Term
open Helper

let binder_names ~pos t =
  let rec aux acc = function
    | Var x -> x :: acc
    | App (t, _, Var x) -> aux (x :: acc) t
    | _ -> failwith @@ Printf.sprintf "%s: binder expected" (Pos.to_string pos)
  in
  aux [] t
%}

%token COLON CCOLON EQ LPAR RPAR LRPAR LACC RACC COMMA LET IN POSTULATE META HOLE N EOF
%token TYPE LARGETYPE
%token<int> INT
%token EMPTY
%token UNIT TT
%token BOOL FALSE TRUE BOOL_IND
%token TO FUN DOT SIGMA TIMES TENS TENSP
%token FLAT FLATTEN
%token IDEQ REFL
%token LEFT RIGHT
%token EQUIV
%token<string> IDENT
%token OPEN
%token<string> IMPORT

%nonassoc EQUIV
%nonassoc IDEQ
%right TIMES
%right TENSP
%right TENS

%start main
%type<Term.decls> main
%%

main:
  | decls EOF { $1 }

decls:
  | { [] }
  | decl { $1 }
  | N decls { $2 }
  | decl N decls { $1@$3 }

decl:
  | x=IDENT c=ccolon a=term N def=def { let y, t = def in assert (x = y); [Def (x, c, Some a, t)] }
  | POSTULATE x=IDENT c=ccolon a=term { [Def (x, c, Some a, mk ~pos:$loc @@ Postulate None)] }
  | m=IMPORT { [Def (m, Crisp, None, mk ~pos:$loc @@ Import m)] }
  | OPEN m=IMPORT { [Def (m, Crisp, None, mk ~pos:$loc(m) @@ Import m); Open (mk ~pos:$loc(m) @@ Var m)] }
  | OPEN t=term { [Open t] }

def:
  | y=IDENT args=list(pattern) EQ t=term { y, abss_pattern ~pos:$loc args t }
  | y=IDENT args=list(pattern) LRPAR { y, abss_pattern ~pos:$loc args (mk ~pos:$loc($3)(IndType_ind (`Empty, []))) }

atom:
  | TYPE { mk ~pos:$loc @@ Type 0 }
  | LARGETYPE { mk ~pos:$loc @@ Type 1 }
  | TYPE n=INT { mk ~pos:$loc @@ Type n }
  | EMPTY { mk ~pos:$loc @@ IndType `Empty }
  | UNIT { mk ~pos:$loc @@ IndType `Unit }
  | TT { mk ~pos:$loc @@ IndTerm `Unit }
  | BOOL { mk ~pos:$loc @@ IndType `Bool }
  | FALSE { mk ~pos:$loc @@ IndTerm (`Bool false) }
  | BOOL_IND LPAR tf=fun_term COMMA tt=term RPAR { mk ~pos:$loc @@ IndType_ind (`Bool, [tf;tt]) }
  | TRUE { mk ~pos:$loc @@ IndTerm (`Bool true) }
  | IDENT { mk ~pos:$loc @@ Var $1 }
  | REFL { mk ~pos:$loc @@ Refl }
  | HOLE { mk ~pos:$loc @@ Hole $loc }
  | META { mk ~pos:$loc @@ Meta (`Fresh (Some $loc)) }
  | LPAR t=term RPAR { t }
  | t=atom DOT x=IDENT { mk ~pos:$loc @@ RecordField (t, x) }

prefix_term:
  | atom { $1 }
  | FLAT t=prefix_term { mk ~pos:$loc @@ Flat t }
  | FLATTEN t=prefix_term { mk ~pos:$loc @@ Flatten t }

app_term:
  | prefix_term { $1 }
  | t=app_term u=prefix_term { app ~pos:$loc t u }
  | t=app_term LACC u=term RACC { app ~pos:$loc ~icit:Implicit t u }

prod_term:
  | app_term { $1 }
  | a=prod_term TENS b=prod_term { mk ~pos:$loc @@ Tens (a, b) }
  | a=prod_term TENSP b=prod_term { mk ~pos:$loc @@ TensPair (a, b) }
  | a=prod_term TIMES b=prod_term { mk ~pos:$loc @@ Sigma ("_", a, b) }
  | t=prod_term IDEQ u=prod_term { mk ~pos:$loc @@ Eq (t, u) }
  | t=prod_term EQUIV u=prod_term { mk ~pos:$loc @@ apps (mk ~pos:$loc($2) @@ Var "_≃_") [t; u] }

fun_term:
  | prod_term { $1 }
  | a=prod_term TO s=option(dir) b=fun_term { match s with None -> mk ~pos:$loc @@ Pi (Explicit, Normal, "_", a, b) | Some s -> mk ~pos:$loc @@ Arr (s, a, b) }
  | abs=nonempty_list(binder_group) TO b=fun_term { pis ~pos:$loc abs b }
  | SIGMA LPAR x=IDENT COLON a=term RPAR DOT b=fun_term { mk ~pos:$loc @@ Sigma (x, a, b) }
  | FUN x=nonempty_list(pattern) to_dot t=fun_term { abss_pattern ~pos:$loc x t }
  | LET x=IDENT c=ccolon a=term EQ t=term IN u=fun_term { mk ~pos:$loc @@ Let (c, x, a, t, u) }
  /* | LET x=pattern EQ t=term IN u=term { app (abs_pattern x u) t } */

term:
  | t=fun_term { t }
  | t=fun_term COMMA u=term { mk ~pos:$loc @@ Pair (t, u) }

pattern:
  | x=identm { `Var (Explicit,x) }
  | LACC x=identm RACC { `Var (Implicit,x) }
  | TT { `Unit }
  | LPAR x=identm COMMA y=identm RPAR { `Pair (x,y) }
  | LPAR x=identm TENSP y=identm RPAR { `Tens (x,y) }
  | FLATTEN x=identm { `Flatten x }
  | REFL { `Refl }

identm:
  | IDENT { $1 }
  | META { "_" }

binder_group:
  | LPAR t=term c=ccolon a=term RPAR { Explicit,c,binder_names ~pos:$loc(t) t,a }
  | LACC x=nonempty_list(IDENT) c=ccolon a=term RACC { Implicit,c,x,a }

dir:
  | LEFT { Left }
  | RIGHT { Right }

ccolon:
  | COLON { Normal }
  | CCOLON { Crisp }

to_dot:
  | TO | DOT { () }
