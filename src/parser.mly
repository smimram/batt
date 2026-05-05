%{
open Lang
%}

%token COLON EQ LPAR RPAR N EOF
%token TYPE
%token BOOL FALSE TRUE
%token TO FUN DOT
%token<string> IDENT

%right TO

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
  | IDENT COLON term EQ term N { ($1, $3, $5) }

term:
  | TYPE { TType }
  | BOOL { TIndType `Bool }
  | FALSE { TIndTerm (`Bool false) }
  | TRUE { TIndTerm (`Bool true) }
  | term TO term { TPi ("_", $1, $3) }
  | LPAR IDENT COLON term RPAR TO term { TPi ($2, $4, $7) }
  | FUN IDENT TO term { TAbs ($2, $4) }
  | IDENT { TVar $1 }

to_dot:
  | TO | DOT { () }
