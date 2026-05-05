%{
open Lang
%}

%token COLON EQ LPAR RPAR N EOF
%token TYPE
%token BOOL FALSE TRUE
%token<string> IDENT

%start main
%type<Lang.decls> main
%%

main:
  | decls EOF { $1 }

decls:
  | { [] }
  | decl decls { $1::$2 }

decl:
  | IDENT COLON term EQ term N { ($1, $3, $5) }

term:
  | TYPE { Type }
  | BOOL { Bool }
  | FALSE { False }
  | TRUE { True }
