type var = string

type term =
  | Var of string
  | Type

type crisp = (var * term) list

type bunch =
  | Bemtpy
  | Bext of bunch * string * term
  | Btens of bunch * bunch

