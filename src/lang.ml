type var = string

type term =
  | Type
  | Var of string

type decl = string * term * term

type decls = decl list

type value =
  | VType

type crisp = (var * term) list

module Bunch = struct
  type t =
    | Empty
    | Ext of t * string * value
    | L of l

  and l =
    | One of string * value
    | Tens of l * t

  let rec assoc_opt x = function
    | Empty -> None
    | Ext (env, y, a) -> if x = y then Some a else assoc_opt x env
    | L l -> assocl_opt x l
  and assocl_opt x = function
    | One (y, a) -> if x = y then Some a else None
    | Tens (lenv, env) ->
       (
         match assoc_opt x env with
         | Some a -> Some a
         | None -> assocl_opt x lenv
       )
end

type bunch = Bunch.t

type context = crisp * bunch

let infer (cenv,benv) t =
  match t with
  | Type -> VType
  | Var x ->
     (
       match Bunch.assoc_opt x benv with
       | Some a -> a
       | None -> List.assoc x cenv
     )
