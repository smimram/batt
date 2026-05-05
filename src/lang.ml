type var = string

type term =
  | TType
  | TBool
  | TFalse
  | TTrue
  | TPi of string * term * term
  | TVar of string

type value =
  | Type
  | Bool
  | False
  | True
  | Pi of value * closure

and closure = var * term * environment

and environment = (var * value) list

(** Evaluate a term to a value. *)
let rec eval (env:environment) = function
  | TType -> Type
  | TBool -> Bool
  | TFalse -> False
  | TTrue -> True
  | TPi (x, a, t) -> Pi (eval env a, (x, t, env))
  | TVar x -> List.assoc x env

type decl = string * term * term

type decls = decl list

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

let eq k (t:value) (u:value) =
  (* TODO *)
  ignore k;
  assert (t = u)

(** Check that term has given type. *)
let rec check k env ctx (t:term) (a:value) =
  match t, a with
  | TBool, Type -> ()
  | TFalse, Bool -> ()
  | TTrue, Bool -> ()
  | t, a ->
     eq k (infer k env ctx t) a

(** Check that a term is a type. *)
and check_type k env ctx a =
  match a with
  | TType -> ()
  | a -> check k env ctx a Type

(** Infer the type of a term. *)
and infer k env ctx (t:term) =
  (* TODO *)
  ignore k; ignore env;
  match t with
  | TBool -> Type
  | TVar x ->
     (
       let cenv, benv = ctx in
       match Bunch.assoc_opt x benv with
       | Some a -> a
       | None -> List.assoc x cenv
     )
  | _ -> failwith "infer"

let check_decl k env ctx (x, a, t) =
  check_type k env ctx a;
  let a = eval env a in
  check k env ctx t a;
  let t = eval env t in
  (x,t)::env

let check_decls k env ctx decls =
  List.fold_left (fun env decl -> check_decl k env ctx decl) env decls

let check_decls_toplevel decls = ignore @@ check_decls 0 [] ([],Bunch.Empty) decls
