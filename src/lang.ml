type var = string

type term =
  | Type
  | Bool
  | False
  | True
  | Var of string

type value =
  | VType
  | VBool
  | VFalse
  | VTrue

type environment = (var * value) list

(** Evaluate a term to a value. *)
let eval (env:environment) = function
  | Type -> VType
  | Bool -> VBool
  | False -> VFalse
  | True -> VTrue
  | Var x -> List.assoc x env

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
  | Bool, VType -> ()
  | False, VBool -> ()
  | True, VBool -> ()
  | t, a ->
     eq k (infer k env ctx t) a

(** Check that a term is a type. *)
and check_type k env ctx a =
  match a with
  | Type -> ()
  | a -> check k env ctx a VType

(** Infer the type of a term. *)
and infer k env ctx (t:term) =
  (* TODO *)
  ignore k; ignore env;
  match t with
  | Bool -> VType
  | Var x ->
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
