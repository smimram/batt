type var = string

(** Basic inductive types. *)
type inductive_type = [`Empty | `Bool]

(** Basic inductive terms. *)
type inductive_term = [`Bool of bool]

type term =
  | TType
  | TIndType of inductive_type
  | TIndTerm of inductive_term
  | TPi of string * term * term
  | TAbs of string * term
  | TSigma of string * term * term
  | TPair of term * term
  | TVar of string

let rec string_of_term = function
  | TType -> "type"
  | TIndType `Empty -> "Empty"
  | TIndType `Bool -> "Bool"
  | TIndTerm (`Bool b) -> string_of_bool b
  | TPi (x, a, t) -> Printf.sprintf "(%s : %s) → %s" x (string_of_term a) (string_of_term t)
  | TAbs (x, t) -> Printf.sprintf "λ%s.%s" x (string_of_term t)
  | TSigma (x, a, t) -> Printf.sprintf "Σ(%s : %s).%s" x (string_of_term a) (string_of_term t)
  | TPair (t, u) -> Printf.sprintf "(%s, %s)" (string_of_term t) (string_of_term u)
  | TVar x -> x

type value =
  | Type
  | IndType of inductive_type
  | IndTerm of inductive_term
  | Pi of value * closure
  | Abs of closure
  | Sigma of value * closure
  | Pair of value * value
  | Neu of neutral

and neutral =
  | Var of int

and closure = var * term * environment

and environment = (var * value) list

(** Make a variable. *)
let vvar k = Neu (Var k)

(** Evaluate a term to a value. *)
let rec eval (env:environment) = function
  | TType -> Type
  | TIndType a -> IndType a
  | TIndTerm t -> IndTerm t
  | TPi (x, a, t) -> Pi (eval env a, (x, t, env))
  | TAbs (x, t) -> Abs (x, t, env)
  | TSigma (x, a, t) -> Sigma (eval env a, (x, t, env))
  | TPair (t, u) -> Pair (eval env t, eval env u)
  | TVar x -> List.assoc x env

(** Reify a value as a term. *)
let readback _k _v =
  failwith "TODO"

(** Instantiate a closure with a value. *)
let capp ((x,t,env):closure) (v:value) =
  eval ((x,v)::env) t

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
  (* TODO: remove *)
  if t <> u then
    if readback k t <> readback k u then failwith "eq"

(** Check that term has given type. *)
let rec check k env ctx (t:term) (a:value) =
  Printf.printf "CHECK %s\n%!" (string_of_term t);
  match t, a with
  | TIndTerm (`Bool _), IndType `Bool -> ()
  | TAbs (x, t), Pi (a, b) ->
     let xv = vvar k in
     let k = k+1 in
     let env = (x,xv)::env in
     let ctx =
       let cenv, benv = ctx in
       let benv = Bunch.Ext (benv, x, a) in
       cenv, benv
     in
     check k env ctx t (capp b xv)
  | TPair (t, u), Sigma (a, b) ->
     check k env ctx t a;
     let t = eval env t in
     check k env ctx u (capp b t)
  | t, a ->
     eq k (infer k env ctx t) a

(** Check that a term is a type. *)
and check_type k env ctx a =
  Printf.printf "CHECK TYPE %s\n%!" (string_of_term a);
  match a with
  | TType -> ()
  | TPi (x, a, b)
  | TSigma (x, a, b) ->
     check_type k env ctx a;
     let xv = vvar k in
     let k = k+1 in
     let env = (x,xv)::env in
     let a = eval env a in
     let ctx =
       let cenv, benv = ctx in
       let benv = Bunch.Ext (benv, x, a) in
       cenv, benv
     in
     check_type k env ctx b
  | a -> check k env ctx a Type

(** Infer the type of a term. *)
and infer k env ctx (t:term) =
  Printf.printf "INFER %s\n%!" (string_of_term t);
  (* TODO *)
  ignore k; ignore env;
  match t with
  | TIndType _ -> Type
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
