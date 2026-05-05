type var = string

(** Basic inductive types. *)
type inductive_type = [`Empty | `Unit | `Bool]

let string_of_inductive_type = function
  | `Empty -> "Empty"
  | `Unit -> "Unit"
  | `Bool -> "Bool"

(** Basic inductive terms. *)
type inductive_term = [`Unit | `Bool of bool]

(** Side for lax arrows. *)
type side = Left | Right

let string_of_side = function
  | Left -> "l"
  | Right -> "r"

(** A term. *)
type term =
  | TType
  | TIndType of inductive_type
  | TIndType_ind of inductive_type * string * term * term * term (* type family we eliminate to, arguments, eliminated term *)
  | TIndTerm of inductive_term
  | TPi of bool * string * term * term (** pi-type *) (* boolean indicates whether crisp *)
  | TAbs of string * term
  | TApp of term * term
  | TSigma of string * term * term
  | TPair of term * term
  | TArr of side * term * term (** lax arrow type *)
  | TTens of term * term
  | TTensPair of term * term
  | TFlat of term
  | TFlatten of term
  | TFlat_ind of string * term * term * term (* as ind above *)
  | TVar of string

(** Multiple abstractions. *)
let rec tabss l t =
  match l with
  | [] -> t
  | x::l -> TAbs (x, tabss l t)

let rec string_of_term = function
  | TType -> "Type"
  | TIndType ind -> string_of_inductive_type ind
  | TIndType_ind (ind, x, a, args, t) -> Printf.sprintf "%s_ind(%s,%s,%s,%s)" (string_of_inductive_type ind) x (string_of_term a) (string_of_term args) (string_of_term t)
  | TIndTerm `Unit -> "tt"
  | TIndTerm (`Bool b) -> string_of_bool b
  | TPi (c, x, a, t) -> Printf.sprintf "(%s %s %s) → %s" x (if c then "::" else ":") (string_of_term a) (string_of_term t)
  | TAbs (x, t) -> Printf.sprintf "λ%s.%s" x (string_of_term t)
  | TApp (t, u) -> Printf.sprintf "(%s %s)" (string_of_term t) (string_of_term u)
  | TSigma (x, a, t) -> Printf.sprintf "Σ(%s : %s).%s" x (string_of_term a) (string_of_term t)
  | TPair (t, u) -> Printf.sprintf "(%s, %s)" (string_of_term t) (string_of_term u)
  | TArr (s, a, b) -> Printf.sprintf "%s →%s %s" (string_of_term a) (string_of_side s) (string_of_term b)
  | TTens (a, b) -> Printf.sprintf "(%s ⨂ %s)" (string_of_term a) (string_of_term b)
  | TTensPair (t, u) -> Printf.sprintf "(%s ⊗ %s)" (string_of_term t) (string_of_term u)
  | TFlat t -> Printf.sprintf "♭%s" (string_of_term t)
  | TFlatten t -> Printf.sprintf "flatten(%s)" (string_of_term t)
  | TFlat_ind (x,a,t,u) -> Printf.sprintf "flat_ind(%s,%s,%s,%s)" x (string_of_term a) (string_of_term t) (string_of_term u)
  | TVar x -> x

(** A value. *)
type value =
  | Type
  | IndType of inductive_type
  | IndTerm of inductive_term
  | Pi of value * closure
  | Abs of closure
  | Sigma of value * closure
  | Pair of value * value
  | Arr of side * value * value
  | Tens of value * value
  | Flat of value
  | Flatten of value
  | Neu of neutral

and neutral =
  | Var of int
  | App of neutral * value
  | IndType_ind of inductive_type * value * neutral
  | Flat_ind of closure * neutral

and closure = var * term * environment

(** An environment. *)
and environment = (var * value) list

(** Evaluate a term to a value. *)
let rec eval (env:environment) = function
  | TType -> Type
  | TIndType a -> IndType a
  | TIndTerm t -> IndTerm t
  | TIndType_ind (ind, _x, _a, args, t) ->
     (
       let args = eval env args in
       match eval env t with
       | Neu t -> Neu (IndType_ind (ind, args, t))
       | IndTerm `Unit -> assert (ind = `Unit); args
       | IndTerm (`Bool b) ->
          assert (ind = `Bool);
          (
            match args with
            | Pair (tf, tt) -> if b then tt else tf
            | _ -> assert false
          )
       | _ -> failwith "TODO: eval inductives"
     )
  | TPi (_, x, a, t) -> Pi (eval env a, (x, t, env))
  | TAbs (x, t) -> Abs (x, t, env)
  | TApp (t, u) -> vapp (eval env t) (eval env u)
  | TSigma (x, a, t) -> Sigma (eval env a, (x, t, env))
  | TPair (t, u) -> Pair (eval env t, eval env u)
  | TArr (s, a, b) -> Arr (s, eval env a, eval env b)
  | TTens (a, b) -> Tens (eval env a, eval env b)
  | TTensPair (t, u) -> Tens (eval env t, eval env u)
  | TFlat t -> Flat (eval env t)
  | TFlatten t -> Flatten (eval env t)
  | TFlat_ind (x, _, t, u) ->
     (
       let t = (x, t, env) in
       match eval env u with
       | Flatten u -> capp t u
       | Neu u -> Neu (Flat_ind (t, u))
       | _ -> failwith "vunflatten"
     )
  | TVar x ->
     (
       match List.assoc_opt x env with
       | Some v -> v
       | None -> failwith @@ Printf.sprintf "eval: could not find %s" x
     )

(** Make a variable. *)
and vvar k = Neu (Var k)

(** Apply a value to another. *)
and vapp t u =
  match t, u with
  | Abs f, u -> capp f u
  | Neu t, u -> Neu (App (t, u))
  | _ -> failwith "vapp"

and vunit = IndType `Unit
and vunit_term = IndTerm `Unit

(** Instantiate a closure with a value. *)
and capp ((x,t,env):closure) (v:value) =
  eval ((x,v)::env) t

(** Reify a value as a term. *)
let rec readback k v =
  let var k = "x" ^ string_of_int k in
  let rec neutral k = function
    | Var i -> TVar (var i)
    | App (t, u) -> TApp (neutral k t, readback k u)
    | IndType_ind (ind, args, t) ->
       (* TODO: we forget about the type... *)
       let x = "_" in
       let a = TType in
       TIndType_ind (ind, x, a, readback k args, neutral k t)
    | Flat_ind _ -> failwith "TODO"
  in
  match v with
  | Type -> TType
  | IndType ind -> TIndType ind
  | IndTerm t -> TIndTerm t
  | Pi (a, b) -> TPi (false, var k, readback k a, readback (k+1) (capp b (vvar k)))
  | Abs f -> TAbs (var k, readback (k+1) (capp f (vvar k)))
  | Sigma (a, b) -> TSigma (var k, readback k a, readback (k+1) (capp b (vvar k)))
  | Pair (t, u) -> TPair (readback k t, readback k u)
  | Arr (s, a, b) -> TArr (s, readback k a, readback k b)
  | Tens (a, b) -> TTens (readback k a, readback k b)
  | Flat a -> TFlat (readback k a)
  | Flatten t -> TFlatten (readback k t)
  | Neu t -> neutral k t

type decl = string * term * term

type decls = decl list

(** A crisp context. *)
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

(** Comparison of values. *)
let eq k (t:value) (u:value) =
  if readback k t <> readback k u then failwith "eq"

(** Check that term has given type. *)
let rec check k env ctx (t:term) (a:value) =
  Printf.printf "CHECK %s\n%!" (string_of_term t);
  let cenv, benv = ctx in
  match t, a with
  | TAbs (x, t), Pi (a, b) ->
     let xv = vvar k in
     let k = k+1 in
     let env = (x,xv)::env in
     let ctx =
       let benv = Bunch.Ext (benv, x, a) in
       cenv, benv
     in
     check k env ctx t (capp b xv)
  | TPair (t, u), Sigma (a, b) ->
     check k env ctx t a;
     let t = eval env t in
     check k env ctx u (capp b t)
  | TTensPair (t, u), Tens (a, b) ->
     (* TODO: how do we perform weakening? *)
     check k env ctx t a;
     check k env ctx u b
  | TFlatten t, Flat a ->
     check k env (cenv,Empty) t a
  | t, a ->
     eq k (infer k env ctx t) a

(** Check that a term is a type. *)
and check_type k env ctx a =
  Printf.printf "CHECK TYPE %s\n%!" (string_of_term a);
  let cenv, benv = ctx in
  match a with
  | TType -> ()
  | TPi (true, x, a, b) ->
     check_type k env (cenv,Bunch.Empty) a;
     let xv = vvar k in
     let k = k+1 in
     let env = (x,xv)::env in
     let a = eval env a in
     let ctx =
       let cenv = (x,a)::cenv in
       cenv, benv
     in
     check_type k env ctx b
  | TPi (false, x, a, b)
    | TSigma (x, a, b) ->
     check_type k env ctx a;
     let xv = vvar k in
     let k = k+1 in
     let env = (x,xv)::env in
     let a = eval env a in
     let ctx =
       let benv = Bunch.Ext (benv, x, a) in
       cenv, benv
     in
     check_type k env ctx b
  | TTens (a, b) ->
     check_type k env (cenv,Empty) a;
     check_type k env (cenv,Empty) b
  | TFlat a ->
     check_type k env (cenv,Empty) a
  | a -> check k env ctx a Type

(** Infer the type of a term. *)
and infer k env ctx (t:term) =
  Printf.printf "INFER %s\n%!" (string_of_term t);
  let cenv, benv = ctx in
  match t with
  | TIndType _ -> Type
  | TIndTerm `Unit -> IndType `Unit
  | TIndTerm (`Bool _) -> IndType `Bool
  | TIndType_ind (`Unit, x, a, args, t) ->
     let a =
       let ctx =
         let benv = Bunch.Ext (benv, x, vunit) in
         cenv, benv
       in
       check_type k env ctx a;
       (x, a, env)
     in
     check k env ctx args (capp a vunit_term);
     check k env ctx t vunit;
     capp a (eval env t)
  (* | TFlat_ind (x, a, t, u) -> *)
     (* let a = *)
       (* let ctx = *)
         (* let benv = Bunch.Ext (benv, x, vunit) in *)
         (* cenv, benv *)
       (* in *)
       (* check_type k env ctx a; *)
       (* (x, a, env) *)
     (* in *)
     (* let t = *)
  (* in *)
     (* failwith "TODO" *)
  | TApp (t, u) ->
     (
       match infer k env ctx t with
       | Pi (a, b) ->
          check k env ctx u a;
          capp b (eval env u)
       | _ -> failwith "infer app"
     )
  | TVar x ->
     (
       match Bunch.assoc_opt x benv with
       | Some a -> a
       | None ->
          match List.assoc_opt x cenv with
          | Some v -> v
          | None -> failwith @@ Printf.sprintf "infer: undefined variable %s" x
     )
  | _ -> failwith "infer"

let check_decl k env ctx (x, a, t) =
  Printf.printf "\nDECL  %s = %s\n%!" x (string_of_term t);
  check_type k env ctx a;
  let a = eval env a in
  check k env ctx t a;
  let t = eval env t in
  (x,t)::env

let check_decls k env ctx decls =
  List.fold_left (fun env decl -> check_decl k env ctx decl) env decls

let check_decls_toplevel decls = ignore @@ check_decls 0 [] ([],Bunch.Empty) decls
