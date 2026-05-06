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
  | TIndType_ind of inductive_type * term list
  | TIndTerm of inductive_term
  | TPi of bool * string * term * term (** pi-type *) (* boolean indicates whether crisp *)
  | TAbs of string * term
  | TApp of term * term
  | TSigma of string * term * term
  | TPair of term * term
  | TPair_ind of string * string * term
  | TArr of side * term * term (** lax arrow type *)
  | TTens of term * term
  | TTensPair of term * term
  | TTens_ind of string * string * term
  | TFlat of term
  | TFlatten of term
  | TFlat_ind of string * term
  | TEq of term * term
  | TRefl
  | TVar of string

module FV = struct
  include Set.Make(String)

  let rec term t =
    let list l = List.fold_left (fun fv t -> union fv (term t)) empty l in
    match t with
    | TType
    | TIndType _ -> empty
    | TIndType_ind (_, l) -> list l
    | TIndTerm _ -> empty
    | TPi (_, x, a, b)
    | TSigma (x, a, b) -> union (term a) (remove x (term b))
    | TAbs (x, t) -> remove x (term t)
    | TApp (t, u)
    | TPair (t, u) -> union (term t) (term u)
    | TPair_ind (x, y, t) -> remove x (remove y (term t))
    | TArr (_, a, b)
    | TTens (a, b) -> union (term a) (term b)
    | TTensPair (t, u) -> union (term t) (term u)
    | TTens_ind (x, y, t) -> remove x (remove y (term t))
    | TFlat a -> term a
    | TFlatten t -> term t
    | TFlat_ind (x, t) -> remove x (term t)
    | TEq (t, u) -> union (term t) (term u)
    | TRefl -> empty
    | TVar x -> singleton x
end

(** String representation of a term. *)
let rec string_of_term = function
  | TType -> "Type"
  | TIndType ind -> string_of_inductive_type ind
  | TIndType_ind (ind, args) -> Printf.sprintf "%s_ind(%s)" (string_of_inductive_type ind) (String.concat "," @@ List.map string_of_term args)
  | TIndTerm `Unit -> "tt"
  | TIndTerm (`Bool b) -> string_of_bool b
  | TPi (c, x, a, t) -> Printf.sprintf "(%s %s %s) → %s" x (if c then "::" else ":") (string_of_term a) (string_of_term t)
  | TAbs (x, t) -> Printf.sprintf "λ%s.%s" x (string_of_term t)
  | TApp (t, u) -> Printf.sprintf "(%s %s)" (string_of_term t) (string_of_term u)
  | TSigma (x, a, t) -> Printf.sprintf "(Σ(%s : %s).%s)" x (string_of_term a) (string_of_term t)
  | TPair (t, u) -> Printf.sprintf "(%s, %s)" (string_of_term t) (string_of_term u)
  | TPair_ind (x, y, t) -> Printf.sprintf "(λ(%s,%s).%s)" x y (string_of_term t)
  | TArr (s, a, b) -> Printf.sprintf "%s →%s %s" (string_of_term a) (string_of_side s) (string_of_term b)
  | TTens (a, b) -> Printf.sprintf "(%s ⨂ %s)" (string_of_term a) (string_of_term b)
  | TTensPair (t, u) -> Printf.sprintf "(%s ⊗ %s)" (string_of_term t) (string_of_term u)
  | TTens_ind (x, y, t) -> Printf.sprintf "(λ(%s⊗%s).%s)" x y (string_of_term t)
  | TFlat t -> Printf.sprintf "♭%s" (string_of_term t)
  | TFlatten t -> Printf.sprintf "flatten(%s)" (string_of_term t)
  | TFlat_ind (x,t) -> Printf.sprintf "flat_ind(%s,%s)" x (string_of_term t)
  | TEq (t,u) -> Printf.sprintf "%s = %s" (string_of_term t) (string_of_term u)
  | TRefl -> Printf.sprintf "refl"
  | TVar x -> x

(** A value. *)
type value =
  | Type
  | IndType of inductive_type
  | IndTerm of inductive_term
  | IndType_ind of inductive_type * value list
  | Pi of value * closure
  | Abs of closure
  | Sigma of value * closure
  | Pair of value * value
  | Pair_ind of closure2
  | Arr of side * value * value
  | Tens of value * value
  | Tens_ind of closure2
  | Flat of value
  | Flatten of value
  | Flat_ind of closure
  | Eq of value * value
  | Refl
  | Neu of neutral

(** A neutral term. *)
and neutral =
  | Var of int
  | App of neutral * value
  | NPair_ind of closure2 * neutral
  | NTens_ind of closure2 * neutral
  | NIndType_ind of inductive_type * value list * neutral
  | NFlat_ind of closure * neutral

(** A closure. *)
and closure = var * term * environment

(** A binary closure. *)
and closure2 = var * var * term * environment

(** An environment. *)
and environment = (var * value) list

(** Evaluate a term to a value. *)
let rec eval (env:environment) = function
  | TType -> Type
  | TIndType a -> IndType a
  | TIndTerm t -> IndTerm t
  | TIndType_ind (ind, args) -> IndType_ind (ind, List.map (eval env) args)
  | TPi (_, x, a, t) -> Pi (eval env a, (x, t, env))
  | TAbs (x, t) -> Abs (x, t, env)
  | TApp (t, u) -> vapp (eval env t) (eval env u)
  | TSigma (x, a, t) -> Sigma (eval env a, (x, t, env))
  | TPair (t, u) -> Pair (eval env t, eval env u)
  | TPair_ind (x, y, t) -> Pair_ind (x, y, t, env)
  | TArr (s, a, b) -> Arr (s, eval env a, eval env b)
  | TTens (a, b) -> Tens (eval env a, eval env b)
  | TTensPair (t, u) -> Tens (eval env t, eval env u)
  | TTens_ind (x, y, t) -> Tens_ind (x, y, t, env)
  | TFlat t -> Flat (eval env t)
  | TFlatten t -> Flatten (eval env t)
  | TFlat_ind (x, t) -> Flat_ind (x,t,env)
  | TEq (t, u) -> Eq (eval env t, eval env u)
  | TRefl -> Refl
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
  | IndType_ind (`Unit, [t]), IndTerm `Unit -> t
  | IndType_ind (`Bool, [tf;_tt]), IndTerm (`Bool false) -> tf
  | IndType_ind (`Bool, [_tf;tt]), IndTerm (`Bool true) -> tt
  | IndType_ind (ind, t), Neu u -> Neu (NIndType_ind (ind, t, u))
  | Neu t, u -> Neu (App (t, u))
  | _ -> failwith "vapp"

(** Instantiate a closure with a value. *)
and capp ((x,t,env):closure) (v:value) =
  eval ((x,v)::env) t

and capp2 ((x,y,t,env):closure2) (u:value) (v:value) =
  eval ((y,v)::(x,u)::env) t

(** Reify a value as a term. *)
let rec readback k v =
  let var k = "x" ^ string_of_int k in
  let rec neutral k = function
    | Var i -> TVar (var i)
    | App (t, u) -> TApp (neutral k t, readback k u)
    | NPair_ind (t, u) -> TApp (readback k @@ Pair_ind t, neutral k u)
    | NTens_ind (t, u) -> TApp (readback k @@ Tens_ind t, neutral k u)
    | NIndType_ind (ind, args, t) -> TApp (readback k @@ IndType_ind (ind, args), neutral k t)
    | NFlat_ind (t, u) -> TApp (readback k @@ Flat_ind t, neutral k u)
  in
  match v with
  | Type -> TType
  | IndType ind -> TIndType ind
  | IndType_ind (ind, args) -> TIndType_ind (ind, List.map (readback k) args)
  | IndTerm t -> TIndTerm t
  | Pi (a, b) -> TPi (false, var k, readback k a, readback (k+1) (capp b (vvar k)))
  | Abs f -> TAbs (var k, readback (k+1) (capp f (vvar k)))
  | Sigma (a, b) -> TSigma (var k, readback k a, readback (k+1) (capp b (vvar k)))
  | Pair (t, u) -> TPair (readback k t, readback k u)
  | Pair_ind t -> TPair_ind (var k, var (k+1), readback (k+2) @@ capp2 t (vvar k) (vvar (k+1)))
  | Arr (s, a, b) -> TArr (s, readback k a, readback k b)
  | Tens (a, b) -> TTens (readback k a, readback k b)
  | Tens_ind (t) -> TTens_ind (var k, var (k+1), readback (k+2) @@ capp2 t (vvar k) (vvar (k+1)))
  | Flat a -> TFlat (readback k a)
  | Flatten t -> TFlatten (readback k t)
  | Flat_ind t -> TFlat_ind (var k, readback (k+1) (capp t (vvar k)))
  | Eq (t, u) -> TEq (readback k t, readback k u)
  | Refl -> TRefl
  | Neu t -> neutral k t

let string_of_value k v = string_of_term @@ readback k v

(** A declaration. *)
type decl = string * term * term

type decls = decl list

(** A crisp context. *)
type crisp = (var * value) list

(** Operation on bunched contexts. *)
module Bunch = struct
  (** A bunched context. *)
  type t =
    | Empty
    | Ext of t * string * value
    | L of l

  and l =
    | One
    | Tens of l * t

  let rec to_string k = function
    | Empty -> "()"
    | Ext (env,x,a) -> Printf.sprintf "%s,%s:%s" (to_string k env) x (string_of_value k a)
    | L l -> Printf.sprintf "(%s)" (to_stringl k l)
  and to_stringl k = function
    | One -> "()"
    | Tens (l,env) -> Printf.sprintf "%s⊗(%s)" (to_stringl k l) (to_string k env)

  (** Find the type of a variable. *)
  let rec assoc_opt x = function
    | Empty -> None
    | Ext (env, y, a) -> if x = y then Some a else assoc_opt x env
    | L l -> assocl_opt x l
  and assocl_opt x = function
    | One -> None
    | Tens (lenv, env) ->
       (
         match assoc_opt x env with
         | Some a -> Some a
         | None -> assocl_opt x lenv
       )

  (** Domain of a bunch. *)
  let rec dom b =
    let rec doml = function
      | One -> FV.empty
      | Tens (l,b) -> FV.union (doml l) (dom b)
    in
    match b with
    | Empty -> FV.empty
    | Ext (b,x,_) -> FV.add x (dom b)
    | L l -> doml l

      (*
  (** Split a buch so that we have the given free variables. *)
  (* TODO: do we only want to split at toplevel? *)
  let rec splitl fvl fvr l =
    if FV.is_empty fvl then One, l
    else if FV.is_empty fvr then l, One
    else
      match l with
      | One -> failwith "splitl"
      | Tens (l, b) ->
         let fv = FV.diff fv (dom b) in
         let l1, l2 = splitl fv l in
         l1, Tens (l2, b)

  let split fv = function
    | Empty -> Empty, Empty
    | Ext _ as b -> Empty, b (* TODO: can we do better? *)
    | L l -> Pair.map (fun l -> L l) (fun l -> L l) @@ splitl fv l
       *)

    (* TODO *)
    let split _fvl _fvr b = b, b
end

(** A bunched context. *)
type bunch = Bunch.t

(** Contexts. *)
module Context = struct
  type t = crisp * bunch

  let empty : t = [],Bunch.Empty

  let ext ((cenv,benv):t) x a : t = cenv,Bunch.Ext(benv,x,a)

  let split fvl fvr (cenv,benv) =
    let l, r = Bunch.split fvl fvr benv in
    (cenv,l),(cenv,r)
end

(** A context. *)
type context = Context.t

(** Comparison of values. *)
let eq k (t:value) (u:value) =
  if readback k t <> readback k u then failwith "eq"

(** Check that term has given type. *)
let rec check k env ctx (t:term) (a:value) =
  Printf.printf "CHECK %s : %s\n%!" (string_of_term t) (string_of_value k a);
  let cenv, benv = ctx in
  (* Printf.printf ". cenv: %s\n" (String.concat ", " @@ List.map (fun (x,a) -> x ^ ":" ^ string_of_value k a) cenv); *)
  match t, a with
  | TAbs (x, t), Pi (a, b) ->
     let xv = vvar k in
     let k = k+1 in
     let env = (x,xv)::env in
     let ctx = Context.ext ctx x a in
     check k env ctx t (capp b xv)
  | TPair (t, u), Sigma (a, b) ->
     check k env ctx t a;
     let t = eval env t in
     check k env ctx u (capp b t)
  | TPair_ind (x, y, t), Pi (a, b) ->
    (
      match a with
      | Sigma (a1, a2) ->
        let x1 = vvar k in
        let x2 = vvar (k+1) in
        let k = k+2 in
        let env = (y,x2)::(x,x1)::env in
        let ctx = Context.ext (Context.ext ctx x a1) y (capp a2 x1) in
        check k env ctx t (capp b (Pair (x1, x2)))
      | _ -> failwith "pair_ind"
    )
  | TTensPair (t, u), Tens (a, b) ->
    (* TODO: fix split *)
    let ctxa, ctxb = Context.split (FV.term t) (FV.term u) ctx in
    check k env ctxa t a;
    check k env ctxb u b
  | TTens_ind (x, y, t), Pi (a, b) ->
    (
      match a with
      | Tens (a1, a2) ->
        (* TODO: properly split context *)
        let x1 = vvar k in
        let x2 = vvar (k+1) in
        let k = k+2 in
        let env = (y,x2)::(x,x1)::env in
        let ctx = Context.ext (Context.ext ctx x a1) y a2 in
        check k env ctx t (capp b (Tens (x1, x2)))
      | _ -> failwith "tens_ind"
    )
  | TIndType_ind (`Unit, [t]), Pi (a, b) ->
     eq k (IndType `Unit) a;
     check k env ctx t (capp b (IndTerm `Unit))
  | TIndType_ind (`Bool, [tf;tt]), Pi (a, b) ->
     eq k (IndType `Bool) a;
     check k env ctx tf (capp b (IndTerm (`Bool false)));
     check k env ctx tt (capp b (IndTerm (`Bool true)));
  | TFlatten t, Flat a ->
     check k env (cenv,Empty) t a
  | TFlat_ind (x, t), Pi (a, b) ->
     let a =
       match a with
       | Flat a -> a
       | _ -> failwith "flat type expected"
     in
     let xv = vvar k in
     let k = k+1 in
     check k ((x,xv)::env) ((x,a)::cenv,benv) t (capp b xv)
  | TRefl, Eq (t, u) -> eq k t u
  | t, a ->
     eq k (infer k env ctx t) a

(** Check that a term is a type. *)
and check_type k env ctx a =
  Printf.printf "CHECK TYPE %s\n%!" (string_of_term a);
  let cenv, benv = ctx in
  (* Printf.printf ". benv: %s\n%!" (Bunch.to_string k benv); *)
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
  | TEq (t, u) ->
     let a = infer k env ctx t in
     check k env ctx u a
  | a ->
     check k env ctx a Type
     (*
     (
       match infer k env ctx a with
       | Type | Flat Type -> ()
       | _ -> failwith "check type"
     )
     *)

(** Infer the type of a term. *)
and infer k env ctx (t:term) =
  Printf.printf "INFER %s\n%!" (string_of_term t);
  let cenv, benv = ctx in
  match t with
  | TIndType _ -> Type
  | TIndTerm `Unit -> IndType `Unit
  | TIndTerm (`Bool _) -> IndType `Bool
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
  let env = (x,t)::env in
  let ctx = Context.ext ctx x a in
  env, ctx

let check_decls k env ctx decls =
  List.fold_left (fun (env,ctx) decl -> check_decl k env ctx decl) (env,ctx) decls

let check_decls_toplevel decls = ignore @@ check_decls 0 [] Context.empty decls
