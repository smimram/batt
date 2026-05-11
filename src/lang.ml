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
  | Left -> "ₗ"
  | Right -> "ᵣ"

let string_of_opt_side s =
  Option.value ~default:"" @@ Option.map string_of_side s

type crispness = Crisp | Normal

(** A term. *)
type term =
  | TType
  | TIndType of inductive_type
  | TIndType_ind of inductive_type * term list
  | TIndTerm of inductive_term
  | TPi of crispness * string * term * term (** pi-type *)
  | TAbs of side option * string * term
  | TApp of side option * term * term
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
  | TJ of term
  | TVar of string
  | TLet of string * term * term * term

module FV = struct
  include Set.Make(String)

  let to_string fv = String.concat "," @@ List.of_seq @@ to_seq fv

  let rec term t =
    let list l = List.fold_left (fun fv t -> union fv (term t)) empty l in
    match t with
    | TType
    | TIndType _ -> empty
    | TIndType_ind (_, l) -> list l
    | TIndTerm _ -> empty
    | TPi (_, x, a, b)
    | TSigma (x, a, b) -> union (term a) (remove x (term b))
    | TAbs (_, x, t) -> remove x (term t)
    | TApp (_, t, u)
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
    | TJ (r) -> term r
    | TVar x -> singleton x
    | TLet (_x, a, t, u) -> union (term a) @@ union (term t) (term u)
end

(** String representation of a term. *)
let rec string_of_term = function
  | TType -> "Type"
  | TIndType ind -> string_of_inductive_type ind
  | TIndType_ind (ind, args) -> Printf.sprintf "%s_ind(%s)" (string_of_inductive_type ind) (String.concat "," @@ List.map string_of_term args)
  | TIndTerm `Unit -> "tt"
  | TIndTerm (`Bool b) -> string_of_bool b
  | TPi (c, x, a, t) -> Printf.sprintf "(%s %s %s) → %s" x (match c with Crisp -> "::" | Normal -> ":") (string_of_term a) (string_of_term t)
  | TAbs (s, x, t) -> Printf.sprintf "λ%s%s.%s" x (string_of_opt_side s) (string_of_term t)
  | TApp (s, t, u) -> Printf.sprintf "(%s @%s %s)" (string_of_term t) (string_of_opt_side s) (string_of_term u)
  | TSigma (x, a, t) -> Printf.sprintf "(Σ(%s : %s).%s)" x (string_of_term a) (string_of_term t)
  | TPair (t, u) -> Printf.sprintf "(%s, %s)" (string_of_term t) (string_of_term u)
  | TPair_ind (x, y, t) -> Printf.sprintf "(λ(%s,%s).%s)" x y (string_of_term t)
  | TArr (s, a, b) -> Printf.sprintf "%s →%s %s" (string_of_term a) (string_of_side s) (string_of_term b)
  | TTens (a, b) -> Printf.sprintf "(%s ⨂ %s)" (string_of_term a) (string_of_term b)
  | TTensPair (t, u) -> Printf.sprintf "(%s ⊗ %s)" (string_of_term t) (string_of_term u)
  | TTens_ind (x, y, t) -> Printf.sprintf "(λ(%s⊗%s).%s)" x y (string_of_term t)
  | TFlat t -> Printf.sprintf "♭%s" (string_of_term t)
  | TFlatten t -> Printf.sprintf "𝄫%s" (string_of_term t)
  | TFlat_ind (x,t) -> Printf.sprintf "♭_ind(%s,%s)" x (string_of_term t)
  | TEq (t,u) -> Printf.sprintf "%s = %s" (string_of_term t) (string_of_term u)
  | TRefl -> Printf.sprintf "refl"
  | TJ (r) -> Printf.sprintf "J(%s)" (string_of_term r)
  | TVar x -> x
  | TLet (x,a,t,u) -> Printf.sprintf "let %s : %s = %s in %s" x (string_of_term a) (string_of_term t) (string_of_term u)

(** A value. *)
type value =
  | Type
  | IndType of inductive_type
  | IndTerm of inductive_term
  | IndType_ind of inductive_type * value list
  | Pi of crispness * value * closure
  | Abs of side option * closure
  | Sigma of value * closure
  | Pair of value * value
  | Pair_ind of closure2
  | Arr of side * value * value
  | Tens of value * value
  | TensPair of value * value
  | Tens_ind of closure2
  | Flat of value
  | Flatten of value
  | Flat_ind of closure
  | Eq of value * value
  | Refl
  | J of value
  | Neu of neutral

(** A neutral term. *)
and neutral =
  | Var of int
  | App of side option * neutral * value
  | NPair_ind of closure2 * neutral
  | NTens_ind of closure2 * neutral
  | NIndType_ind of inductive_type * value list * neutral
  | NFlat_ind of closure * neutral
  | NJ of value * neutral

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
  | TPi (c, x, a, t) -> Pi (c, eval env a, (x, t, env))
  | TAbs (s, x, t) -> Abs (s, (x, t, env))
  | TApp (_, t, u) -> vapp (eval env t) (eval env u)
  | TSigma (x, a, t) -> Sigma (eval env a, (x, t, env))
  | TPair (t, u) -> Pair (eval env t, eval env u)
  | TPair_ind (x, y, t) -> Pair_ind (x, y, t, env)
  | TArr (s, a, b) -> Arr (s, eval env a, eval env b)
  | TTens (a, b) -> Tens (eval env a, eval env b)
  | TTensPair (t, u) -> TensPair (eval env t, eval env u)
  | TTens_ind (x, y, t) -> Tens_ind (x, y, t, env)
  | TFlat t -> Flat (eval env t)
  | TFlatten t -> Flatten (eval env t)
  | TFlat_ind (x, t) -> Flat_ind (x,t,env)
  | TEq (t, u) -> Eq (eval env t, eval env u)
  | TRefl -> Refl
  | TJ r -> J (eval env r)
  | TVar x ->
    (
      match List.assoc_opt x env with
      | Some v -> v
      | None -> failwith @@ Printf.sprintf "eval: could not find %s" x
    )
  | TLet (x,_a,t,u) ->
    eval env (TApp (None, TAbs(None, x, u), t))

(** Make a variable. *)
and vvar k = Neu (Var k)

(** Apply a value to another. *)
and vapp t u =
  match t, u with
  | Abs (_, f), u -> capp f u
  | IndType_ind (`Unit, [t]), IndTerm `Unit -> t
  | IndType_ind (`Bool, [tf;_tt]), IndTerm (`Bool false) -> tf
  | IndType_ind (`Bool, [_tf;tt]), IndTerm (`Bool true) -> tt
  | IndType_ind (ind, t), Neu u -> Neu (NIndType_ind (ind, t, u))
  | Pair_ind t, Pair (u, v) -> capp2 t u v
  | Pair_ind t, Neu u -> Neu (NPair_ind (t, u))
  | Tens_ind t, TensPair (u, v) -> capp2 t u v
  | Tens_ind t, Neu u -> Neu (NTens_ind (t, u))
  | Flat_ind t, Flatten u -> capp t u
  | Flat_ind t, Neu u -> Neu (NFlat_ind (t, u))
  | J r, Refl -> r
  | J r, Neu t -> Neu (NJ (r, t))
  | Neu t, u -> Neu (App (None, t, u))
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
    | App (s, t, u) -> TApp (s, neutral k t, readback k u)
    | NPair_ind (t, u) -> TApp (None, readback k @@ Pair_ind t, neutral k u)
    | NTens_ind (t, u) -> TApp (None, readback k @@ Tens_ind t, neutral k u)
    | NIndType_ind (ind, args, t) -> TApp (None, readback k @@ IndType_ind (ind, args), neutral k t)
    | NFlat_ind (t, u) -> TApp (None, readback k @@ Flat_ind t, neutral k u)
    | NJ (r, t) -> TApp (None, readback k @@ J r, neutral k t)
  in
  match v with
  | Type -> TType
  | IndType ind -> TIndType ind
  | IndType_ind (ind, args) -> TIndType_ind (ind, List.map (readback k) args)
  | IndTerm t -> TIndTerm t
  | Pi (c, a, b) -> TPi (c, var k, readback k a, readback (k+1) (capp b (vvar k)))
  | Abs (s, f) -> TAbs (s, var k, readback (k+1) (capp f (vvar k)))
  | Sigma (a, b) -> TSigma (var k, readback k a, readback (k+1) (capp b (vvar k)))
  | Pair (t, u) -> TPair (readback k t, readback k u)
  | Pair_ind t -> TPair_ind (var k, var (k+1), readback (k+2) @@ capp2 t (vvar k) (vvar (k+1)))
  | Arr (s, a, b) -> TArr (s, readback k a, readback k b)
  | Tens (a, b) -> TTens (readback k a, readback k b)
  | TensPair (t, u) -> TTensPair (readback k t, readback k u)
  | Tens_ind (t) -> TTens_ind (var k, var (k+1), readback (k+2) @@ capp2 t (vvar k) (vvar (k+1)))
  | Flat a -> TFlat (readback k a)
  | Flatten t -> TFlatten (readback k t)
  | Flat_ind t -> TFlat_ind (var k, readback (k+1) (capp t (vvar k)))
  | Eq (t, u) -> TEq (readback k t, readback k u)
  | Refl -> TRefl
  | J r -> TJ (readback k r)
  | Neu t -> neutral k t

let string_of_value k v = string_of_term @@ readback k v

(** A declaration. *)
type decl = string * crispness * term * term

type decls = decl list

(** A crisp context. *)
type crisp = (var * value) list

(** Operation on bunched contexts. *)
module Bunch = struct
  (** A bunched context. *)
  type t =
    | Empty
    | Decl of string * value
    | Prod of t * t
    | Tens of t * t

  let rec to_string k = function
    | Empty -> "()"
    | Decl (x, a) -> Printf.sprintf "%s:%s" x (string_of_value k a)
    | Prod (l,r) -> Printf.sprintf "%s,%s" (to_string k l) (to_string k r)
    | Tens (l,r) -> Printf.sprintf "%s⊗%s" (to_string k l) (to_string k r)

  let ext ctx x a = Prod (ctx,Decl(x,a))
  
  let ext_tens ctx s x a =
    let ext = Decl (x, a) in
    match s with
    | Left -> Tens (ext, ctx)
    | Right -> Tens (ctx, ext)

  (** Find the type of a variable. *)
  let rec assoc_opt x = function
    | Empty -> None
    | Decl (y, a) -> if x = y then Some a else None
    | Prod (l, r)
    | Tens (l, r) ->
      (
        match assoc_opt x r with
        | Some a -> Some a
        | None -> assoc_opt x l
      )

  (** Domain of a bunch. *)
  let rec dom b =
    match b with
    | Empty -> FV.empty
    | Decl (x,_) -> FV.singleton x
    | Prod (l,r)
    | Tens (l,r) -> FV.union (dom l) (dom r)

  (** Split a buch so that we have the given free variables. *)
  (* TODO: do we only want to split at toplevel? *)
  let split fvl fvr crisp b =
    assert (FV.is_empty @@ FV.inter fvl fvr);
    let fvc = FV.of_list @@ List.map fst crisp in
    (* Printf.printf "crisp: %s\n%!" @@ FV.to_string fvc; *)
    let rec aux fvl fvr b =
      match b with
      | b when FV.is_empty fvl -> Empty, b
      | b when FV.is_empty fvr -> b, Empty
      | Empty -> Empty, Empty
      | Tens (b1, b2) ->
        let fv1 = FV.union fvc @@ dom b1 in
        let fv2 = FV.union fvc @@ dom b2 in
        if FV.subset fvl fv1 && FV.subset fvr fv2 then b1, b2
        else if FV.subset fvl fv1 then
          let b1', b1'' = aux fvl (FV.diff fvr fv2) b1 in
          b1', Tens (b1'', b2)
        else if FV.subset fvr fv2 then
          let b2', b2'' = aux (FV.diff fvl fv1) fvr b2 in
          Tens (b1, b2'), b2''
        else if not @@ FV.subset (FV.union fvl fvr) (FV.union fv1 fv2) then failwith @@ Printf.sprintf "split: undefined variables: %s" @@ FV.to_string (FV.diff (FV.union fvl fvr) (FV.union fv1 fv2))
        else failwith "split"
      | Prod (Empty, b)
      | Prod (b, Empty) -> aux fvl fvr b
      | Decl _ -> failwith @@ Printf.sprintf "trying to split %s as %s / %s" (to_string 0 b) (FV.to_string fvl) (FV.to_string fvr)
      | Prod _ (* (b1, b2) *) ->
        (* let fv = FV.union fvl fvr in *)
        (* if FV.subset fv (dom b1) then split fvl fvr b1 *)
        (* else if FV.subset fv (dom b2) then *)
        (* TODO: we should check that b2 does not depend on b1... *)
        (* split fvl fvr b2 *)
        (* else *)
        failwith @@ Printf.sprintf "TODO: split prod: %s" @@ to_string 0 b
    in
    aux fvl fvr b
end

(** A bunched context. *)
type bunch = Bunch.t

(** Contexts. *)
module Context = struct
  type t = crisp * bunch

  let to_string k (cenv,benv) =
    let cenv = String.concat ", " @@ List.map (fun (x,a) -> Printf.sprintf "%s:%s" x (string_of_value k a)) cenv in
    let benv = Bunch.to_string k benv in
    Printf.sprintf "%s / %s" cenv benv

  let empty : t = [],Bunch.Empty

  let ext ((cenv,benv):t) x a : t = cenv, Bunch.ext benv x a

  let ext_tens (cenv,benv) s x a = cenv, Bunch.ext_tens benv s x a

  let ext_crisp ((cenv,benv):t) x a : t = ((x,a)::cenv), benv

  let ext ctx ?(crispness=Normal) x a =
    match crispness with
    | Normal -> ext ctx x a
    | Crisp -> ext_crisp ctx x a

  let crisp (cenv,_) : t = cenv,Bunch.Empty

  let crisp ?(crispness=Crisp) ctx =
    match crispness with
    | Crisp -> crisp ctx
    | Normal -> ctx

  let assoc_opt x (cenv,benv) =
    match Bunch.assoc_opt x benv with
    | Some a -> Some a
    | None -> List.assoc_opt x cenv

  let split fvl fvr (cenv,benv) =
    let l, r = Bunch.split fvl fvr cenv benv in
    (cenv,l),(cenv,r)
end

(** A context. *)
type context = Context.t

(** Comparison of values. *)
let is_eq k (t:value) (u:value) =
  readback k t = readback k u

let eq k t u =
  if not @@ is_eq k t u then failwith "eq"

(** Check that term has given type. *)
let rec check k env ctx (t:term) (a:value) =
  Printf.printf "CHECK %s : %s\n%!" (string_of_term t) (string_of_value k a);
  (* let cenv, benv = ctx in *)
  (* Printf.printf ". cenv: %s\n%!" (Context.to_string k ctx); *)
  match t, a with
  | TAbs (None, x, t), Pi (c, a, b) ->
    let xv = vvar k in
    let k = k+1 in
    let env = (x,xv)::env in
    let ctx = Context.ext ~crispness:c ctx x a in
    check k env ctx t (capp b xv)
  | TAbs (Some s, x, t), Arr (s', a, b) ->
    assert (s = s');
    (* TODO: fix this *)
    let xv = vvar k in
    let k = k+1 in
    let env = (x,xv)::env in
    let ctx = Context.ext_tens ctx s x a in
    check k env ctx t b
  | TLet (x, a, t, u), b ->
    let a = eval env a in
    check k env ctx t a;
    let xv = vvar k in
    let k = k+1 in
    let env = (x,xv)::env in
    let ctx = Context.ext ctx x a in
    check k env ctx u b
  | TPair (t, u), Sigma (a, b) ->
    check k env ctx t a;
    let t = eval env t in
    check k env ctx u (capp b t)
  | TPair_ind (x, y, t), Pi (c, a, b) ->
    (
      match a with
      | Sigma (a1, a2) ->
        let x1 = vvar k in
        let x2 = vvar (k+1) in
        let k = k+2 in
        let env = (y,x2)::(x,x1)::env in
        let ctx = Context.ext ~crispness:c (Context.ext ctx x a1) y (capp a2 x1) in
        check k env ctx t (capp b (Pair (x1, x2)))
      | _ -> failwith "pair_ind"
    )
  | TTensPair (t, u), Tens (a, b) ->
    let ctxa, ctxb = Context.split (FV.term t) (FV.term u) ctx in
    check k env ctxa t a;
    check k env ctxb u b
  | TTens_ind (x, y, t), Pi (c, a, b) ->
    (
      match a with
      | Tens (a1, a2) ->
        (* TODO: properly split context *)
        let x' = vvar k in
        let y' = vvar (k+1) in
        let k = k+2 in
        let env = (y,y')::(x,x')::env in
        let ctx =
          match c with
          | Normal ->
            let cctx, bctx = ctx in
            let bctx = Bunch.Prod (bctx, Bunch.Tens (Bunch.Decl (x, a1), Bunch.Decl (y, a2))) in
            cctx, bctx
          | Crisp -> Context.ext_crisp (Context.ext_crisp ctx x a1) y a2
        in
        check k env ctx t (capp b (Tens (x', y')))
      | _ -> failwith "tens_ind"
    )
  | TIndType_ind (`Empty, []), Pi (_, a, _) ->
    eq k (IndType `Empty) a
  | TIndType_ind (`Unit, [t]), Pi (_, a, b) ->
    eq k (IndType `Unit) a;
    check k env ctx t (capp b (IndTerm `Unit))
  | TIndType_ind (`Bool, [tf;tt]), Pi (_, a, b) ->
    eq k (IndType `Bool) a;
    check k env ctx tf (capp b (IndTerm (`Bool false)));
    check k env ctx tt (capp b (IndTerm (`Bool true)));
  | TFlatten t, Flat a ->
    check k env (Context.crisp ctx) t a
  | TFlat_ind (x, t), Pi (Normal, a, b) ->
    let a =
      match a with
      | Flat a -> a
      | _ -> failwith "flat type expected"
    in
    let xv = vvar k in
    let k = k+1 in
    check k ((x,xv)::env) (Context.ext_crisp ctx x a) t (capp b (Flatten xv))
  | TRefl, Eq (t, u) -> eq k t u
  | TJ r, Pi (Normal, a, b) ->
    let unpi = function
      | Pi (_, a, b) -> a, b
      | _ -> assert false
    in
    let x, k = vvar k, k+1 in
    let b, c = unpi (capp b x) in
    eq k a b;
    let y, k = vvar k, k+1 in
    let c', _ = unpi (capp c y) in
    eq k c' (Eq (x, y));
    let _, d = unpi (capp c x) in
    let d = capp d Refl in
    check k env ctx r d
  | TPi _, Type -> check_type k env ctx t
  | t, a ->
    let a' = infer k env ctx t in
    if not @@ is_eq k a' a then
      failwith @@ Printf.sprintf "%s has type %s but %s expected" (string_of_term t) (string_of_value k a') (string_of_value k a)

(** Check that a term is a type. *)
and check_type k env ctx a =
  Printf.printf "CHECK TYPE %s\n%!" (string_of_term a);
  (* let cenv, benv = ctx in *)
  (* Printf.printf ". ctx: %s\n%!" (Context.to_string k ctx); *)
  match a with
  | TType -> ()
  | TPi (Crisp, x, a, b) ->
    check_type k env (Context.crisp ctx) a;
    let xv = vvar k in
    let k = k+1 in
    let env = (x,xv)::env in
    let a = eval env a in
    let ctx = Context.ext_crisp ctx x a in
    check_type k env ctx b
  | TPi (Normal, x, a, b)
  | TSigma (x, a, b) ->
    check_type k env ctx a;
    let xv = vvar k in
    let k = k+1 in
    let env = (x,xv)::env in
    let a = eval env a in
    let ctx = Context.ext ctx x a in
    check_type k env ctx b
  | TTens (a, b) ->
    check_type k env (Context.crisp ctx) a;
    check_type k env (Context.crisp ctx) b
  | TArr (_, a, b) ->
    check_type k env (Context.crisp ctx) a;
    check_type k env (Context.crisp ctx) b    
  | TFlat a ->
    check_type k env (Context.crisp ctx) a
  | TEq (t, u) ->
    let a = infer k env ctx t in
    check k env ctx u a
  | a ->
    check k env ctx a Type

(** Infer the type of a term. *)
and infer k env ctx (t:term) =
  Printf.printf "INFER %s\n%!" (string_of_term t);
  (* let cenv, benv = ctx in *)
  match t with
  | TIndType _ -> Type
  | TIndTerm `Unit -> IndType `Unit
  | TIndTerm (`Bool _) -> IndType `Bool
  | TApp (None, t, u) ->
    (
      match infer k env ctx t with
      | Pi (c, a, b) ->
        check k env (Context.crisp ~crispness:c ctx) u a;
        capp b (eval env u)
      | _ -> failwith "infer app"
    )
  | TVar x ->
    (
      match Context.assoc_opt x ctx with
      | Some a -> a
      | None -> failwith @@ Printf.sprintf "infer: undefined variable %s" x
    )
  | _ -> failwith "infer"

let check_decl k env ctx (x, c, a, t) =
  Printf.printf "\nDECL  %s = %s %s %s\n%!" x (string_of_term t) (match c with Normal -> ":" | Crisp -> "::") (string_of_term a);
  check_type k env ctx a;
  let a = eval env a in
  check k env (Context.crisp ~crispness:c ctx) t a;
  let t = eval env t in
  let env = (x,t)::env in
  let ctx = Context.ext ~crispness:c ctx x a in
  env, ctx

let check_decls k env ctx (decls:decls) =
  List.fold_left (fun (env,ctx) decl -> check_decl k env ctx decl) (env,ctx) decls

let check_decls_toplevel decls = ignore @@ check_decls 0 [] Context.empty decls
