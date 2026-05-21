open Common

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

type icit = Explicit | Implicit

type crispness = Normal | Crisp

(** A term. *)
type term =
  | TType
  | TIndType of inductive_type
  | TIndType_ind of inductive_type * term list
  | TIndTerm of inductive_term
  | TPi of icit * crispness * string * term * term (** pi-type *)
  | TAbs of icit * side option * string * term
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
  | TJ of term
  | TVar of var
  | TLet of crispness * string * term * term * term
  | TPostulate (** a postulate *)
  | THole of Pos.t
  | TMeta of int option (** metavariable with given internal identifier *)

let rec app_spine t = function
  | u::uu -> TApp (app_spine t uu, u)
  | [] -> t

(** Canonical variable with given number. *)
let varn n = "x" ^ string_of_int n

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
    | TPi (_, _, x, a, b)
    | TSigma (x, a, b) -> union (term a) (remove x (term b))
    | TAbs (_, _, x, t) -> remove x (term t)
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
    | TJ (r) -> term r
    | TVar x -> singleton x
    | TLet (_c, _x, a, t, u) -> union (term a) @@ union (term t) (term u)
    | TPostulate -> empty
    | THole _ -> empty
    | TMeta _ -> empty
end

(** String representation of a term. *)
let rec string_of_term t =
  let colon = function
    | Normal -> ":"
    | Crisp -> "∷"
  in
  match t with
  | TType -> "Type"
  | TIndType ind -> string_of_inductive_type ind
  | TIndType_ind (ind, args) -> Printf.sprintf "%s_ind(%s)" (string_of_inductive_type ind) (String.concat "," @@ List.map string_of_term args)
  | TIndTerm `Unit -> "tt"
  | TIndTerm (`Bool b) -> string_of_bool b
  | TPi (i, c, x, a, t) ->
    (
      match i with
      | Explicit -> Printf.sprintf "(%s %s %s) → %s" x (colon c) (string_of_term a) (string_of_term t)
      | Implicit -> Printf.sprintf "{%s %s %s} → %s" x (colon c) (string_of_term a) (string_of_term t)
    )
  | TAbs (i, s, x, t) ->
    (
      match i with
      | Explicit -> Printf.sprintf "λ%s%s.%s" x (string_of_opt_side s) (string_of_term t)
      | Implicit -> Printf.sprintf "λ{%s%s}.%s" x (string_of_opt_side s) (string_of_term t)
    )
  | TApp (t, u) -> Printf.sprintf "(%s %s)" (string_of_term t) (string_of_term u)
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
  | TEq (t,u) -> Printf.sprintf "%s ≡ %s" (string_of_term t) (string_of_term u)
  | TRefl -> Printf.sprintf "refl"
  | TJ (r) -> Printf.sprintf "J(%s)" (string_of_term r)
  | TVar x -> x
  | TLet (c,x,a,t,u) -> Printf.sprintf "let %s %s %s = %s in %s" x (colon c) (string_of_term a) (string_of_term t) (string_of_term u)
  | TPostulate -> "postulate"
  | THole _ -> "?"
  | TMeta None -> "_"
  | TMeta (Some n) -> Printf.sprintf "?%d" n

(** A value. *)
type value =
  | Type
  | IndType of inductive_type
  | IndTerm of inductive_term
  | IndType_ind of inductive_type * value list
  | Pi of icit * crispness * value * closure
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
  | Meta of meta * spine
  | Neu of neutral

(** A neutral term. *)
and neutral =
  | Var of int
  | Hole of Pos.t
  | Postulate
  | App of neutral * value
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

(** A metavariable. *)
and meta =
  {
    id : int;
    mutable value : value option;
  }

(** A list of arguments: first in the list, last to be applied. *)
and spine = value list

(** Metavariables. *)
module Meta = struct
  type t = meta

  (* Backward compatibility. *)
  module Dynarray = struct
    type 'a t = 'a array ref
    let create () : 'a t = ref [||]
    let length (a : 'a t) = Array.length !a
    let add_last (a : 'a t) x = a := Array.append !a [|x|]
    let get (a : 'a t) i = Array.get !a i
  end

  let variables = Dynarray.create ()

  (** Generate a fresh metavariable. *)
  let fresh () =
    let m = { id = Dynarray.length variables; value = None } in
    Dynarray.add_last variables m;
    m

  (** Get metavariable with given id. *)
  let get id =
    Dynarray.get variables id
end

(** Evaluate a term to a value. *)
let rec eval (env:environment) = function
  | TType -> Type
  | TIndType a -> IndType a
  | TIndTerm t -> IndTerm t
  | TIndType_ind (ind, args) -> IndType_ind (ind, List.map (eval env) args)
  | TPi (i, c, x, a, t) -> Pi (i, c, eval env a, (x, t, env))
  | TAbs (_, s, x, t) -> Abs (s, (x, t, env))
  | TApp (t, u) -> vapp (eval env t) (eval env u)
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
  | TLet (_c,x,_a,t,u) ->
    eval env (TApp (TAbs(Explicit, None, x, u), t))
  | TPostulate -> Neu Postulate
  | THole pos -> Neu (Hole pos)
  | TMeta None -> fresh_meta env
  | TMeta (Some id) -> Meta (Meta.get id, [])

(** Make a variable. *)
and vvar k = Neu (Var k)

(** Generate a fresh metavariable. *)
and fresh_meta env =
  let m = Meta.fresh () in
  (* We only keep variables in the environment. *)
  let vars = List.filter_map (fun (x,v) -> match force v with Neu (Var _) -> Some (TVar x) | _ -> None) env |> List.map (eval env) in
  Meta (m, vars)

(** Apply a value to another. *)
and vapp t u =
  match force t, u with
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
  | Meta (m, s), u -> Meta (m, u::s)
  | Neu t, u -> Neu (App (t, u))
  | _ -> failwith "vapp"

(** Apply a value to a list of values. *)
and vapps t = function
  | u::uu -> vapps (vapp t u) uu
  | [] -> t

(** Apply a value to a spine of values. *)
and vapp_spine t = function
  | u::uu -> vapp (vapp_spine t uu) u
  | [] -> t

(** Instantiate a closure with a value. *)
and capp ((x,t,env):closure) (v:value) =
  eval ((x,v)::env) t

and capp2 ((x,y,t,env):closure2) (u:value) (v:value) =
  eval ((y,v)::(x,u)::env) t

(** Remove already evaluated values. *)
and force t =
  match t with
  | Meta (m, s) when m.value <> None -> vapp_spine (Option.get m.value) s
  | _ -> t

(** Reify a value as a term. *)
let rec readback k v =
  let var k = "x" ^ string_of_int k in
  let rec neutral k = function
    | Var i -> TVar (var i)
    | App (t, u) -> TApp (neutral k t, readback k u)
    | Postulate -> TPostulate
    | Hole pos -> THole pos
    | NPair_ind (t, u) -> TApp (readback k @@ Pair_ind t, neutral k u)
    | NTens_ind (t, u) -> TApp (readback k @@ Tens_ind t, neutral k u)
    | NIndType_ind (ind, args, t) -> TApp (readback k @@ IndType_ind (ind, args), neutral k t)
    | NFlat_ind (t, u) -> TApp (readback k @@ Flat_ind t, neutral k u)
    | NJ (r, t) -> TApp (readback k @@ J r, neutral k t)
  in
  match force v with
  | Type -> TType
  | IndType ind -> TIndType ind
  | IndType_ind (ind, args) -> TIndType_ind (ind, List.map (readback k) args)
  | IndTerm t -> TIndTerm t
  | Pi (i, c, a, b) -> TPi (i, c, var k, readback k a, readback (k+1) (capp b (vvar k)))
  | Abs (s, f) -> TAbs (Explicit, s, var k, readback (k+1) (capp f (vvar k)))
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
  | Meta (m, s) -> app_spine (TMeta (Some m.id)) (List.map (readback k) s)
  | Neu t -> neutral k t

let string_of_value k v = string_of_term @@ readback k v

let string_of_environment k env = List.map (fun (x,t) -> x ^ "=" ^ string_of_value k t) env |> String.concat ", "

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
    | Prod (l,r) -> Printf.sprintf "(%s,%s)" (to_string k l) (to_string k r)
    | Tens (l,r) -> Printf.sprintf "(%s⊗%s)" (to_string k l) (to_string k r)

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
      (* Printf.printf "split %s as %s / %s\n%!" (to_string 0 b) (FV.to_string fvl) (FV.to_string fvr); *)
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
      | Prod (b1, b2) ->
        let fv = FV.union fvl fvr in
        if FV.subset fv (dom b1) then aux fvl fvr b1
        else if FV.subset fv (dom b2) then aux fvl fvr b2
        else failwith @@ Printf.sprintf "TODO: split prod: %s as %s / %s" (to_string 0 b) (FV.to_string fvl) (FV.to_string fvr)
    in
    aux fvl fvr b
end

(** A bunched context. *)
type bunch = Bunch.t

(** Contexts. *)
module Context = struct
  type t = crisp * bunch

  let to_string ?(multiline=false) k (cenv,benv) =
    if multiline then
      let benv = Bunch.to_string k benv in
      String.concat "\n" @@ (List.rev_map (fun (x,a) -> Printf.sprintf "%s : %s" x (string_of_value k a)) cenv @ [benv])
    else
      let cenv = String.concat ", " @@ List.rev_map (fun (x,a) -> Printf.sprintf "%s:%s" x (string_of_value k a)) cenv in
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

exception Unification

module IntMap = Map.Make(Int)

(** Partial renaming of variables. *)
type partial_renaming =
  {
    dom : int; (** domain *)
    cod : int; (** codomain *)
    ren : int IntMap.t; (** renaming function *)
  }

(** Unify two values. *)
let rec unify k (t:value) (u:value) =
  (* debug "UNIFY %s VS %s\n%!" (string_of_value k t) (string_of_value k u); *)
  (* Make sure that metavariable m applied to spine s equals t. *)
  let solve k m s t =
    (* debug "SOLVE %s =? %s\n" (string_of_value k (Meta (m, s))) (string_of_value k t); *)
    (* Construct the initial renaming. Note that we number variables x0, x1, etc so that the furthest variable is x0: this is to avoid having to shift all indices when lifting. *)
    let r =
      let rec aux = function
        | t::s ->
          let cod, r = aux s in
          (
            match force t with
            | Neu (Var x) when not (IntMap.mem x r) -> cod+1, IntMap.add x cod r
            | _ -> raise Unification
          )
        | [] -> 0, IntMap.empty
      in
      let cod, ren = aux s in
      { dom = k; cod; ren }
    in
    (*
    (* Add an extra variable to a renaming. *)
    let lift r =
      { dom = r.dom+1; cod = r.cod+1; ren = IntMap.add r.dom r.cod r.ren }
    in
    *)
    (* Apply a partial renaming to a value. Along the way, we also make sure that the metavariable does not occur in the term (occurs check). *)
    let rename m r (t:value) : term =
      let var i = TVar ("x" ^ string_of_int i) in
      let rec rename r = function
        | Meta (m',s) ->
          if m'.id = m.id then (debug "OCCURS\n"; raise Unification); (* Occurs-check. *)
          app_spine (TMeta (Some m'.id)) (List.map (rename r) s)
        (* | Abs (s,t) -> *)
          (* let t = capp t (vvar r.dom) in *)
          (* TAbs (s, rename (lift r) t) *)
        | Type -> TType
        | IndType i -> TIndType i
        | Neu n -> neutral r n
        | t -> failwith @@ Printf.sprintf "TODO: rename %s" (string_of_value k t)
      and neutral r = function
        | Var x ->
          (
            match IntMap.find_opt x r.ren with
            | Some y -> var y
            | None ->
              debug "ESCAPED %s\n" (string_of_value k (Neu (Var x)));
              raise Unification
          )
        | t -> failwith @@ Printf.sprintf "TODO: rename neutral %s" (string_of_value k (Neu t))
      in
      rename r t
    in
    let t = rename m r t in
    let t =
      (* TODO: move up *)
      let rec abss l t =
        match l with
        | (s,x)::l -> TAbs (Explicit, s, x, abss l t)
        | [] -> t
      in
      (* TODO: correctly handle side... *)
      abss (List.init r.cod (fun i -> None, "x" ^ string_of_int i)) t
    in
    debug "UNIF ?%d <- %s\n%!" m.id (string_of_term t);
    let t = eval [] t in
    m.value <- Some t
  in
  let rec neutral k t u =
    match t, u with
    | Var x, Var y when x = y -> ()
    | App (t, u), App (t', u') -> neutral k t t'; unify k u u'
    | NIndType_ind (i, l, t), NIndType_ind (i', l', t') ->
      if i <> i' then raise Unification;
      if List.length l <> List.length l' then raise Unification;
      List.iter2 (unify k) l l';
      neutral k t t'
    | NPair_ind (t, u), NPair_ind (t', u')
    | NTens_ind (t, u), NTens_ind (t', u') ->
      unify (k+2) (capp2 t (vvar k) (vvar (k+1))) (capp2 t' (vvar k) (vvar (k+1)));
      neutral k u u'
    | NFlat_ind (t, u), NFlat_ind (t', u') ->
      unify (k+1) (capp t (vvar k)) (capp t' (vvar k));
      neutral k u u'
    | Postulate, Postulate -> (* TODO: number them *) ()
    | t, u ->
      debug "CLASH %s VS %s \n%!" (string_of_value k (Neu t)) (string_of_value k (Neu u));
      raise Unification
  in
  match force t, force u with
  | Type, Type -> ()
  | IndType i, IndType i' ->
    if i <> i' then raise Unification
  | IndTerm t, IndTerm t' ->
    if t <> t' then raise Unification
  | IndType_ind (i, l), IndType_ind (i', l') ->
    if i <> i' then raise Unification;
    if List.length l <> List.length l' then raise Unification;
    List.iter2 (unify k) l l'
  | Pi (i, s, a, b), Pi (i', s', a', b') ->
    if i <> i' then raise Unification;
    if s <> s' then raise Unification;
    unify k a a';
    unify (k+1) (capp b (vvar k)) (capp b' (vvar k))
  | Abs (s, t), Abs (s', t') ->
    if s <> s' then raise Unification;
    unify (k+1) (capp t (vvar k)) (capp t' (vvar k))
  | Meta (m, s), Meta (m', s') when m.id = m'.id ->
    if List.length s <> List.length s' then raise Unification;
    List.iter2 (unify k) s s'
  | Sigma (a, b), Sigma (a', b') ->
    unify k a a';
    unify (k+1) (capp b (vvar k)) (capp b' (vvar k))
  | Tens (a, b), Tens (a', b') ->
    unify k a a';
    unify k b b'
  | Pair (t, u), Pair (t', u')
  | TensPair (t, u), TensPair (t', u')
  | Eq (t, u), Eq (t', u') ->
    unify k t t';
    unify k u u'
  | Pair_ind t, Pair_ind t'
  | Tens_ind t, Tens_ind t' ->
    unify (k+2) (capp2 t (vvar k) (vvar (k+1))) (capp2 t' (vvar k) (vvar (k+1)))
  | Arr (s, a, b), Arr (s', a', b') ->
    if s <> s' then raise Unification;
    unify k a a';
    unify k b b'
  | Flat a, Flat a' -> unify k a a'
  | Flatten t, Flatten t' -> unify k t t'
  | Flat_ind t, Flat_ind t' ->
    unify (k+1) (capp t (vvar k)) (capp t' (vvar k))
  | Refl, Refl -> ()
  | Meta (m, s), t -> solve k m s t
  | t, Meta (m, s) -> solve k m s t
  | Neu t, Neu u -> neutral k t u
  | t, u ->
    debug "CLASH %s VS %s \n%!" (string_of_value k t) (string_of_value k u);
    raise Unification

(*
(** Comparison of values. *)
let is_eq k (t:value) (u:value) =
  readback k t = readback k u


let eq k t u =
  if not @@ is_eq k t u then failwith "eq"
*)

(** Check that term has given type and elaborate it. *)
let rec check k env ctx (t:term) (a:value) : term =
  debug "CHECK %s : %s\n%!" (string_of_term t) (string_of_value k a);
  (* let cenv, benv = ctx in *)
  (* Printf.printf "      %s\n%!" (Context.to_string k ctx); *)
  match t, a with
  | TAbs (i, None, x, t), Pi (i', c, a, b) ->
    assert (i = i');
    let xk = k in
    let xv = vvar xk in
    let k = k+1 in
    let env = (x,xv)::env in
    let ctx = Context.ext ~crispness:c ctx x a in
    let t = check k env ctx t (capp b xv) in
    TAbs (i, None, varn xk, t)
  | TAbs (i, Some s, x, t), Arr (s', a, b) ->
    assert (i = Explicit);
    assert (s = s');
    let xk = k in
    let xv = vvar xk in
    let k = k+1 in
    let env = (x,xv)::env in
    let ctx = Context.ext_tens ctx s x a in
    let t = check k env ctx t b in
    TAbs (i, Some s, varn xk, t)
  | TLet (c, x, a, t, u), b ->
    let a = check_type k env (Context.crisp ~crispness:c ctx) a in
    let av = eval env a in
    let t = check k env (Context.crisp ~crispness:c ctx) t av in
    let xk = k in
    let xv = vvar xk in
    let k = k+1 in
    let env = (x,xv)::env in
    let ctx = Context.ext ~crispness:c ctx x av in
    let u = check k env ctx u b in
    TLet (c, varn xk, a, t, u)
  | TPair (t, u), Sigma (a, b) ->
    let t = check k env ctx t a in
    let u =
      let t = eval env t in
      check k env ctx u (capp b t)
    in
    TPair (t, u)
  | TPair_ind (x, y, t), Pi (Explicit, c, a, b) ->
    (
      match a with
      | Sigma (a1, a2) ->
        let x1k = k in
        let x2k = k+1 in
        let k = k+2 in
        let x1 = vvar x1k in
        let x2 = vvar x2k in
        let env = (y,x2)::(x,x1)::env in
        let ctx = Context.ext ~crispness:c (Context.ext ~crispness:c ctx x a1) y (capp a2 x1) in
        let t = check k env ctx t (capp b (Pair (x1, x2))) in
        TPair_ind (varn x1k, varn x2k, t)
      | _ -> failwith "pair_ind"
    )
  | TTensPair (t, u), Tens (a, b) ->
    let ctxa, ctxb = Context.split (FV.term t) (FV.term u) ctx in
    let t = check k env ctxa t a in
    let u = check k env ctxb u b in
    TTensPair (t, u)
  | TTens_ind (x, y, t), Pi (Explicit, c, a, b) ->
    (
      match a with
      | Tens (a1, a2) ->
        let xk = k in
        let yk = k+1 in
        let k = k+2 in
        let x' = vvar xk in
        let y' = vvar yk in
        let env = (y,y')::(x,x')::env in
        let ctx =
          match c with
          | Normal ->
            let cctx, bctx = ctx in
            let bctx = Bunch.Prod (bctx, Bunch.Tens (Bunch.Decl (x, a1), Bunch.Decl (y, a2))) in
            cctx, bctx
          | Crisp ->
            Context.ext_crisp (Context.ext_crisp ctx x a1) y a2
        in
        let t = check k env ctx t (capp b (TensPair (x', y'))) in
        TTens_ind (varn xk, varn yk, t)
      | _ -> failwith "tens_ind"
    )
  | TIndType_ind (`Empty, []), Pi (Explicit, _, a, _) ->
    unify k a (IndType `Empty);
    TIndType_ind (`Empty, [])
  | TIndType_ind (`Unit, [t]), Pi (Explicit, _, a, b) ->
    unify k a (IndType `Unit);
    let t = check k env ctx t (capp b (IndTerm `Unit)) in
    TIndType_ind (`Unit, [t])
  | TIndType_ind (`Bool, [tf;tt]), Pi (Explicit, _, a, b) ->
    unify k a (IndType `Bool);
    let tf = check k env ctx tf (capp b (IndTerm (`Bool false))) in
    let tt = check k env ctx tt (capp b (IndTerm (`Bool true))) in
    TIndType_ind (`Bool, [tf;tt])
  | TFlatten t, Flat a ->
    let t = check k env (Context.crisp ctx) t a in
    TFlatten t
  | TFlat_ind (x, t), Pi (Explicit, Normal, a, b) ->
    let a =
      match a with
      | Flat a -> a
      | _ -> failwith "flat type expected"
    in
    let xk = k in
    let xv = vvar xk in
    let k = k+1 in
    let t = check k ((x,xv)::env) (Context.ext_crisp ctx x a) t (capp b (Flatten xv)) in
    TFlat_ind (varn xk, t)
  | TRefl, Eq (t, u) ->
    unify k t u;
    TRefl
  | TJ r, Pi (Explicit, Normal, _a, b) ->
    (* we should make sure that b := (y : a) (p : x ≡ y) → P[x,y,p] *)
    let unpi = function
      | Pi (Explicit, _, a, b) -> a, b
      | _ -> assert false
    in
    let y, k = vvar k, k+1 in
    let b', _ = unpi (capp b y) in
    let x =
      match b' with
      | Eq (x, y') when y' = y -> x
      | _ -> assert false
    in
    let c = capp (snd @@ unpi @@ capp b x) Refl in
    let r = check k env ctx r c in
    TJ r
  | TPi _, Type
  | TSigma _, Type
  | TArr _, Type
  | TTens _, Type -> check_type k env ctx t
  | TPostulate, a ->
    important "POSTULATE %s\n%!" (string_of_value k a);
    TPostulate
  | THole pos, a ->
    important "HOLE %s : %s IN\n%s\n%!" (Pos.to_string pos) (string_of_value k a) (Context.to_string ~multiline:true k ctx);
    THole pos
  | t, a ->
    let t, a' = infer k env ctx t in
    (
      try unify k a' a; t
      with Unification -> failwith @@ Printf.sprintf "%s has type %s but %s expected" (string_of_term t) (string_of_value k a') (string_of_value k a)
    )

(** Check that a term is a type. *)
and check_type k env ctx a =
  debug "CHECK TYPE %s\n%!" (string_of_term a);
  (* let cenv, benv = ctx in *)
  (* Printf.printf ". ctx: %s\n%!" (Context.to_string k ctx); *)
  match a with
  | TType -> TType
  | TPi (i, Crisp, x, a, b) ->
    let a = check_type k env (Context.crisp ctx) a in
    let xk = k in
    let xv = vvar xk in
    let k = k+1 in
    let ctx =
      let a = eval env a in
      Context.ext_crisp ctx x a
    in
    let env = (x,xv)::env in
    let b = check_type k env ctx b in
    TPi (i, Crisp, varn xk, a, b)
  | TPi (i, Normal, x, a, b) ->
    let a = check_type k env ctx a in
    let xk = k in
    let xv = vvar xk in
    let k = k+1 in
    let ctx =
      Printf.printf "eval a = %s in %s\n%!" (string_of_term a) (string_of_environment k env);
      let a = eval env a in
      Context.ext ctx x a
    in
    let env = (x,xv)::env in
    Printf.printf "check b\n%!";
    let b = check_type k env ctx b in
    TPi (i, Normal, varn xk, a, b)
  | TSigma (x, a, b) ->
    let a = check_type k env ctx a in
    let xk = k in
    let xv = vvar xk in
    let k = k+1 in
    let ctx =
      let a = eval env a in
      Context.ext ctx x a
    in
    let env = (x,xv)::env in
    let b = check_type k env ctx b in
    TSigma (varn xk, a, b)
  | TTens (a, b) ->
    let a = check_type k env (Context.crisp ctx) a in
    let b = check_type k env (Context.crisp ctx) b in
    TTens (a, b)
  | TArr (s, a, b) ->
    let a = check_type k env (Context.crisp ctx) a in
    let b = check_type k env (Context.crisp ctx) b in
    TArr (s, a, b)
  | TFlat a ->
    let a = check_type k env (Context.crisp ctx) a in
    TFlat a
  | TEq (t, u) ->
    let t, a = infer k env ctx t in
    let u = check k env ctx u a in
    TEq (t, u)
  | a ->
    check k env ctx a Type

(** Infer the type of a term. *)
and infer k env ctx (t:term) : term * value =
  debug "INFER %s\n%!" (string_of_term t);
  (* let cenv, benv = ctx in *)
  match t with
  | TIndType ind -> TIndType ind, Type
  | TIndTerm `Unit -> TIndTerm `Unit, IndType `Unit
  | TIndTerm (`Bool b) -> TIndTerm (`Bool b), IndType `Bool
  | TApp (t, u) ->
    (
      match infer k env ctx t with
      | t, Pi (Explicit, c, a, b) ->
        let u = check k env (Context.crisp ~crispness:c ctx) u a in
        TApp (t, u), capp b (eval env u)
      | t, Arr (_s, a, b) ->
        let u = check k env ctx u a in
        TApp (t, u), b
      | _ -> failwith "infer app"
    )
  | TEq (t, u) ->
    let t, a = infer k env ctx t in
    let u = check k env ctx u a in
    TEq (t, u), Type
  | TVar x ->
    let rec aux = function
      | (y, _)::l when x = y -> List.length l
      | _::l -> aux l
      | [] -> failwith @@ Printf.sprintf "infer: undefined variable %s" x
    in
    let k = aux env in
    let a = Option.get @@ Context.assoc_opt x ctx in
    TVar (varn k), a
  | TMeta None ->
    let a = fresh_meta env in
    TMeta None, a
  | _ -> failwith "infer"

let check_decl k env ctx (x, c, a, t) =
  Printf.printf "\nDECL  %s = %s %s %s\n%!" x (string_of_term t) (match c with Normal -> ":" | Crisp -> "::") (string_of_term a);
  let a = check_type k env ctx a in
  let a = eval env a in
  let t = check k env (Context.crisp ~crispness:c ctx) t a in
  let t = eval env t in
  let env = (x,t)::env in
  let ctx = Context.ext ~crispness:c ctx x a in
  env, ctx

let check_decls k env ctx (decls:decls) =
  List.fold_left (fun (env,ctx) decl -> check_decl k env ctx decl) (env,ctx) decls

let check_decls_toplevel decls = ignore @@ check_decls 0 [] Context.empty decls
