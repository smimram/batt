open Common

module T = Term
module V = Value

type term = T.t
type value = V.t

module FV = Term.FV

let string_of_environment k env = List.map (fun (x,t) -> x ^ "=" ^ V.to_string k t) env |> String.concat ", "

type var = string

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
    | Decl (x, a) -> Printf.sprintf "%s:%s" x (V.to_string k a)
    | Prod (l,r) -> Printf.sprintf "(%s,%s)" (to_string k l) (to_string k r)
    | Tens (l,r) -> Printf.sprintf "(%s⊗%s)" (to_string k l) (to_string k r)

  let ext ctx x a = Prod (ctx,Decl(x,a))
  
  let ext_tens ctx (s:V.side) x (a:value) =
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
  let split fvl fvr crisp b =
    debug "SPLIT %s as %s / %s\n" (to_string 0 b) (FV.to_string fvl) (FV.to_string fvr);
    assert (FV.is_empty @@ FV.inter fvl fvr);
    let fvc = FV.of_list @@ List.map fst crisp in
    let is_crisp fv = FV.subset fv fvc in
    (* Printf.printf "crisp: %s\n%!" @@ FV.to_string fvc; *)
    let rec aux fvl fvr b =
      (* Printf.printf "split %s as %s / %s\n%!" (to_string 0 b) (FV.to_string fvl) (FV.to_string fvr); *)
      match b with
      | b when is_crisp fvl -> Empty, b
      | b when is_crisp fvr -> b, Empty
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
      String.concat "\n" @@ (List.rev_map (fun (x,a) -> Printf.sprintf "%s : %s" x (V.to_string k a)) cenv @ [benv])
    else
      let cenv = String.concat ", " @@ List.rev_map (fun (x,a) -> Printf.sprintf "%s:%s" x (V.to_string k a)) cenv in
      let benv = Bunch.to_string k benv in
      Printf.sprintf "%s / %s" cenv benv

  let empty : t = [],Bunch.Empty

  let ext ((cenv,benv):t) x a : t = cenv, Bunch.ext benv x a

  let ext_tens ((cenv,benv):t) s x a = cenv, Bunch.ext_tens benv s x a

  let ext_crisp ((cenv,benv):t) x a : t = ((x,a)::cenv), benv

  let ext ctx ?(crispness=(Normal:V.crispness)) x a =
    match crispness with
    | Normal -> ext ctx x a
    | Crisp -> ext_crisp ctx x a

  let crisp ((cenv,_):t) : t = cenv,Bunch.Empty

  let crisp ?(crispness=(Crisp:V.crispness)) ctx =
    match crispness with
    | Crisp -> crisp ctx
    | Normal -> ctx

  let assoc_opt x ((cenv,benv):t) =
    match Bunch.assoc_opt x benv with
    | Some a -> Some a
    | None -> List.assoc_opt x cenv

  let split fvl fvr ((cenv,benv):t) =
    let l, r = Bunch.split fvl fvr cenv benv in
    (cenv,l),(cenv,r)
end

(** A context. *)
type context = Context.t

(** Unification problems. *)
module Unification = struct
  let set m t =
    debug "UNIF %s <- %s\n%!" (V.Meta.to_string m) (T.to_string t);
    assert (m.value = None);
    let t = V.eval [] t in
    m.value <- Some t

  (** A unification problem. *)
  type t = Pos.t option * int * value * value

  let deferred = ref ([] : t list)

  let is_empty () = !deferred = []

  (** Defer a unification problem. *)
  let defer pos k t u =
    (* TODO: better data structure *)
    deferred := !deferred @ [pos,k,t,u]

  let solvable ((_,_,t,u) : t) =
    match V.force t, V.force u with
    | Meta (m, _), Meta (m', _) -> m.id = m'.id
    | _ -> true

  let has_solvable () =
    List.exists solvable !deferred

  (** Find a unification problem to solve. *)
  let pop_opt () =
    let rec find_and_remove_opt f = function
      | x::l when f x -> Some x, l
      | x::l ->
        let y, l = find_and_remove_opt f l in
        y, x::l
      | [] -> None, []
    in
    let pb, rem = find_and_remove_opt solvable !deferred in
    deferred := rem;
    pb

  let pop () =
    Option.get @@ pop_opt ()
end

exception Unification

module IntMap = Map.Make(Int)

(** Partial renaming of variables. *)
type partial_renaming =
  {
    dom : int; (** domain *)
    cod : int; (** codomain *)
    ren : int option IntMap.t; (** renaming function *)
  }

let error ?t fmt =
  let pos =
    match t with
    | Some t -> T.Position.to_string_comma t
    | None -> ""
  in
  Printf.ksprintf (fun s -> failwith (pos ^ s)) fmt

(** Unify two values. *)
let unify ~pos k (t:value) (u:value) =
  (* debug "UNIFY %s WITH %s\n%!" (V.to_string k t) (V.to_string k u); *)
  (* Make sure that metavariable m applied to spine s equals t. *)
  let solve k m s t =
    (* debug "SOLVE %s =? %s\n" (V.to_string k (Meta (m, s))) (V.to_string k t); *)
    (* Construct the initial renaming. Note that we number variables x0, x1, etc so that the furthest variable is x0: this is to avoid having to shift all indices when lifting. *)
    let r =
      let rec aux = function
        | t::s ->
          let cod, r = aux s in
          (
            match V.force t with
            | Var (x, []) ->
              if IntMap.mem x r then
                (* NOTE: in case we have mutiple times the same variable, we simply associate None so that we refuse to disambiguate *)
                cod+1, IntMap.add x None r
              else
                cod+1, IntMap.add x (Some cod) r
            | _ -> raise Unification
          )
        | [] -> 0, IntMap.empty
      in
      let cod, ren = aux s in
      { dom = k; cod; ren }
    in
    (* Add an extra variable to a renaming. *)
    let lift r = { dom = r.dom+1; cod = r.cod+1; ren = IntMap.add r.dom (Some r.cod) r.ren } in
    (* Fresh variable name. *)
    let var_name i = "x!" ^ string_of_int i in
    (* Apply a partial renaming to a value. Along the way, we also make sure that the metavariable does not occur in the term (occurs check). *)
    let rename (m:V.meta) (r:partial_renaming) (t:value) : term =
      let var i = T.Var (var_name i) in
      let rec rename r t =
        let t = V.force t in
        let spine l (t:term) = T.app_spine t (List.map (rename r) l) in
        match t with
        | Meta (m',l) ->
          if m'.id = m.id then (debug "OCCURS\n"; raise Unification); (* Occurs-check. *)
          spine l @@ Meta (`Generated m'.id)
        | Pi (i, c, a, b) ->
          let a = rename r a in
          let x = var_name r.cod in
          let b = rename (lift r) @@ V.capp b (V.var r.dom) in
          Pi (i, c, x, a, b)
        | Arr (s, a, b) ->
          let a = rename r a in
          let b = rename r b in
          Arr (s, a, b)
        | Abs (s, t) ->
          let x = var_name r.cod in
          let t = V.capp t (V.var r.dom) in
          Abs (Explicit, s, x, rename (lift r) t)
        | Sigma (a, b) ->
          let x = var_name r.cod in
          let a = rename r a in
          let b = rename (lift r) @@ V.capp b (V.var r.dom) in
          Sigma (x, a, b)
        | Type n -> Type n
        | IndType i -> IndType i
        | IndTerm t -> IndTerm t
        | IndType_ind (i, t, l) -> spine l @@ IndType_ind (i, List.map (rename r) t)
        | Pair_ind (t, l) ->
          let k = r.dom in
          let x = var_name r.cod in
          let y = var_name (r.cod+1) in
          let t = V.capp2 t (V.var k) (V.var (k+1)) in
          let t = rename (lift (lift r)) t in
          spine l @@ Pair_ind (x, y, t)
        | Tens (a,b) -> Tens (rename r a, rename r b)
        | TensPair (t, u) -> TensPair (rename r t, rename r u)
        | Tens_ind (t, l) ->
          let k = r.dom in
          let x = var_name r.cod in
          let y = var_name (r.cod+1) in
          let t = V.capp2 t (V.var k) (V.var (k+1)) in
          let t = rename (lift (lift r)) t in
          spine l @@ Tens_ind (x, y, t)
        | Eq(t,u) -> Eq (rename r t, rename r u)
        | J (t, l) -> spine l @@ J (rename r t)
        | Flat a -> Flat (rename r a)
        | Flatten t -> Flatten (rename r t)
        | Flat_ind (t, l) ->
          let x = var_name r.cod in
          let t = V.capp t (V.var k) in
          let t = rename (lift r) t in
          spine l @@ Flat_ind (x, t)
        | Hole (pos, l) -> spine l @@ Hole pos
        | Var (x, l) ->
          spine l @@
          (
            match IntMap.find_opt x r.ren with
            | Some (Some y) -> var y
            | Some None ->
              debug "DUPLICATE %s\n" (V.to_string k (V.var x));
              raise Unification
            | None ->
              debug "ESCAPED %s\n" (V.to_string k (V.var x));
              raise Unification
          )
        | Postulate (n, l) ->
          spine l @@ Postulate (Some n)
        | t -> failwith @@ Printf.sprintf "TODO: rename %s" (V.to_string k t)
      in
      rename r t
    in
    let t = rename m r t in
    let t =
      (* TODO: correctly handle side... *)
      T.abss (List.init r.cod (fun i -> None, var_name i)) t
    in
    Unification.set m t
  in
  let rec unify k t u =
    let spine k l l' =
      if List.length l <> List.length l' then raise Unification;
      List.iter2 (unify k) l l'
    in
    match V.force t, V.force u with
    | Type l, Type l' ->
      if l <> l' then raise Unification
    | IndType i, IndType i' ->
      if i <> i' then raise Unification
    | IndTerm t, IndTerm t' ->
      if t <> t' then raise Unification
    | IndType_ind (i, t, l), IndType_ind (i', t', l') ->
      if i <> i' then raise Unification;
      spine k t t'; (* NOTE: this is not a spine but ok *)
      spine k l l'
    | Pi (i, s, a, b), Pi (i', s', a', b') ->
      if i <> i' then raise Unification;
      if s <> s' then raise Unification;
      unify k a a';
      unify (k+1) (V.capp b (V.var k)) (V.capp b' (V.var k))
    | Abs (s, t), Abs (s', t') ->
      if s <> s' then raise Unification;
      unify (k+1) (V.capp t (V.var k)) (V.capp t' (V.var k))
    | Meta (m, s), Meta (m', s') when m.id = m'.id ->
      if List.length s <> List.length s' then raise Unification;
      List.iter2 (unify k) s s'
    | Sigma (a, b), Sigma (a', b') ->
      unify k a a';
      unify (k+1) (V.capp b (V.var k)) (V.capp b' (V.var k))
    | Tens (a, b), Tens (a', b') ->
      unify k a a';
      unify k b b'
    | Pair (t, u), Pair (t', u')
    | TensPair (t, u), TensPair (t', u')
    | Eq (t, u), Eq (t', u') ->
      unify k t t';
      unify k u u'
    | Pair_ind (t, l), Pair_ind (t', l')
    | Tens_ind (t, l), Tens_ind (t', l') ->
      unify (k+2) (V.capp2 t (V.var k) (V.var (k+1))) (V.capp2 t' (V.var k) (V.var (k+1)));
      spine k l l'
    | Arr (s, a, b), Arr (s', a', b') ->
      if s <> s' then raise Unification;
      unify k a a';
      unify k b b'
    | Flat a, Flat a' -> unify k a a'
    | Flatten t, Flatten t' -> unify k t t'
    | Flat_ind (t, l), Flat_ind (t', l') ->
      unify (k+1) (V.capp t (V.var k)) (V.capp t' (V.var k));
      spine k l l'
    | Refl, Refl -> ()
    | Postulate (_n, l), Postulate (_n', l') ->
      (* NOTE: disabling for now because we regenerate numbers when we include multiple times *)
      (* if n <> n' then raise Unification; *)
      spine k l l'
    | Var (x, l), Var (x', l') ->
      if x <> x' then raise Unification;
      spine k l l'
    | Hole (pos, l), Hole (pos', l') ->
      if pos <> pos' then raise Unification;
      spine k l l'
    | Meta _, Meta _ -> Unification.defer pos k t u
    | Meta (m, l), t -> solve k m l t
    | t, Meta (m, l) -> solve k m l t
    | t, u ->
      debug "CLASH %s VS %s \n%!" (V.to_string k t) (V.to_string k u);
      raise Unification
  in
  Unification.defer pos k t u;
  while Unification.has_solvable () do
    let _pos, k, t, u = Unification.pop () in
    unify k t u
  done

(** Make sure that there are no unification problems left. *)
let finalize_unify () =
  let solve () =
    (* Solve what can be. *)
    while Unification.has_solvable () do
      let pos, k, t, u = Unification.pop () in
      unify ~pos k t u
    done;
  in
  (* TODO: we should remove pruning! *)
  let prune t u =
    match V.force t, V.force u with
    | Meta (m, l), Meta (m', l') ->
      (* TODO: we should be able to spare a few List.rev *)
      (* Remove duplicated variables and non-variables from the spine. *)
      let sanitize l =
        let rec aux = function
          | (V.Var (_, []) as x)::l ->
            if List.mem x l then aux (List.filter (fun y -> x <> y) l)
            else x::(aux l)
          | _::l -> aux l
          | [] -> []
        in
        List.rev @@ aux l
      in
      (* replace (m1,l1) with (m2,l2) *)
      let replace m1 l1 (m2:V.meta) l2 =
        let t =
          let var i = "x~" ^ string_of_int (i+1) in
          let xx = List.init (List.length l1) (fun i -> None, var i) in
          let args = List.mapi (fun i x -> if List.mem x l2 then Some (T.Var (var i)) else None) (List.rev l1) |> List.filter_map Fun.id in
          let m2 = T.Meta (`Generated m2.id) in
          let t = T.apps m2 args in
          T.abss xx t
        in
        Unification.set m1 t
      in
      let l2 = sanitize l in
      let l2' = sanitize l' in
      let l2 = List.filter (fun x -> List.mem x l2') l2 in
      let m2 = V.Meta.fresh () in
      replace m l m2 l2;
      replace m' l' m2 l2
    | _ -> assert false
  in
  solve ();
  if false then
    while !Unification.deferred <> [] do
      (* Flex-flex: prune to common non-duplicated variables. *)
      let _,_,t,u = List.hd !Unification.deferred in
      Unification.deferred := List.tl !Unification.deferred;
      prune t u;
      solve ()
    done;
  if not @@ Unification.is_empty () then
    let pb =
      List.rev !Unification.deferred
      |> List.map (fun (pos,k,t,u) -> Printf.sprintf "- %s: %s vs %s" (Pos.opt_to_string pos) (V.to_string k t) (V.to_string k u))
      |> String.concat "\n"
    in
    warning "\n%d unsovled unification problems:\n%s\n" (List.length !Unification.deferred) pb

let unify k t a b =
  try unify k a b
  with Unification -> error ~t "term has type %s but %s expected" (V.to_string k a) (V.to_string k b)

(*
(** Comparison of values. *)
let is_eq k (t:value) (u:value) =
  readback k t = readback k u

let eq k t u =
  if not @@ is_eq k t u then failwith "eq"
*)

(** Check that term has given type and elaborate it. *)
let rec check k env ctx (t:term) (a:value) : term =
  debug "CHECK %s : %s\n%!" (T.to_string t) (V.to_string k a);
  (* let cenv, benv = ctx in *)
  (* Printf.printf "      %s\n%!" (Context.to_string k ctx); *)
  let t0 = t in
  let pos = T.Position.find_opt t in
  match t, V.force a with
  | Abs (i, None, x, t), Pi (i', c, a, b) when i = i' ->
    let xv = V.var k in
    let k = k+1 in
    let env = (x,xv)::env in
    let ctx = Context.ext ~crispness:c ctx x a in
    let t = check k env ctx t (V.capp b xv) in
    Abs (i, None, x, t)
  | Abs (i, Some s, x, t), Arr (s', a, b) ->
    assert (i = Explicit);
    assert (s = s');
    let xv = V.var k in
    let k = k+1 in
    let env = (x,xv)::env in
    let ctx = Context.ext_tens ctx s x a in
    let t = check k env ctx t b in
    Abs (i, Some s, x, t)
  | Let (c, x, a, t, u), b ->
    let a, _level = check_type k env (Context.crisp ~crispness:c ctx) a in
    let av = V.eval env a in
    let t = check k env (Context.crisp ~crispness:c ctx) t av in
    let env = (x, V.eval env t)::env in
    let ctx = Context.ext ~crispness:c ctx x av in
    let u = check k env ctx u b in
    Let (c, x, a, t, u)
  | Pair (t, u), Sigma (a, b) ->
    let t = check k env ctx t a in
    let u =
      let t = V.eval env t in
      check k env ctx u (V.capp b t)
    in
    Pair (t, u)
  | Pair_ind (x, y, t), Pi (Explicit, c, a, b) ->
    (
      match a with
      | Sigma (a1, a2) ->
        let x1 = V.var k in
        let x2 = V.var (k+1) in
        let k = k+2 in
        let env = (y,x2)::(x,x1)::env in
        let ctx = Context.ext ~crispness:c (Context.ext ~crispness:c ctx x a1) y (V.capp a2 x1) in
        let t = check k env ctx t (V.capp b (Pair (x1, x2))) in
        Pair_ind (x, y, t)
      | _ -> failwith "pair_ind"
    )
  | TensPair (t, u), Tens (a, b) ->
    let ctxa, ctxb = Context.split (FV.term t) (FV.term u) ctx in
    let t = check k env ctxa t a in
    let u = check k env ctxb u b in
    TensPair (t, u)
  | Tens_ind (x, y, t), Pi (Explicit, c, a, b) ->
    (
      match a with
      | Tens (a1, a2) ->
        let x' = V.var k in
        let y' = V.var (k+1) in
        let k = k+2 in
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
        let t = check k env ctx t (V.capp b (TensPair (x', y'))) in
        Tens_ind (x, y, t)
      | _ -> failwith "tens_ind"
    )
  | IndType_ind (`Empty, []), Pi (Explicit, _, a, _) ->
    unify ~pos k t a (IndType `Empty);
    IndType_ind (`Empty, [])
  | IndType_ind (`Unit, [t]), Pi (Explicit, _, a, b) ->
    unify ~pos k t a (IndType `Unit);
    let t = check k env ctx t (V.capp b (IndTerm `Unit)) in
    IndType_ind (`Unit, [t])
  | IndType_ind (`Bool, [tf;tt]), Pi (Explicit, _, a, b) ->
    unify ~pos k t a (IndType `Bool);
    let tf = check k env ctx tf (V.capp b (IndTerm (`Bool false))) in
    let tt = check k env ctx tt (V.capp b (IndTerm (`Bool true))) in
    IndType_ind (`Bool, [tf;tt])
  | Flatten t, Flat a ->
    let t = check k env (Context.crisp ctx) t a in
    Flatten t
  | Flat_ind (x, t), Pi (Explicit, _, a, b) ->
    let a =
      match V.force a with
      | Flat a -> a
      | _ -> error ~t "flat type expected"
    in
    let xv = V.var k in
    let k = k+1 in
    let t = check k ((x,xv)::env) (Context.ext_crisp ctx x a) t (V.capp b (Flatten xv)) in
    Flat_ind (x, t)
  | Refl, Eq (t, u) ->
    unify ~pos k Refl t u; (* TODO: better error *)
    Refl
  | J r, Pi (_, Normal, _a, b) ->
    (* we should make sure that b := {y : a} (p : x ≡ y) → P[x,y,p] *)
    let unpi ?icit a =
      let a0 = a in
      match V.force a with
      | Pi (icit', _, a, b) when icit = None || Some icit' = icit -> a, b
      | _ -> error ~t "got %s but function type expected" (V.to_string k a0)
    in
    let y, k = V.var k, k+1 in
    let b', _ = unpi (V.capp b y) in
    let x =
      match b' with
      | Eq (x, y') when y' = y -> x
      | _ -> error ~t "identity type expected"
    in
    let c = V.capp (snd @@ unpi ~icit:Explicit @@ V.capp b x) Refl in
    let r = check k env ctx r c in
    J r
  | _, Pi (Implicit, _, _, _) ->
    (* Insert implicit abstraction. *)
    check k env ctx (Abs (Implicit, None, "_", t)) a
  | Pi _, Type m
  | Sigma _, Type m
  | Arr _, Type m
  | Tens _, Type m
  | Flat _, Type m ->
    let t, level = check_type k env ctx t in
    if level > m then error ~t:t0 "universe level %d but at most %d expected" level m;
    t
  | Postulate n, a ->
    let n = match n with Some n -> n | None -> incr V.postulate; !V.postulate in
    important "POSTULATE %d %s\n%!" n (V.to_string k a);
    Postulate (Some n)
  | Hole pos, a ->
    important "HOLE %s : %s IN\n%s\n%!" (Pos.to_string pos) (V.to_string k a) (Context.to_string ~multiline:true k ctx);
    Hole pos
  | t, a ->
    let t0 = t in
    let t, a' = infer k env ctx t in
    (
      match V.force a', V.force a with
      | Type n, Type m when n <= m -> t  (* cumulativity *)
      | Pi (Implicit, _, _, _), Pi (Explicit, _, _, _) ->
        let pos = T.Position.find_opt t in
        check k env ctx (T.mk ?pos (T.app ~icit:Implicit t0 (Meta (`Fresh None)))) a
      | _ ->
        try unify ~pos k t0 a' a; t
        with Unification -> error ~t:t0 "%s has type %s but %s expected" (T.to_string t) (V.to_string k a') (V.to_string k a)
    )

(** Check that a term is a type; returns the elaborated term and its universe level. *)
and check_type k env ctx a : term * int =
  debug "CHECK TYPE %s\n%!" (T.to_string a);
  match a with
  | Hole pos -> Hole pos, 0
  | _ ->
    match infer k env ctx a with
    | a, Type l -> a, l
    | _, b -> error ~t:a "%s has type %s by type expected" (T.to_string a) (V.to_string k b)

(** Infer the type of a term. *)
and infer k env ctx (t:term) : term * value =
  debug "INFER %s\n%!" (T.to_string t);
  let t0 = t in
  (* let cenv, benv = ctx in *)
  match t with
  | Type n -> Type n, V.Type (n + 1)
  | IndType ind -> IndType ind, V.Type 0
  | IndTerm `Unit -> IndTerm `Unit, IndType `Unit
  | IndTerm (`Bool b) -> IndTerm (`Bool b), IndType `Bool
  | Pi (i, Crisp, x, a, b) ->
    let a, la = check_type k env (Context.crisp ctx) a in
    let xv = V.var k in
    let k = k+1 in
    let ctx =
      let a = V.eval env a in
      Context.ext_crisp ctx x a
    in
    let env = (x,xv)::env in
    let b, lb = check_type k env ctx b in
    Pi (i, Crisp, x, a, b), Type (max la lb)
  | Pi (i, Normal, x, a, b) ->
    let a, la = check_type k env ctx a in
    let xv = V.var k in
    let k = k+1 in
    let ctx =
      let a = V.eval env a in
      Context.ext ctx x a
    in
    let env = (x,xv)::env in
    let b, lb = check_type k env ctx b in
    Pi (i, Normal, x, a, b), Type (max la lb)
  | Sigma (x, a, b) ->
    let a, la = check_type k env ctx a in
    let xv = V.var k in
    let k = k+1 in
    let ctx =
      let a = V.eval env a in
      Context.ext ctx x a
    in
    let env = (x,xv)::env in
    let b, lb = check_type k env ctx b in
    Sigma (x, a, b), Type (max la lb)
  | Tens (a, b) ->
    let a, la = check_type k env (Context.crisp ctx) a in
    let b, lb = check_type k env (Context.crisp ctx) b in
    Tens (a, b), Type (max la lb)
  | Arr (s, a, b) ->
    let a, la = check_type k env (Context.crisp ctx) a in
    let b, lb = check_type k env (Context.crisp ctx) b in
    Arr (s, a, b), Type (max la lb)
  | Flat a ->
    let a, la = check_type k env (Context.crisp ctx) a in
    Flat a, Type la
  | Flatten t ->
    let t, a = infer k env (Context.crisp ctx) t in
    Flatten t, Flat a
  | Eq (t, u) ->
    let t, a = infer k env ctx t in
    let u = check k env ctx u a in
    Eq (t, u), Type 0
  | App (t, icit, u) ->
    (
      let pos = T.Position.find_opt t in
      let rec insert_implicits t a =
        match V.force a with
        | Pi (Implicit, c, a, b) ->
          let m = check k env (Context.crisp ~crispness:c ctx) (T.mk ?pos (Meta (`Fresh None))) a in
          let mv = V.eval env m in
          insert_implicits (T.App (t, Implicit, m)) (V.capp b mv)
        | _ -> t, a
      in
      let t1 = t in
      let t, a = infer k env ctx t in
      let t, a = if icit = Explicit then insert_implicits t a else t, a in
      (
        match V.force a with
        | Pi (icit', c, a, b) ->
          if icit <> icit' then error ~t:t0 "got an implicit argument where an explicit one was expected";
          let u = check k env (Context.crisp ~crispness:c ctx) u a in
          App (t, icit, u), V.capp b (V.eval env u)
        | Arr (s, a, b) ->
          let ctxt, ctxu =
            match s with
            | Left -> Context.split (FV.term u) (FV.term t1) ctx
            | Right -> Context.split (FV.term t1) (FV.term u) ctx
          in
          let t = check k env ctxt t1 (Arr (s, a, b)) in
          let u = check k env ctxu u a in
          App (t, Explicit, u), b
        | _ -> error ~t:t0 "cannot infer the type of the application"
      )
    )
  | Var x ->
    let rec aux n = function
      | (y, _)::_ when x = y -> n
      | _::l -> aux (n+1) l
      | [] -> error ~t "undefined variable %s" x
    in
    let k = aux 0 env in
    let a = match Context.assoc_opt x ctx with Some a -> a | None -> error ~t "variable %s is in the context but not in the typing environment (crispness issue?)" x in
    Var' k, a
  | Meta (`Fresh pos) ->
    let a = V.fresh_meta env in
    Meta (`Fresh pos), a
  | _ -> error ~t "cannot infer type"

let rec check_decl k env ctx = function
  | Term.Def (x, c, a, t) ->
    Printf.printf "\nDECL  %s = %s %s %s\n%!" x (T.to_string t) (match c with Normal -> ":" | Crisp -> "::") (T.to_string a);
    let a, _level = check_type k env ctx a in
    let a = V.eval env a in
    let t = check k env (Context.crisp ~crispness:c ctx) t a in
    let t = V.eval env t in
    let env = (x,t)::env in
    let ctx = Context.ext ~crispness:c ctx x a in
    env, ctx
  | Include name ->
    let dirs = Common.include_directories () in
    let fname = name ^ ".batt" in
    let fname =
      match List.find_map (fun dir ->
          let f = Filename.concat dir fname in
          if Sys.file_exists f then Some f else None) dirs
      with
      | Some f -> f
      | None ->
        failwith @@ Printf.sprintf "Could not find library file %s (in %s)" fname (String.concat ", " dirs)
    in
    Printf.printf "Include %s...\n%!" fname;
    let decls = Module.parse fname in
    check_decls k env ctx decls

and check_decls k env ctx (decls:T.decls) =
  List.fold_left (fun (env,ctx) decl -> check_decl k env ctx decl) (env,ctx) decls

let check_decls_toplevel decls = ignore @@ check_decls 0 [] Context.empty decls

let check_meta () =
  let m =
    V.Meta.variables
    |> V.Meta.Dynarray.to_list
    |> List.filter (fun (m:V.meta) -> m.value = None && m.pos <> None)
    |> List.map (fun m -> "- " ^ V.Meta.to_string m ^ " at " ^ Pos.to_string (Option.get m.pos))
    |> String.concat "\n"
  in
  if m <> "" then important "\nUNSOLVED META\n%s\n%!" m
