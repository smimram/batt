open Common

module T = Term
module V = Value

type term = T.t
type value = V.t

module FV = Term.FV

(** Names of the variables at levels [k-1], ..., [0] in an environment, made distinct by adding primes. The environment also contains definitions, which do not have a level, so that we look for the entries whose value is a variable. *)
let names k env =
  let a = Array.init k (fun i -> "x" ^ string_of_int i) in
  (* Go from the most recent entry to the oldest one, so that the binder of a variable wins over later definitions such as let y = x. *)
  List.iter (fun (x,v) -> match V.force v with V.Var (i, []) when 0 <= i && i < k -> a.(i) <- x | _ -> ()) env;
  T.fresh_names @@ List.rev @@ Array.to_list a

(** String representation of a value at level [k] in environment [env]. *)
let string_of_value k env v = V.to_string ~vars:(names k env) k v

(** String representation of an elaborated term in environment [env]: its variables are de Bruijn indices in [env]. *)
let string_of_term env t = T.to_string ~vars:(T.fresh_names @@ List.map fst env) t

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

  let rec to_string ?vars k = function
    | Empty -> "()"
    | Decl (x, a) -> Printf.sprintf "%s:%s" x (V.to_string ?vars k a)
    | Prod (l,r) -> Printf.sprintf "(%s,%s)" (to_string ?vars k l) (to_string ?vars k r)
    | Tens (l,r) -> Printf.sprintf "(%s⊗%s)" (to_string ?vars k l) (to_string ?vars k r)

  let ext ctx x a = Prod (ctx,Decl(x,a))

  let tens ?(side=(Right:V.side)) b1 b2 =
    match side with
    | Left -> Tens (b2, b1)
    | Right -> Tens (b1, b2)
  
  let ext_tens ctx (s:V.side) x (a:value) =
    let ext = Decl (x, a) in
    tens ~side:s ctx ext

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
  let split ?t ?vars k fvl fvr crisp b =
    let failwith s =
      let pos = match t with Some t -> T.Position.to_string_comma t | None -> "" in
      failwith (pos ^ s)
    in
    let to_string = to_string ?vars k in
    if !Common.show_debug then debug "SPLIT %s as %s / %s\n" (to_string b) (FV.to_string fvl) (FV.to_string fvr);
    let fvc = FV.of_list @@ List.map fst crisp in
    let shared = FV.diff (FV.inter fvl fvr) fvc in
    if not (FV.is_empty shared) then failwith @@ Printf.sprintf "non-crisp variables used on both sides of a tensor: %s" (FV.to_string shared);
    let is_crisp fv = FV.subset fv fvc in
    (* Printf.printf "crisp: %s\n%!" @@ FV.to_string fvc; *)
    let rec aux fvl fvr b =
      (* Printf.printf "split %s as %s / %s\n%!" (to_string b) (FV.to_string fvl) (FV.to_string fvr); *)
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
        else failwith @@ Printf.sprintf "cannot split %s as %s / %s" (to_string b) (FV.to_string fvl) (FV.to_string fvr)
      | Prod (Empty, b)
      | Prod (b, Empty) -> aux fvl fvr b
      | Decl _ -> failwith @@ Printf.sprintf "trying to split %s as %s / %s" (to_string b) (FV.to_string fvl) (FV.to_string fvr)
      | Prod (b1, b2) ->
        let fv = FV.union fvl fvr in
        if FV.subset fv (dom b1) then aux fvl fvr b1
        else if FV.subset fv (dom b2) then aux fvl fvr b2
        else failwith @@ Printf.sprintf "cannot split %s as %s / %s" (to_string b) (FV.to_string fvl) (FV.to_string fvr)
    in
    aux fvl fvr b

  (*
  let split fvl fvr crisp b =
    let l, r = split fvl fvr crisp b in
    debug "SPLITED AS %s / %s\n" (to_string 0 l) (to_string 0 r);
    l, r
  *)
end

(** A bunched context. *)
type bunch = Bunch.t

(** Contexts. *)
module Context = struct
  type t = crisp * bunch

  let to_string ?(multiline=false) ?(crisp=true) ?vars k (cenv,benv) =
    let cenv = if crisp then cenv else [] in
    if multiline then
      let benv = Bunch.to_string ?vars k benv in
      String.concat "\n" @@ (List.rev_map (fun (x,a) -> Printf.sprintf "%s ∷ %s" x (V.to_string ?vars k a)) cenv @ [benv])
    else
      let cenv = String.concat ", " @@ List.rev_map (fun (x,a) -> Printf.sprintf "%s∷%s" x (V.to_string ?vars k a)) cenv in
      let benv = Bunch.to_string ?vars k benv in
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

  let split ?t ?vars k fvl fvr ((cenv,benv):t) =
    let l, r = Bunch.split ?t ?vars k fvl fvr cenv benv in
    (cenv,l),(cenv,r)
end

(** A context. *)
type context = Context.t

(** Unification problems. *)
module Unification = struct
  let set m t =
    if !Common.show_debug then debug "META  %s <- %s\n%!" (V.Meta.to_string m) (T.to_string t);
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
    dom : int; (** domain (a level) *)
    cod : int; (** codomain (a level) *)
    ren : int option IntMap.t; (** renaming function, from levels in the domain to levels in the codomain *)
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
  if !Common.show_debug then debug "UNIFY %s WITH %s\n%!" (V.to_string k t) (V.to_string k u);
  (* Make sure that metavariable m applied to spine s equals t. *)
  let solve k m s t =
    if !Common.show_debug then debug "SOLVE %s =? %s\n" (V.to_string k (Meta (m, s))) (V.to_string k t);
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
            | _ ->
              raise Unification
              (* warning "\nignoring non-variable in meta spine\n"; *)
              (* cod+1, r *)
          )
        | [] -> 0, IntMap.empty
      in
      let cod, ren = aux s in
      { dom = k; cod; ren }
    in
    (* Add an extra variable to a renaming. *)
    let lift r = { dom = r.dom+1; cod = r.cod+1; ren = IntMap.add r.dom (Some r.cod) r.ren } in
    (* Apply a partial renaming to a value. Along the way, we also make sure that the metavariable does not occur in the term (occurs check). The result uses de Bruijn indices, so that binders can keep their original names. *)
    let rename (m:V.meta) (r:partial_renaming) (t:value) : term =
      let rec rename r t =
        (* The variable at level y in the codomain. *)
        let var y = T.Var' (r.cod - y - 1) in
        let t = V.force t in
        let spine l (t:term) = T.app_spine t (List.map (rename r) l) in
        match t with
        | Meta (m',l) ->
          if m'.id = m.id then (debug "OCCURS\n"; raise Unification); (* Occurs-check. *)
          spine l @@ Meta (`Generated m'.id)
        | Pi (i, c, a, ((x,_,_) as b)) ->
          let a = rename r a in
          let b = rename (lift r) @@ V.capp b (V.var r.dom) in
          Pi (i, c, x, a, b)
        | Arr (s, a, b) ->
          let a = rename r a in
          let b = rename r b in
          Arr (s, a, b)
        | Abs ((x,_,_) as t) ->
          let t = V.capp t (V.var r.dom) in
          Abs (Explicit, x, rename (lift r) t)
        | Sigma (a, ((x,_,_) as b)) ->
          let a = rename r a in
          let b = rename (lift r) @@ V.capp b (V.var r.dom) in
          Sigma (x, a, b)
        | Type n -> Type n
        | IndType i -> IndType i
        | IndTerm (t, l) -> IndTerm (t, List.map (rename r) l)
        | IndType_ind (i, t, l) -> spine l @@ IndType_ind (i, List.map (rename r) t)
        | Pair (t, u) -> Pair (rename r t, rename r u)
        | Pair_ind ((x,y,_,_) as t, l) ->
          let k = r.dom in
          let t = V.capp2 t (V.var k) (V.var (k+1)) in
          let t = rename (lift (lift r)) t in
          spine l @@ Pair_ind (x, y, t)
        | Tens (a,b) -> Tens (rename r a, rename r b)
        | TensPair (t, u) -> TensPair (rename r t, rename r u)
        | Tens_ind ((x,y,_,_) as t, l) ->
          let k = r.dom in
          let t = V.capp2 t (V.var k) (V.var (k+1)) in
          let t = rename (lift (lift r)) t in
          spine l @@ Tens_ind (x, y, t)
        | Eq(a,t,u) -> Eq (rename r a, rename r t, rename r u)
        | Refl t -> Refl (rename r t)
        | J (t, l) -> spine l @@ J (rename r t)
        | Flat a -> Flat (rename r a)
        | Flatten t -> Flatten (rename r t)
        | Flat_ind ((x,_,_) as t, l) ->
          let t = V.capp t (V.var r.dom) in
          let t = rename (lift r) t in
          spine l @@ Flat_ind (x, t)
        | Hole (pos, l) -> spine l @@ Hole pos
        | Var (x, l) ->
          (* x is a level in the domain and y a level in the codomain. *)
          spine l @@
          (
            match IntMap.find_opt x r.ren with
            | Some (Some y) -> var y
            | Some None ->
              if !Common.show_debug then debug "DUPLICATE %s\n" (V.to_string k (V.var x));
              raise Unification
            | None ->
              if !Common.show_debug then debug "ESCAPED %s\n" (V.to_string k (V.var x));
              raise Unification
          )
        | Opaque (o, l) ->
          spine l @@ Opaque (Some o)
        | I -> I
        | I0 -> I0
        | I1 -> I1
        | Iv (i, j) -> Iv (rename r i, rename r j)
        | Iw (i, j) -> Iw (rename r i, rename r j)
        | t -> failwith @@ Printf.sprintf "TODO: rename %s" (V.to_string k t)
      in
      rename r t
    in
    let t = rename m r t in
    let t =
      (* TODO: correctly handle side... *)
      T.abss (List.init r.cod (fun i -> "x" ^ string_of_int i)) t
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
    | IndTerm (t, l), IndTerm (t', l') ->
      if t <> t' then raise Unification;
      spine k l l'
    | IndType_ind (i, t, l), IndType_ind (i', t', l') ->
      if i <> i' then raise Unification;
      spine k t t'; (* NOTE: this is not a spine but ok *)
      spine k l l'
    | Pi (i, s, a, b), Pi (i', s', a', b') ->
      if i <> i' then raise Unification;
      if s <> s' then raise Unification;
      unify k a a';
      unify (k+1) (V.capp b (V.var k)) (V.capp b' (V.var k))
    | Abs t, Abs t' ->
      unify (k+1) (V.capp t (V.var k)) (V.capp t' (V.var k))
    (* eta-expansion *)
    | (Abs _ as t), u
    | t, (Abs _ as u) ->
      let x = V.var k in
      unify (k+1) (V.app t x) (V.app u x)
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
    | TensPair (t, u), TensPair (t', u') ->
      unify k t t';
      unify k u u'
    | Eq (a, t, u), Eq (a', t', u') ->
      unify k a a';
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
    | Refl t, Refl t' ->
      unify k t t'
    | J (r, l), J (r', l') ->
      unify k r r';
      spine k l l'
    | Opaque (o, l), Opaque (o', l') ->
      if o <> o' then raise Unification;
      spine k l l'
    | Var (x, l), Var (x', l') ->
      if x <> x' then raise Unification;
      spine k l l'
    | Hole (pos, l), Hole (pos', l') ->
      if pos <> pos' then raise Unification;
      spine k l l'
    | I, I | I0, I0 | I1, I1 -> ()
    | Iv (i, j), Iv (i', j')
    | Iw (i, j), Iw (i', j') ->
      unify k i i';
      unify k j j'
    | Meta _, Meta _ -> Unification.defer pos k t u
    | Meta (m, l), t -> solve k m l t
    | t, Meta (m, l) -> solve k m l t
    (* eta-expansion (needs to be after meta-variables, otherwise the spine might contain a pair and not be a pattern *)
    (* only for unapplied eliminators: an applied one is stuck (neutral) and
       applying it to a pair would only grow its spine, looping forever *)
    | (Pair_ind (_, []) as t), u
    | t, (Pair_ind (_, []) as u) ->
      let x = V.var k in
      let y = V.var (k+1) in
      let p = V.Pair (x,y) in
      unify (k+2) (V.app t p) (V.app u p)
    | (Tens_ind (_, []) as t), u
    | t, (Tens_ind (_, []) as u) ->
      let x = V.var k in
      let y = V.var (k+1) in
      let p = V.TensPair (x,y) in
      unify (k+2) (V.app t p) (V.app u p)
    | t, u ->
      if !Common.show_debug then debug "CLASH %s VS %s \n%!" (V.to_string k t) (V.to_string k u);
      raise Unification
  in
  Unification.defer pos k t u;
  while Unification.has_solvable () do
    let _pos, k, t, u = Unification.pop () in
    unify k t u
  done

(** Make sure that there are no unification problems left. *)
let finalize_unify () =
  (* Solve what can be. *)
  while Unification.has_solvable () do
    let pos, k, t, u = Unification.pop () in
    unify ~pos k t u
  done;
  if not @@ Unification.is_empty () then
    let pb =
      List.rev !Unification.deferred
      |> List.map (fun (pos,k,t,u) -> Printf.sprintf "- %s: %s vs %s" (Pos.opt_to_string pos) (V.to_string k t) (V.to_string k u))
      |> String.concat "\n"
    in
    warning "\n%d unsolved unification problems:\n%s\n" (List.length !Unification.deferred) pb

let unify_base = unify

let unify k env t a b =
  try unify ~pos:(T.Position.find_opt t) k a b
  with Unification -> error ~t "term has type %s but %s expected" (string_of_value k env a) (string_of_value k env b)

(*
(** Comparison of values. *)
let is_eq k (t:value) (u:value) =
  readback k t = readback k u

let eq k t u =
  if not @@ is_eq k t u then failwith "eq"
*)

(** Generate a fresh metavariable. *)
let fresh_meta ?pos env =
  let m = V.Meta.fresh ?pos () in
  (* We only keep variables. Here, i is a de Bruijn index in env. *)
  let rec aux i = function
    | [] -> []
    | (_x,v)::l ->
      match V.force v with
      | Var _ -> (T.Var' i)::(aux (i+1) l)
      | _ -> aux (i+1) l
  in
  let vars = aux 0 env in
  T.apps (T.Meta (`Generated m.id)) vars

(** Check that term has given type and elaborate it. Here, [k] is the current level (the number of bound variables, which is the length of [env] minus the number of definitions), values use de Bruijn levels and the elaborated terms use de Bruijn indices in [env]. *)
let rec check k env ctx (t:term) (a:value) : term =
  if !Common.show_debug then debug "CHECK %s : %s\n%!" (string_of_term env t) (string_of_value k env a);
  (* let cenv, benv = ctx in *)
  (* Printf.printf "      %s\n%!" (Context.to_string k ctx); *)
  let t0 = t in
  let pos = T.Position.find_opt t in
  match t, V.force a with
  | Abs (i, x, t), Pi (i', c, a, b) when i = i' ->
    let xv = V.var k in
    let k = k+1 in
    let env = (x,xv)::env in
    let ctx = Context.ext ~crispness:c ctx x a in
    let t = check k env ctx t (V.capp b xv) in
    Abs (i, x, t)
  | Abs (i, x, t), Arr (s, a, b) ->
    assert (i = Explicit);
    let xv = V.var k in
    let k = k+1 in
    let env = (x,xv)::env in
    let ctx = Context.ext_tens ctx s x a in
    let t = check k env ctx t b in
    Abs (i, x, t)
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
      match V.force a with
      | Sigma (a1, a2) ->
        let x1 = V.var k in
        let x2 = V.var (k+1) in
        let k = k+2 in
        let env = (y,x2)::(x,x1)::env in
        let ctx = Context.ext ~crispness:c (Context.ext ~crispness:c ctx x a1) y (V.capp a2 x1) in
        let t = check k env ctx t (V.capp b (Pair (x1, x2))) in
        Pair_ind (x, y, t)
      | _ -> failwith "pair_ind: type of argument is expected to be a Sigma type"
    )
  | Pair_ind _, Arr _ -> failwith "TODO: pair_ind vs arr"
  | TensPair (t, u), Tens (a, b) ->
    let ctxa, ctxb = Context.split ~t:t0 ~vars:(names k env) k (FV.term t) (FV.term u) ctx in
    let t = check k env ctxa t a in
    let u = check k env ctxb u b in
    TensPair (t, u)
  | Tens_ind (x, y, t), Pi (Explicit, c, a, b) ->
    (
      match V.force a with
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
  | Tens_ind (x, y, t), Arr (side, a, b) ->
    let a1, a2 =
      match V.force a with
      | Tens (a1, a2) -> a1, a2
      | _ -> error ~t:t0 "tensor expected for the argument of the arrow"
    in
    let x' = V.var k in
    let y' = V.var (k+1) in
    let k = k+2 in
    let env = (y,y')::(x,x')::env in
    let ctx =
      let cctx, bctx = ctx in
      let bctx = Bunch.tens ~side bctx (Bunch.Tens (Bunch.Decl (x, a1), Bunch.Decl (y, a2))) in
      cctx, bctx
    in
    let t = check k env ctx t b in
    Tens_ind (x, y, t)
  | IndType_ind (`Empty, []), Pi (Explicit, _, a, _)
  | IndType_ind (`Empty, []), Arr (_, a, _) ->
    unify k env t a (IndType `Empty);
    IndType_ind (`Empty, [])
  | IndType_ind (`Unit, [t]), Pi (Explicit, _, a, b) ->
    unify k env t a (IndType `Unit);
    let t = check k env ctx t (V.capp b (IndTerm (`Unit, []))) in
    IndType_ind (`Unit, [t])
  | IndType_ind (`Unit, [t]), Arr (_, a, b) ->
    unify k env t a (IndType `Unit);
    let t = check k env ctx t b in
    IndType_ind (`Unit, [t])    
  | IndType_ind (`Bool, [tf;tt]), Pi (Explicit, _, a, b) ->
    unify k env t a (IndType `Bool);
    let tf = check k env ctx tf (V.capp b (IndTerm (`Bool false, []))) in
    let tt = check k env ctx tt (V.capp b (IndTerm (`Bool true, []))) in
    IndType_ind (`Bool, [tf;tt])
  | IndType_ind (`Bool, [tf;tt]), Arr (_, a, b) ->
    unify k env t a (IndType `Bool);
    let tf = check k env ctx tf b in
    let tt = check k env ctx tt b in
    IndType_ind (`Bool, [tf;tt])
  | IndType_ind (`Nat, [tz;ts]), Pi (Explicit, c, a, b) ->
    unify k env t a (IndType `Nat);
    let tz = check k env ctx tz (V.capp b (IndTerm (`Zero, []))) in
    (* The type (n : ℕ) → C n → C (succ n) of the step. *)
    let s =
      let env = ["C", V.Abs b] in
      V.eval env @@ T.Pi (Explicit, c, "n", IndType `Nat, T.Pi (Explicit, c, "_", T.app (Var "C") (Var "n"), T.app (Var "C") (IndTerm (`Succ, [Var "n"]))))
    in
    let ts = check k env ctx ts s in
    IndType_ind (`Nat, [tz;ts])
  | IndType_ind (`Nat, _), Arr _ -> error ~t "induction on natural numbers is not supported for lax arrows"
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
  | Refl t, Eq (a, u, u') ->
    let t = check k env ctx t a in
    (
      let t = V.eval env t in
      try
        unify_base ~pos k t u;
        unify_base ~pos k t u'
      with Unification ->
        error ~t:t0 "reflexivity cannot prove %s ≡ %s" (string_of_value k env u) (string_of_value k env u')
    );
    Refl t
  | J r, Pi (_, _, a, b) ->
    (* we should make sure that b := {y : a} (p : x ≡ y) → P[x,y,p] *)
    let unpi ?icit k a =
      let a0 = a in
      match V.force a with
      | Pi (icit', _, a, b) when icit = None || Some icit' = icit -> a, b
      | _ -> error ~t "got %s but function type expected" (string_of_value k env a0)
    in
    let x =
      let y, k = V.var k, k+1 in
      let b', _ = unpi k (V.capp b y) in
      match b' with
      | Eq (a', x, y') when y' = y -> unify_base ~pos k a a'; x
      | _ -> error ~t "identity type expected"
    in
    let c = V.capp (snd @@ unpi ~icit:Explicit k @@ V.capp b x) (Refl x) in
    let r = check k env ctx r c in
    J r
  | Opaque o, a ->
    (* This is before implicit abstraction insertion so that the postulate gets its full type. *)
    let o = match o with Some o -> o | None -> incr V.abstract; `Postulate !V.abstract in
    important "\nPOSTULATE %s %s\n%!" (T.string_of_opaque o) (string_of_value k env a);
    Opaque (Some o)
  | _, Pi (Implicit, _, _, _) ->
    (* Insert implicit abstraction. *)
    check k env ctx (Abs (Implicit, "_", t)) a
  | Pi _, Type m
  | Sigma _, Type m
  | Arr _, Type m
  | Tens _, Type m
  | Flat _, Type m ->
    let t, level = check_type k env ctx t in
    if level > m then error ~t:t0 "universe level %d but at most %d expected" level m;
    t
  | Hole pos, a ->
    important "\nHOLE %s : %s IN\n%s\n%!" (Pos.to_string pos) (string_of_value k env a) (Context.to_string ~multiline:true ~crisp:false ~vars:(names k env) k ctx);
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
        try unify k env t0 a' a; t
        with Unification -> error ~t:t0 "%s has type %s but %s expected" (string_of_term env t) (string_of_value k env a') (string_of_value k env a)
    )

(** Check that a term is a type; returns the elaborated term and its universe level. *)
and check_type k env ctx a : term * int =
  if !Common.show_debug then debug "CHECK TYPE %s\n%!" (string_of_term env a);
  (*
  match a with
  | Hole pos -> Hole pos, 0
  | _ ->
    match infer k env ctx a with
    | a, Type l -> a, l
    | _, b -> error ~t:a "%s has type %s by type expected" (T.to_string a) (V.to_string k b)
  *)
  match infer k env ctx a with
  | a, Type l -> a, l
  | a, b -> unify k env a b (Type 0); a, 0
(* error ~t:a "%s has type %s by type expected" (T.to_string a) (V.to_string k b) *)

(** Infer the type of a term. *)
and infer k env ctx (t:term) : term * value =
  if !Common.show_debug then debug "INFER %s\n%!" (string_of_term env t);
  (* Printf.printf "ctx: %s\n%!" (Context.to_string k ctx); *)
  let t0 = t in
  (* let cenv, benv = ctx in *)
  match t with
  | Type n -> Type n, Type (n + 1)
  | IndType ind -> IndType ind, Type 0
  | IndTerm (`Unit, []) -> IndTerm (`Unit, []), IndType `Unit
  | IndTerm (`Bool b, []) -> IndTerm (`Bool b, []), IndType `Bool
  | IndTerm (`Zero, []) -> IndTerm (`Zero, []), IndType `Nat
  | IndTerm (`Succ, [n]) ->
    let n = check k env ctx n (IndType `Nat) in
    IndTerm (`Succ, [n]), IndType `Nat
  | IndTerm _ -> error ~t "constructor applied to the wrong number of arguments"
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
  | Eq (a, t, u) ->
    let a, l = check_type k env ctx a in
    let t, u =
      let a = V.eval env a in
      let t = check k env ctx t a in
      let u = check k env ctx u a in
      t, u
    in
    Eq (a, t, u), Type l
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
            | Left -> let ctxu, ctxt = Context.split ~t:t0 ~vars:(names k env) k (FV.term u) (FV.term t1) ctx in ctxt, ctxu
            | Right -> Context.split ~t:t0 ~vars:(names k env) k (FV.term t1) (FV.term u) ctx
          in
          let t = check k env ctxt t1 (Arr (s, a, b)) in
          let u = check k env ctxu u a in
          App (t, Explicit, u), b
        | a -> error ~t:t0 "%s is applied to %s but has type %s, which is not a function type" (string_of_term env t1) (string_of_term env u) (string_of_value k env a)
      )
    )
  | Var x ->
    let rec aux n = function
      | (y, _)::_ when x = y -> n
      | _::l -> aux (n+1) l
      | [] -> error ~t "undefined variable %s" x
    in
    (* The de Bruijn index of x in env (not a level!). *)
    let k = aux 0 env in
    let a = match Context.assoc_opt x ctx with Some a -> a | None -> error ~t "variable %s is in the context but not in the typing environment (crispness issue?)" x in
    Var' k, a
  | Meta (`Fresh pos) ->
    let a = V.eval env @@ fresh_meta env in
    let t = fresh_meta ?pos env in
    t, a
  | Import m ->
    let module_type m =
      match Context.assoc_opt m ctx with
      | None -> None
      | Some a ->
        match V.force a with
        | RecordType _ -> Some a
        | _ -> None
    in
    (
      match module_type m with
      | Some a ->
        warning "\nmodule %s apparently already imported, ignoring\n" m;
        Var m, a
      | None ->
        let pos = T.Position.find_opt t in
        let decls = Module.parse ?pos m in
        let _,tm,ty = check_decls k env ctx decls in
        if List.mem_assoc m tm then error ~t "module %s contains a field %s, this is expected to cause problems" m m;
        T.Record (`Recursive, tm), V.RecordType ty
    )
  | RecordField (t, x) ->
    let t0 = t in
    let t, a = infer k env ctx t in
    let l =
      match V.force a with
      | RecordType l -> l
      | _ -> error ~t:t0 "record type expected but got %s" (string_of_value k env a)
    in
    let a =
      match List.find_opt (fun (y,_,_) -> y = x) l with
      | Some (_,_,a) -> a
      | None -> error ~t:t0 "no field %s in %s" x (string_of_value k env a);
    in
    RecordField (t, x), a
  | I -> I, Type 0
  | I0 -> I0, I
  | I1 -> I1, I
  | Iv (i, j) ->
    let i = check k env ctx i I in
    let j = check k env ctx j I in
    Iv (i, j), I
  | Iw (i, j) ->
    let i = check k env ctx i I in
    let j = check k env ctx j I in
    Iw (i, j), I
  | _ -> error ~t "cannot infer type"

and check_decls k env ctx (decls:T.decls) =
  let tm = ref [] in
  let ty = ref [] in
  let env = ref env in
  let ctx = ref ctx in
  let decls = ref decls in
  while !decls <> [] do
    let decl = List.hd !decls in
    decls := List.tl !decls;
    match decl with
    | T.Def (x,c,abstract,a,t) ->
      Common.print "\n%sDECL  %s = %s%s\n%!" (if abstract then "ABSTRACT " else "") x (T.to_string t) (match a with Some a -> " " ^ T.crispy_colon c ^ " " ^ T.to_string a | None -> "");
      let t, a =
        match a with
        | Some a ->
          let a, _ = check_type k !env !ctx a in
          let a = V.eval !env a in
          let t = check k !env (Context.crisp ~crispness:c !ctx) t a in
          t, a
        | None ->
          infer k !env (Context.crisp ~crispness:c !ctx) t
      in
      let t =
        if not abstract then t else
          (
            (* The definition is elaborated to a fresh opaque constant so that it does not reduce, including when imported from another module. *)
            incr V.abstract;
            T.Opaque (Some (`Abstract (x, !V.abstract)))
          )
      in
      tm := (x,t) :: !tm;
      env := (x, V.eval !env t) :: !env;
      ctx := Context.ext ~crispness:c !ctx x a;
      ty := (x,c,a) :: !ty
    | Open t ->
      let t0 = t in
      let t, a = infer k !env !ctx t in
      let l =
        match V.force a with
        | RecordType l -> l
        | _ -> error ~t:t0 "record type expected but got %s" (string_of_value k !env a)
      in
      (* Fields which are already bound to the very same value (typically because the module was already opened) are not declared again: otherwise, modules re-exporting opened modules make the number of declarations blow up. *)
      let already_bound =
        match V.force (V.eval !env t) with
        | Record r ->
          fun x ->
            (
              match List.assoc_opt x !env, List.assoc_opt x r with
              | Some v, Some v' -> v == v'
              | _ -> false
            )
        | _ -> fun _ -> false
      in
      let l = List.filter (fun (x,_,_) -> not (already_bound x)) l in
      let pos = T.Position.find_opt t0 in
      List.iter (fun (x,c,_) -> decls := (Def (x,c,false,None,T.mk ?pos @@ RecordField(t0, x)) :: !decls)) (List.rev l)
  done;
  let tm = List.rev !tm in
  let ty = List.rev !ty in
  (!env,!ctx),tm,ty

let check_decls_toplevel decls =
  let env = ref ([] : V.environment) in
  let ctx = ref Context.empty in
  let add ?(crispness=T.Crisp) x a t =
    env := (x,t) :: !env;
    ctx := Context.ext ~crispness !ctx x a
  in
  if !Common.builtins then
    (
      let type0 = V.Type 0 in
      (* add "Type" type1 type0; *)
      (* add "U" type1 type0; *)
      add "TYPE" (V.Type 2) (V.Type 1);
      let empty = V.IndType `Empty in
      add "empty" type0 empty;
      let unit = V.IndType `Unit in
      add "unit" type0 unit;
      let bool = V.IndType `Bool in
      add "bool" type0 bool;
      add "false" bool (V.IndTerm (`Bool false, []));
      add "true" bool (V.IndTerm (`Bool true, []));
      (* The successor function (constructors are always fully applied, so we eta-expand). *)
      add "succ" (V.Pi (Explicit, Normal, IndType `Nat, ("_", IndType `Nat, []))) (V.eval [] @@ Abs (Explicit, "n", IndTerm (`Succ, [Var "n"])));
      (* Induction on natural numbers: {C : ℕ → Type} → C 0 → ((n : ℕ) → C n → C (succ n)) → (n : ℕ) → C n. *)
      add "Nat-ind"
        (V.eval [] @@
           Pi (Implicit, Normal, "C", Pi (Explicit, Normal, "_", IndType `Nat, Type 0),
               Pi (Explicit, Normal, "_", T.app (Var "C") (IndTerm (`Zero, [])),
                   Pi (Explicit, Normal, "_", Pi (Explicit, Normal, "n", IndType `Nat, Pi (Explicit, Normal, "_", T.app (Var "C") (Var "n"), T.app (Var "C") (IndTerm (`Succ, [Var "n"])))),
                       Pi (Explicit, Normal, "n", IndType `Nat, T.app (Var "C") (Var "n"))))))
        (V.eval [] @@ Abs (Implicit, "C", T.abss ["z"; "s"; "n"] (T.app (IndType_ind (`Nat, [Var "z"; Var "s"])) (Var "n"))));
    );
  ignore @@ check_decls 0 !env !ctx decls

let check_meta () =
  let m =
    V.Meta.variables
    |> V.Meta.Dynarray.to_list
    |> List.filter (fun (m:V.meta) -> m.value = None && m.pos <> None)
    |> List.map (fun m -> "- " ^ V.Meta.to_string m ^ " at " ^ Pos.to_string (Option.get m.pos))
    |> String.concat "\n"
  in
  if m <> "" then important "\nUNSOLVED META\n%s\n%!" m
