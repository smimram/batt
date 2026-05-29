type inductive_type = Term.inductive_type
[@@deriving show]
type inductive_term = Term.inductive_term
[@@deriving show]
type icit = Term.icit
[@@deriving show]
type crispness = Term.crispness
[@@deriving show]
type side = Term.side
[@@deriving show]
type term = Term.t
type var = string
[@@deriving show]

(** A value. *)
type t =
  | Type of int (** universe level *)
  | IndType of inductive_type
  | IndTerm of inductive_term
  | IndType_ind of inductive_type * t list * spine
  | Pi of icit * crispness * t * closure
  | Abs of side option * closure
  | Sigma of t * closure
  | Pair of t * t
  | Pair_ind of closure2 * spine
  | Arr of side * t * t
  | Tens of t * t
  | TensPair of t * t
  | Tens_ind of closure2 * spine
  | Flat of t
  | Flatten of t
  | Flat_ind of closure * spine
  | Eq of t * t
  | Refl
  | J of t * spine
  | Meta of meta * spine
  | Var of int * spine
  | Hole of (Pos.t [@opaque]) * spine
  | Postulate of int * spine
  | RecordType of (string * crispness * t) list
  | Record of (string * t) list
  | RecordField of string * spine
[@@deriving show]

(** A closure. *)
and closure = var * (term[@opaque]) * (environment[@opaque])

(** A binary closure. *)
and closure2 = var * var * (term[@opaque]) * (environment[@opaque])

(** An environment. *)
and environment = (var * t) list

(** A metavariable. *)
and meta =
  {
    id : int;
    pos : Pos.t option [@opaque];
    mutable value : t option;
  }

(** A list of arguments: first in the list, last to be applied. *)
and spine = t list

(** Metavariables. *)
module Meta = struct
  type t = meta

  (* Backward compatibility. *)
  module Dynarray = struct
    type 'a t = 'a array ref
    let create () : 'a t = ref [||]
    let length (a : 'a t) = Array.length !a
    let to_list (a : 'a t) = Array.to_list !a
    let add_last (a : 'a t) x = a := Array.append !a [|x|]
    let get (a : 'a t) i = Array.get !a i
  end

  let variables = Dynarray.create ()

  let to_string m = "?" ^ string_of_int m.id

  (** Generate a fresh metavariable. *)
  let fresh ?pos () =
    let m = { id = Dynarray.length variables; pos; value = None } in
    Dynarray.add_last variables m;
    m

  (** Get metavariable with given id. *)
  let get id =
    Dynarray.get variables id
end

(** Postulate counter. *)
let postulate = ref (-1)

(** Evaluate a term to a value. *)
let rec eval (env:environment) : Term.t -> t = function
  | Type n -> Type n
  | IndType a -> IndType a
  | IndTerm t -> IndTerm t
  | IndType_ind (ind, args) -> IndType_ind (ind, List.map (eval env) args, [])
  | Pi (i, c, x, a, t) -> Pi (i, c, eval env a, (x, t, env))
  | Abs (_, s, x, t) -> Abs (s, (x, t, env))
  | App (t, _, u) -> app (eval env t) (eval env u)
  | Sigma (x, a, t) -> Sigma (eval env a, (x, t, env))
  | Pair (t, u) -> Pair (eval env t, eval env u)
  | Pair_ind (x, y, t) -> Pair_ind ((x, y, t, env), [])
  | Arr (s, a, b) -> Arr (s, eval env a, eval env b)
  | Tens (a, b) -> Tens (eval env a, eval env b)
  | TensPair (t, u) -> TensPair (eval env t, eval env u)
  | Tens_ind (x, y, t) -> Tens_ind ((x, y, t, env), [])
  | Flat t -> Flat (eval env t)
  | Flatten t -> Flatten (eval env t)
  | Flat_ind (x, t) -> Flat_ind ((x, t, env), [])
  | Eq (t, u) -> Eq (eval env t, eval env u)
  | Refl -> Refl
  | J r -> J (eval env r, [])
  | Var x ->
    (
      match List.assoc_opt x env with
      | Some v -> v
      | None -> failwith @@ Printf.sprintf "eval: could not find %s" x
    )
  | Var' n -> snd @@ List.nth env n
  | Let (_c,x,_a,t,u) ->
    eval env (Term.app (Abs(Explicit, None, x, u)) t)
  | Postulate (Some n) -> Postulate (n, [])
  | Postulate None -> assert false
  | Hole pos -> Hole (pos, [])
  | Meta (`Fresh pos) -> fresh_meta ?pos env
  | Meta (`Generated id) -> Meta (Meta.get id, [])
  | RecordType l ->
    let l = List.map (fun (x, c, a) -> x, c, eval env a) l in
    RecordType l
  | Record (r,l) ->
    (
      match r with
      | `Recursive ->
        let _, l =
          List.fold_left_map
            (fun env (x,t) ->
               let t = eval env t in
               let env = (x,t)::env in
               env, (x, t)
            ) env l
        in
        Record l
      | `NonRecursive ->
        Record (List.map (fun (x, t) -> x, eval env t) l)
    )
  | RecordField (t, x) ->
    app (RecordField (x, [])) (eval env t)

(** Make a variable. *)
and var k = Var (k, [])

(** Generate a fresh metavariable. *)
and fresh_meta ?pos env =
  let m = Meta.fresh ?pos () in
  (* We only keep variables in the environment. *)
  let vars = List.filter_map (fun (_x,v) -> match force v with Var _ -> Some v | _ -> None) env in
  Meta (m, vars)

(** Apply a value to another. *)
and app t u =
  match force t, force u with
  | Abs (_, f), u -> capp f u
  | IndType_ind (`Unit, [t], []), IndTerm `Unit -> t
  | IndType_ind (`Bool, [tf;_tt], []), IndTerm (`Bool false) -> tf
  | IndType_ind (`Bool, [_tf;tt], []), IndTerm (`Bool true) -> tt
  | IndType_ind (ind, t, l), u -> IndType_ind (ind, t, u::l)
  | Pair_ind (t, []), Pair (u, v) -> capp2 t u v
  | Pair_ind (t, l), u -> Pair_ind (t, u::l)
  | Tens_ind (t, []), TensPair (u, v) -> capp2 t u v
  | Tens_ind (t, l), u -> Tens_ind (t, u::l)
  | Flat_ind (t, []), Flatten u -> capp t u
  | Flat_ind (t, l), u -> Flat_ind (t, u::l)
  | J (r, [_]), Refl -> r
  | J (r, l), u -> J (r, u::l)
  | Var (x, l), u -> Var (x, u::l)
  | Meta (m, l), u -> Meta (m, u::l)
  | Hole (pos, l), u -> Hole (pos, u::l)
  | Postulate (n, l), u -> Postulate (n, u::l)
  | _ -> failwith @@ Printf.sprintf "vapp: %s vs %s" (show t) (show u)

(** Apply a value to a list of values. *)
and apps t = function
  | u::uu -> apps (app t u) uu
  | [] -> t

(** Apply a value to a spine of values. *)
and app_spine t = function
  | u::uu -> app (app_spine t uu) u
  | [] -> t

(** Instantiate a closure with a value. *)
and capp ((x,t,env):closure) (v:t) =
  eval ((x,v)::env) t

and capp2 ((x,y,t,env):closure2) (u:t) (v:t) =
  eval ((y,v)::(x,u)::env) t

(** Remove already evaluated values. *)
and force t =
  match t with
  | Meta (m, s) when m.value <> None -> app_spine (Option.get m.value) s
  | _ -> t

(** Reify a value as a term. *)
let rec readback k v : Term.t =
  let var_name k = "x" ^ string_of_int k in
  let spine l t = Term.app_spine t (List.map (readback k) l) in
  match force v with
  | Type n -> Type n
  | IndType ind -> IndType ind
  | IndType_ind (ind, args, l) -> spine l @@ IndType_ind (ind, List.map (readback k) args)
  | IndTerm t -> IndTerm t
  | Pi (i, c, a, b) -> Pi (i, c, var_name k, readback k a, readback (k+1) (capp b (var k)))
  | Abs (s, f) -> Abs (Explicit, s, var_name k, readback (k+1) (capp f (var k)))
  | Sigma (a, b) -> Sigma (var_name k, readback k a, readback (k+1) (capp b (var k)))
  | Pair (t, u) -> Pair (readback k t, readback k u)
  | Pair_ind (t, l) -> spine l @@ Pair_ind (var_name k, var_name (k+1), readback (k+2) @@ capp2 t (var k) (var (k+1)))
  | Arr (s, a, b) -> Arr (s, readback k a, readback k b)
  | Tens (a, b) -> Tens (readback k a, readback k b)
  | TensPair (t, u) -> TensPair (readback k t, readback k u)
  | Tens_ind (t, l) -> spine l @@ Tens_ind (var_name k, var_name (k+1), readback (k+2) @@ capp2 t (var k) (var (k+1)))
  | Flat a -> Flat (readback k a)
  | Flatten t -> Flatten (readback k t)
  | Flat_ind (t, l) -> spine l @@ Flat_ind (var_name k, readback (k+1) (capp t (var k)))
  | Eq (t, u) -> Eq (readback k t, readback k u)
  | Refl -> Refl
  | J (r, l) -> spine l @@ J (readback k r)
  | Meta (m, l) -> spine l @@ Meta (`Generated m.id)
  | Var (i, l) -> spine l @@ Var' i
  | Postulate (n, l) -> spine l @@ Postulate (Some n)
  | Hole (pos, l) -> spine l @@ Hole pos
  | RecordType l -> RecordType (List.map (fun (x, c, a) -> x, c, readback k a) l)
  | Record l -> Record (`NonRecursive, List.map (fun (x, t) -> x, readback k t) l)
  | RecordField (x, l) ->
    assert (l <> []);
    let t, l =
      let l = List.rev l in
      List.hd l, List.rev @@ List.tl l
    in
    spine l @@ RecordField (readback k t, x)

let to_string k v = Term.to_string @@ readback k v
