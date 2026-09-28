type var = string

(** Basic inductive types. *)
type inductive_type = [`Empty | `Unit | `Bool | `Nat]
[@@deriving show]

let string_of_inductive_type = function
  | `Empty -> "Empty"
  | `Unit -> "Unit"
  | `Bool -> "Bool"
  | `Nat -> "Nat"

(** Basic inductive terms. *)
type inductive_term = [`Unit | `Bool of bool | `Zero | `Succ]
[@@deriving show]

(** Side for lax arrows. *)
type side = Left | Right
[@@deriving show]

let string_of_side = function
  | Left -> "ₗ"
  | Right -> "ᵣ"

let string_of_opt_side s =
  Option.value ~default:"" @@ Option.map string_of_side s

type icit = Explicit | Implicit
[@@deriving show]

type crispness = Normal | Crisp
[@@deriving show]

(** A term. *)
type t =
  | Type of int (** universe level *)
  | IndType of inductive_type
  | IndType_ind of inductive_type * t list
  | IndTerm of inductive_term * t list (* Constructors are always applied to arguments (use an eta-expansion if needed) *)
  | Pi of icit * crispness * string * t * t (** pi-type *)
  | Abs of icit * string * t
  | App of t * icit * t
  | Sigma of string * t * t
  | Pair of t * t
  | Pair_ind of string * string * t
  | Arr of side * t * t (** lax arrow type *)
  | Tens of t * t
  | TensPair of t * t
  | Tens_ind of string * string * t
  | Flat of t
  | Flatten of t
  | Flat_ind of string * t
  | Eq of t * t * t
  | Refl of t
  | J of t
  | Var of var
  | Var' of int (** a variable given de Bruijn index *) (* TODO: it would be much better to have preterms (strings) and terms (de Bruijn) *)
  | Let of crispness * string * t * t * t
  | Postulate of int option (** a postulate with given internal identifier *)
  | Hole of Pos.t
  | Meta of [`Fresh of Pos.t option | `Generated of int] (** metavariable with given internal identifier *)
  | Import of string (** import a module *)
  | RecordType of (string * crispness * t) list
  | Record of [`Recursive | `NonRecursive] * (string * t) list
  | RecordField of t * string
  | I | I0 | I1 | Iv of t * t | Iw of t * t

(** A declaration. *)
and decl =
  | Def of (string * crispness * t option * t)
  | Open of t

(** A list of declarations. *)
and decls = decl list

let rec abss l t =
  match l with
  | x::l -> Abs (Explicit, x, abss l t)
  | [] -> t

let app ?(icit=Explicit) t u =
  App (t, icit, u)

(* Apply a term to a list (not a spine!) of values. *)
let rec apps t = function
  | u::uu -> apps (App (t, Explicit, u)) uu
  | [] -> t

let rec app_spine ?icit t = function
  | u::uu -> app ?icit (app_spine t uu) u
  | [] -> t

module Position = struct
  module E = Ephemeron.K1.Make(struct type nonrec t = t let equal = (==) let hash = Hashtbl.hash end)
  let (cache : Pos.t E.t) = E.create 100
  let register t pos = E.add cache t pos
  let find_opt t = E.find_opt cache t
  let to_string_comma t =
    match find_opt t with
    | Some pos -> Pos.to_string pos ^ ", "
    | None -> ""
end

let mk ?pos t =
  (match pos with Some pos -> Position.register t pos | None -> ());
  t

module FV = struct
  include Set.Make(String)

  let to_string fv = String.concat "," @@ List.of_seq @@ to_seq fv

  let rec term t =
    let list l = List.fold_left (fun fv t -> union fv (term t)) empty l in
    match t with
    | Type _ -> empty
    | IndType _ -> empty
    | IndType_ind (_, l) -> list l
    | IndTerm _ -> empty
    | Pi (_, _, x, a, b)
    | Sigma (x, a, b) -> union (term a) (remove x (term b))
    | Abs (_, x, t) -> remove x (term t)
    | App (t, _, u)
    | Pair (t, u) -> union (term t) (term u)
    | Pair_ind (x, y, t) -> remove x (remove y (term t))
    | Arr (_, a, b)
    | Tens (a, b) -> union (term a) (term b)
    | TensPair (t, u) -> union (term t) (term u)
    | Tens_ind (x, y, t) -> remove x (remove y (term t))
    | Flat a -> term a
    | Flatten t -> term t
    | Flat_ind (x, t) -> remove x (term t)
    | Eq (a, t, u) -> union (term a) @@ union (term t) (term u)
    | Refl t -> term t
    | J r -> term r
    | Var x -> singleton x
    | Var' _ -> assert false
    | Let (_c, _x, a, t, u) -> union (term a) @@ union (term t) (term u)
    | Postulate _ -> empty
    | Hole _ -> empty
    | Meta _ -> empty
    | Import _ -> assert false
    | Record _ -> failwith "TODO"
    | RecordType l -> List.fold_left (fun fv (_x, _c, a) -> union fv (term a)) empty l
    | RecordField (t, _x) -> term t
    | I | I0 | I1 -> empty
    | Iv (i, j) | Iw (i, j) -> union (term i) (term j)
end

let crispy_colon = function
  | Normal -> ":"
  | Crisp -> "∷"

module IntSet = Set.Make(Int)
module StringSet = Set.Make(String)

(** Free de Bruijn indices of a term. *)
let free_indices t =
  let rec aux n t =
    (* n is the number of binders we went through *)
    let list l = List.fold_left (fun s t -> IntSet.union s (aux n t)) IntSet.empty l in
    match t with
    | Var' i -> if i >= n then IntSet.singleton (i-n) else IntSet.empty
    | Type _ | IndType _ | Var _ | Postulate _ | Hole _ | Meta _ | Import _ | I | I0 | I1 -> IntSet.empty
    | IndType_ind (_, l) | IndTerm (_, l) -> list l
    | Pi (_, _, _, a, t) | Sigma (_, a, t) -> IntSet.union (aux n a) (aux (n+1) t)
    | Abs (_, _, t) | Flat_ind (_, t) -> aux (n+1) t
    | Pair_ind (_, _, t) | Tens_ind (_, _, t) -> aux (n+2) t
    | App (t, _, u) | Pair (t, u) | Arr (_, t, u) | Tens (t, u) | TensPair (t, u) | Iv (t, u) | Iw (t, u) -> list [t; u]
    | Flat t | Flatten t | Refl t | J t | RecordField (t, _) -> aux n t
    | Eq (a, t, u) -> list [a; t; u]
    | Let (_, _, a, t, u) -> IntSet.union (list [a; t]) (aux (n+1) u)
    | RecordType l -> list @@ List.map (fun (_, _, a) -> a) l
    | Record (`NonRecursive, l) -> list @@ List.map snd l
    | Record (`Recursive, l) ->
      (* each field is bound in the following ones *)
      snd @@ List.fold_left (fun (n, s) (_, t) -> n+1, IntSet.union s (aux n t)) (n, IntSet.empty) l
  in
  aux 0 t

(** A variant of the name [x] which does not belong to [used], obtained by adding primes. *)
let rec fresh_name used x =
  if x = "_" || not (StringSet.mem x used) then x else fresh_name used (x ^ "'")

(** Make the names of a list of variables (most recent first) distinct, by adding primes to the ones shadowing older ones. *)
let fresh_names vars =
  snd @@ List.fold_left (fun (used, vars) x -> let x = fresh_name used x in StringSet.add x used, x::vars) (StringSet.empty, []) (List.rev vars)

(** Name of the variable with de Bruijn index [n] in [vars]: when it is shadowed by more recent variables with the same name, we add one prime for each of those. *)
let var_name vars n =
  let rec aux i shadow = function
    | x::_ when i = n ->
      let shadow = List.length @@ List.filter (fun y -> y = x) shadow in
      Some (x ^ String.make shadow '\'')
    | x::l -> aux (i+1) (x::shadow) l
    | [] -> None
  in
  if n < 0 then None else aux 0 [] vars

(** String representation of a term. The list [vars] gives the names of the variables, indexed by de Bruijn indices (most recent first); shadowed variables are disambiguated by [var_name]. A bound variable keeps its name, unless this would capture a variable occurring in its scope, in which case we add primes to it: [ren] records those renamings, which are used for named variables [Var x]. *)
let rec to_string ?(ren=[]) vars t =
  (* Names of the variables of vars which occur in t, under n binders. *)
  let used n t =
    IntSet.fold (fun i used -> if i < n then used else match var_name vars (i-n) with Some x -> StringSet.add x used | None -> used) (free_indices t) StringSet.empty
  in
  (* Bind a variable x in t: we return the name used for x and the representation of t. We only look for the variables occurring in t when x could capture one of them. *)
  let bind x t =
    (* Printed names of variables are of the form y followed by primes, with y in vars. *)
    let rec base x = if String.ends_with ~suffix:"'" x then base (String.sub x 0 (String.length x - 1)) else x in
    let x' = if List.mem (base x) (List.map base vars) then fresh_name (used 1 t) x else x in
    x', to_string ~ren:((x,x')::ren) (x'::vars) t
  in
  (* Bind two variables x and y (y being the most recent) in t. *)
  let bind2 x y t =
    let used = used 2 t in
    let y' = fresh_name used y in
    let x' = fresh_name (if IntSet.mem 1 (free_indices t) then StringSet.add y' used else used) x in
    x', y', to_string ~ren:((y,y')::(x,x')::ren) (y'::x'::vars) t
  in
  let to_string vars t = to_string ~ren vars t in
  let colon = crispy_colon in
  match t with
  | Type 0 -> "Type"
  | Type n -> Printf.sprintf "Type %d" n
  | IndType ind -> string_of_inductive_type ind
  | IndType_ind (ind, args) -> Printf.sprintf "%s_ind(%s)" (string_of_inductive_type ind) (String.concat "," @@ List.map (to_string vars) args)
  | IndTerm (`Unit, []) -> "tt"
  | IndTerm (`Bool b, []) ->  string_of_bool b
  | IndTerm (`Zero, []) -> "0"
  | IndTerm (`Succ, [n]) ->
    (* Print closed natural numbers as numerals. *)
    let rec numeral k = function
      | IndTerm (`Zero, []) -> Some k
      | IndTerm (`Succ, [n]) -> numeral (k+1) n
      | _ -> None
    in
    (
      match numeral 1 n with
      | Some k -> string_of_int k
      | None -> Printf.sprintf "succ(%s)" @@ to_string vars n
    )
  | IndTerm _ -> assert false
  | Pi (i, c, x, a, t) ->
    let x, t = bind x t in
    (
      match i with
      | Explicit -> Printf.sprintf "(%s %s %s) → %s" x (colon c) (to_string vars a) t
      | Implicit -> Printf.sprintf "{%s %s %s} → %s" x (colon c) (to_string vars a) t
    )
  | Abs (i, x, t) ->
    let x, t = bind x t in
    (
      match i with
      | Explicit -> Printf.sprintf "λ%s.%s" x t
      | Implicit -> Printf.sprintf "λ{%s}.%s" x t
    )
  | App (t, i, u) ->
    (
      match i with
      | Explicit -> Printf.sprintf "(%s %s)" (to_string vars t) (to_string vars u)
      | Implicit -> Printf.sprintf "(%s {%s})" (to_string vars t) (to_string vars u)
    )
  | Sigma (x, a, t) -> let x, t = bind x t in Printf.sprintf "(Σ(%s : %s).%s)" x (to_string vars a) t
  | Pair (t, u) -> Printf.sprintf "(%s, %s)" (to_string vars t) (to_string vars u)
  | Pair_ind (x, y, t) -> let x, y, t = bind2 x y t in Printf.sprintf "(λ(%s,%s).%s)" x y t
  | Arr (s, a, b) -> Printf.sprintf "%s →%s %s" (to_string vars a) (string_of_side s) (to_string vars b)
  | Tens (a, b) -> Printf.sprintf "(%s ⨂ %s)" (to_string vars a) (to_string vars b)
  | TensPair (t, u) -> Printf.sprintf "(%s ⊗ %s)" (to_string vars t) (to_string vars u)
  | Tens_ind (x, y, t) -> let x, y, t = bind2 x y t in Printf.sprintf "(λ(%s⊗%s).%s)" x y t
  | Flat t -> Printf.sprintf "♭%s" (to_string vars t)
  | Flatten t -> Printf.sprintf "𝄫%s" (to_string vars t)
  | Flat_ind (x,t) -> let x, t = bind x t in Printf.sprintf "♭_ind(%s,%s)" x t
  | Eq (_,t,u) -> Printf.sprintf "%s ≡ %s" (to_string vars t) (to_string vars u)
  | Refl t -> Printf.sprintf "refl(%s)" (to_string vars t)
  | J r -> Printf.sprintf "J(%s)" (to_string vars r)
  | Var x -> Option.value ~default:x @@ List.assoc_opt x ren
  | Var' n ->
    (
      match var_name vars n with
      | Some x when not !Common.de_bruijn -> x
      | _ -> Printf.sprintf "x-%d" n
    )
  | Let (c,x,a,t,u) -> let x, u = bind x u in Printf.sprintf "let %s %s %s = %s in %s" x (colon c) (to_string vars a) (to_string vars t) u
  | Postulate n -> "postulate" ^ (match n with Some n -> string_of_int n | None -> "")
  | Hole _ -> "?"
  | Meta (`Fresh _) -> "_"

  | Meta (`Generated n) -> Printf.sprintf "?%d" n
  | Import m -> "import " ^ m
  | Record _ -> "record"
  | RecordType l ->
    let l = String.concat "; " @@ List.map (fun (x,c,a) -> x ^ " " ^ crispy_colon c ^ " " ^ to_string vars a) l in
    Printf.sprintf "{ %s }" l
  | RecordField (t,x) -> Printf.sprintf "%s.%s" (to_string vars t) x
  | I -> "𝕀"
  | I0 -> "𝕀0"
  | I1 -> "𝕀1"
  | Iv (i, j) -> Printf.sprintf "%s 𝕀∨ %s" (to_string vars i) (to_string vars j)
  | Iw (i, j) -> Printf.sprintf "%s 𝕀∧ %s" (to_string vars i) (to_string vars j)
