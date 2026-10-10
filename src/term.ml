type var = string

(** Basic inductive types. *)
type inductive_type = [`Empty | `Unit | `Bool | `Nat | `List]
[@@deriving show]

let string_of_inductive_type = function
  | `Empty -> "Empty"
  | `Unit -> "Unit"
  | `Bool -> "Bool"
  | `Nat -> "Nat"
  | `List -> "List"

(** Basic inductive terms. *)
type inductive_term = [`Unit | `Bool of bool | `Zero | `Succ | `Nil | `Cons]
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

(** Opaque constants, which do not reduce: postulates and abstract definitions (the name is only used for printing, the integer is a unique identifier). *)
type abstract = [`Postulate of int | `Abstract of string * int]
[@@deriving show]

let string_of_opaque = function
  | `Postulate n -> "postulate" ^ string_of_int n
  | `Abstract (x, _) -> x

type crispness = Normal | Crisp
[@@deriving show]

(** A term. *)
type t =
  | Type of int (** universe level *)
  | IndType of inductive_type * t list (** inductive type with its parameters *)
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
  | Opaque of abstract option (** an opaque constant ([None] for a fresh postulate) *)
  | Global of string * int (** a global definition, unfolded on demand, with its name (only used for printing) and its identifier *)
  | Hole of Pos.t
  | Meta of [`Fresh of Pos.t option | `Generated of int] (** metavariable with given internal identifier *)
  | Import of string (** import a module *)
  | RecordType of (string * crispness * t) list
  | Record of [`Recursive | `NonRecursive] * (string * t) list
  | RecordField of t * string
  | I | I0 | I1 | Iv of t * t | Iw of t * t

(** A declaration. *)
and decl =
  | Def of (string * crispness * bool * t option * t) (** a definition, the boolean indicates whether it is abstract (does not reduce) *)
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
    | IndType (_, l) -> list l
    | IndType_ind (_, l) -> list l
    | IndTerm (_, l) -> list l
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
    | Opaque _ -> empty
    | Global _ -> empty
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

module StringSet = Set.Make(String)

(** A variant of the name [x] which is not [used], obtained by adding primes. *)
let rec fresh_name used x =
  if x = "_" || not (used x) then x else fresh_name used (x ^ "'")

(** Make the names of a list of variables (most recent first) distinct, by adding primes to the ones shadowing older ones. *)
let fresh_names vars =
  snd @@ List.fold_left (fun (used, vars) x -> let x = fresh_name (fun x -> StringSet.mem x used) x in StringSet.add x used, x::vars) (StringSet.empty, []) (List.rev vars)

(** String representation of a term. The list [vars] gives the (distinct) names of the variables, indexed by de Bruijn indices. A bound variable whose name is already in [vars] is renamed by adding primes: [ren] records those renamings, which are used for named variables [Var x]. *)
let rec to_string ?(vars=[]) ?(ren=[]) t =
  let fresh vars x = fresh_name (fun x -> List.mem x vars) x in
  let bind x t = let x' = fresh vars x in x', to_string ~vars:(x'::vars) ~ren:((x,x')::ren) t in
  let bind2 x y t =
    let x' = fresh vars x in
    let y' = fresh (x'::vars) y in
    x', y', to_string ~vars:(y'::x'::vars) ~ren:((y,y')::(x,x')::ren) t
  in
  let to_string t = to_string ~vars ~ren t in
  let colon = crispy_colon in
  match t with
  | Type 0 -> "Type"
  | Type n -> Printf.sprintf "Type %d" n
  | IndType (ind, []) -> string_of_inductive_type ind
  | IndType (ind, args) -> Printf.sprintf "(%s %s)" (string_of_inductive_type ind) (String.concat " " @@ List.map to_string args)
  | IndType_ind (ind, args) -> Printf.sprintf "%s_ind(%s)" (string_of_inductive_type ind) (String.concat "," @@ List.map to_string args)
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
      | None -> Printf.sprintf "succ(%s)" @@ to_string n
    )
  | IndTerm (`Nil, []) -> "nil"
  | IndTerm (`Cons, [x; l]) -> Printf.sprintf "(cons %s %s)" (to_string x) (to_string l)
  | IndTerm _ -> assert false
  | Pi (i, c, x, a, t) ->
    let x, t = bind x t in
    (
      match i with
      | Explicit -> Printf.sprintf "(%s %s %s) → %s" x (colon c) (to_string a) t
      | Implicit -> Printf.sprintf "{%s %s %s} → %s" x (colon c) (to_string a) t
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
      | Explicit -> Printf.sprintf "(%s %s)" (to_string t) (to_string u)
      | Implicit -> Printf.sprintf "(%s {%s})" (to_string t) (to_string u)
    )
  | Sigma (x, a, t) -> let x, t = bind x t in Printf.sprintf "(Σ(%s : %s).%s)" x (to_string a) t
  | Pair (t, u) -> Printf.sprintf "(%s, %s)" (to_string t) (to_string u)
  | Pair_ind (x, y, t) -> let x, y, t = bind2 x y t in Printf.sprintf "(λ(%s,%s).%s)" x y t
  | Arr (s, a, b) -> Printf.sprintf "%s →%s %s" (to_string a) (string_of_side s) (to_string b)
  | Tens (a, b) -> Printf.sprintf "(%s ⨂ %s)" (to_string a) (to_string b)
  | TensPair (t, u) -> Printf.sprintf "(%s ⊗ %s)" (to_string t) (to_string u)
  | Tens_ind (x, y, t) -> let x, y, t = bind2 x y t in Printf.sprintf "(λ(%s⊗%s).%s)" x y t
  | Flat t -> Printf.sprintf "♭%s" (to_string t)
  | Flatten t -> Printf.sprintf "𝄫%s" (to_string t)
  | Flat_ind (x,t) -> let x, t = bind x t in Printf.sprintf "♭_ind(%s,%s)" x t
  | Eq (_,t,u) -> Printf.sprintf "%s ≡ %s" (to_string t) (to_string u)
  | Refl t -> Printf.sprintf "refl(%s)" (to_string t)
  | J r -> Printf.sprintf "J(%s)" (to_string r)
  | Var x -> Option.value ~default:x @@ List.assoc_opt x ren
  | Var' n when 0 <= n && n < List.length vars && not !Common.de_bruijn -> List.nth vars n
  | Var' n -> Printf.sprintf "x-%d" n
  | Let (c,x,a,t,u) -> let x, u = bind x u in Printf.sprintf "let %s %s %s = %s in %s" x (colon c) (to_string a) (to_string t) u
  | Opaque n -> (match n with Some n -> string_of_opaque n | None -> "postulate")
  | Global (x, _) -> x
  | Hole _ -> "?"
  | Meta (`Fresh _) -> "_"

  | Meta (`Generated n) -> Printf.sprintf "?%d" n
  | Import m -> "import " ^ m
  | Record _ -> "record"
  | RecordType l ->
    let l = String.concat "; " @@ List.map (fun (x,c,a) -> x ^ " " ^ crispy_colon c ^ " " ^ to_string a) l in
    Printf.sprintf "{ %s }" l
  | RecordField (t,x) -> Printf.sprintf "%s.%s" (to_string t) x
  | I -> "𝕀"
  | I0 -> "𝕀0"
  | I1 -> "𝕀1"
  | Iv (i, j) -> Printf.sprintf "%s 𝕀∨ %s" (to_string i) (to_string j)
  | Iw (i, j) -> Printf.sprintf "%s 𝕀∧ %s" (to_string i) (to_string j)
