type var = string

(** Basic inductive types. *)
type inductive_type = [`Empty | `Unit | `Bool]
[@@deriving show]

let string_of_inductive_type = function
  | `Empty -> "Empty"
  | `Unit -> "Unit"
  | `Bool -> "Bool"

(** Basic inductive terms. *)
type inductive_term = [`Unit | `Bool of bool]
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
  | IndTerm of inductive_term
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
  | Eq of t * t
  | Refl
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
    | Eq (t, u) -> union (term t) (term u)
    | Refl -> empty
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
end

let crispy_colon = function
  | Normal -> ":"
  | Crisp -> "∷"

(** String representation of a term. *)
let rec to_string t =
  let colon = crispy_colon in
  match t with
  | Type 0 -> "Type"
  | Type n -> Printf.sprintf "Type %d" n
  | IndType ind -> string_of_inductive_type ind
  | IndType_ind (ind, args) -> Printf.sprintf "%s_ind(%s)" (string_of_inductive_type ind) (String.concat "," @@ List.map to_string args)
  | IndTerm `Unit -> "tt"
  | IndTerm (`Bool b) -> string_of_bool b
  | Pi (i, c, x, a, t) ->
    (
      match i with
      | Explicit -> Printf.sprintf "(%s %s %s) → %s" x (colon c) (to_string a) (to_string t)
      | Implicit -> Printf.sprintf "{%s %s %s} → %s" x (colon c) (to_string a) (to_string t)
    )
  | Abs (i, x, t) ->
    (
      match i with
      | Explicit -> Printf.sprintf "λ%s.%s" x (to_string t)
      | Implicit -> Printf.sprintf "λ{%s}.%s" x (to_string t)
    )
  | App (t, i, u) ->
    (
      match i with
      | Explicit -> Printf.sprintf "(%s %s)" (to_string t) (to_string u)
      | Implicit -> Printf.sprintf "(%s {%s})" (to_string t) (to_string u)
    )
  | Sigma (x, a, t) -> Printf.sprintf "(Σ(%s : %s).%s)" x (to_string a) (to_string t)
  | Pair (t, u) -> Printf.sprintf "(%s, %s)" (to_string t) (to_string u)
  | Pair_ind (x, y, t) -> Printf.sprintf "(λ(%s,%s).%s)" x y (to_string t)
  | Arr (s, a, b) -> Printf.sprintf "%s →%s %s" (to_string a) (string_of_side s) (to_string b)
  | Tens (a, b) -> Printf.sprintf "(%s ⨂ %s)" (to_string a) (to_string b)
  | TensPair (t, u) -> Printf.sprintf "(%s ⊗ %s)" (to_string t) (to_string u)
  | Tens_ind (x, y, t) -> Printf.sprintf "(λ(%s⊗%s).%s)" x y (to_string t)
  | Flat t -> Printf.sprintf "♭%s" (to_string t)
  | Flatten t -> Printf.sprintf "𝄫%s" (to_string t)
  | Flat_ind (x,t) -> Printf.sprintf "♭_ind(%s,%s)" x (to_string t)
  | Eq (t,u) -> Printf.sprintf "%s ≡ %s" (to_string t) (to_string u)
  | Refl -> Printf.sprintf "refl"
  | J r -> Printf.sprintf "J(%s)" (to_string r)
  | Var x -> x
  | Var' n -> Printf.sprintf "x-%d" n
  | Let (c,x,a,t,u) -> Printf.sprintf "let %s %s %s = %s in %s" x (colon c) (to_string a) (to_string t) (to_string u)
  | Postulate n -> "postulate" ^ (match n with Some n -> string_of_int n | None -> "")
  | Hole _ -> "?"
  | Meta (`Fresh _) -> "_"

  | Meta (`Generated n) -> Printf.sprintf "?%d" n
  | Import m -> "import " ^ m
  | Record _ -> "record"
  | RecordType l ->
    let l = String.concat "; " @@ List.map (fun (x,c,a) -> x ^ " " ^ crispy_colon c ^ " " ^ to_string a) l in
    Printf.sprintf "{ %s }" l
  | RecordField (t,x) -> Printf.sprintf "%s.%s" (to_string t) x
