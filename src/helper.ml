(** Helper functions for the parser. *)

open Term

let abs ~pos ?(icit=Explicit) x t = mk ~pos @@ Abs(icit, x, t)

let app ~pos ?(icit=Explicit) t u = mk ~pos @@ App(t, icit, u)

(** A natural number numeral, as iterated successors of zero. *)
let rec nat ~pos n =
  assert (n >= 0);
  if n = 0 then mk ~pos @@ IndTerm (`Zero, [])
  else mk ~pos @@ IndTerm (`Succ, [nat ~pos (n-1)])

(** Multiple abstractions. *)
let rec abss ~pos l t =
  match l with
  | [] -> t
  | x::l -> abs ~pos x (abss ~pos l t)

let abs_pattern ~pos x t =
  mk ~pos
    (
      match x with
      | `Var (icit, x) -> Abs (icit, x, t)
      | `Unit -> IndType_ind (`Unit, [t])
      | `Pair (x, y) -> Pair_ind (x, y, t)
      | `Tens (x, y) -> Tens_ind (x, y, t)
      | `Flatten x -> Flat_ind (x, t)
      | `Refl -> J t
      | `Bool _ -> failwith @@ Printf.sprintf "%s: boolean pattern not allowed here" (Pos.to_string pos)
      | `Nat _ -> failwith @@ Printf.sprintf "%s: natural number pattern not allowed here" (Pos.to_string pos)
    )

let rec abss_pattern ~pos l t =
  match l with
  | [] -> t
  | x::l -> abs_pattern ~pos x (abss_pattern ~pos l t)

(** Multiple pi abstractions. *)
let rec pis ~pos l b =
  (* Multiple pi abstractions of the same type. *)
  let rec pis' i c l a b =
    match l with
    | [] -> b
    | x::l -> mk ~pos @@ Pi (i, c, x, a, pis' i c l a b)
  in
  match l with
  | [] -> b
  | (i,c,x,a)::l -> pis' i c x a (pis ~pos l b)
  

(** Compile a definition by multiple clauses, each consisting of a list of patterns and a body. *)
let rec compile_clauses ~pos rows =
  let error fmt = Printf.ksprintf (fun s -> failwith @@ Printf.sprintf "%s: %s" (Pos.to_string pos) s) fmt in
  match rows with
  | [] -> error "missing case in definition"
  | ([], t)::_ -> t
  | _ ->
    let heads = List.map (function (p::_, _) -> p | [], _ -> error "clauses have different numbers of arguments") rows in
    let rows = List.map (fun (l, t) -> List.tl l, t) rows in
    if List.exists (function `Bool _ -> true | _ -> false) heads then
      let branch b =
        List.filter_map
          (fun (p, (l, t)) ->
             match p with
             | `Bool b' -> if b = b' then Some (l, t) else None
             | `Var (Explicit, "_") -> Some (l, t)
             | `Var (Explicit, x) -> Some (l, mk ~pos @@ Let (Crisp, x, IndType `Bool, IndTerm (`Bool b, []), t))
             | _ -> error "unsupported pattern in boolean matching"
          ) (List.combine heads rows)
      in
      mk ~pos @@ IndType_ind (`Bool, [compile_clauses ~pos (branch false); compile_clauses ~pos (branch true)])
    else if List.exists (function `Nat _ -> true | _ -> false) heads then
      (* Case analysis on natural numbers (no recursive calls). *)
      let n =
        List.find_map (function `Nat (Some x) when x <> "_" -> Some x | _ -> None) heads
        |> Option.value ~default:"_n"
      in
      let branch zero =
        List.filter_map
          (fun (p, (l, t)) ->
             match p with
             | `Nat None -> if zero then Some (l, t) else None
             | `Nat (Some x) ->
               if zero then None
               else if x = n || x = "_" then Some (l, t)
               else Some (l, mk ~pos @@ Let (Normal, x, IndType `Nat, Var n, t))
             | `Var (Explicit, "_") -> Some (l, t)
             | `Var (Explicit, x) ->
               let v = if zero then IndTerm (`Zero, []) else IndTerm (`Succ, [Var n]) in
               Some (l, mk ~pos @@ Let (Normal, x, IndType `Nat, v, t))
             | _ -> error "unsupported pattern in natural number matching"
          ) (List.combine heads rows)
      in
      let tz = compile_clauses ~pos (branch true) in
      let ts = abss ~pos [n; "_"] (compile_clauses ~pos (branch false)) in
      mk ~pos @@ IndType_ind (`Nat, [tz; ts])
    else if List.for_all (function `Var _ -> true | _ -> false) heads then
      let icit = match List.hd heads with `Var (i, _) -> i | _ -> assert false in
      let names = List.filter_map (function `Var (i, x) -> if i <> icit then error "implicit and explicit arguments mixed in clauses" else if x = "_" then None else Some x | _ -> assert false) heads in
      let names = List.sort_uniq compare names in
      let z = match names with [] -> "_" | [x] -> x | _ -> error "clauses should use the same variable name for the same argument" in
      abs ~pos ~icit z (compile_clauses ~pos rows)
    else
      let p = List.hd heads in
      if List.exists (fun p' -> p' <> p) heads then error "unsupported pattern in multi-clause definition";
      abs_pattern ~pos p (compile_clauses ~pos rows)

(** A toplevel item, before grouping clauses. *)
type item =
  | Sig of Pos.t * string * crispness * t (** type signature *)
  | Clause of Pos.t * string * pattern list * t (** defining clause *)
  | Decls of decls (** other declarations *)

and pattern = [`Var of icit * string | `Unit | `Pair of string * string | `Tens of string * string | `Flatten of string | `Refl | `Bool of bool | `Nat of string option]

(** Group signatures with their defining clauses. *)
let rec group_decls = function
  | [] -> []
  | Decls d :: items -> d @ group_decls items
  | Clause (pos, x, _, _) :: _ -> failwith @@ Printf.sprintf "%s: missing type declaration for %s" (Pos.to_string pos) x
  | Sig (pos, x, c, a) :: items ->
    let rec clauses = function
      | Clause (pos, y, l, t) :: items when y = x -> let cl, items = clauses items in (pos, (l, t)) :: cl, items
      | items -> [], items
    in
    let cl, items = clauses items in
    (
      match cl, items with
      | [], Clause (pos, _, _, _) :: _ -> failwith (Pos.to_string pos ^ ", function name should be the same as in type declaration")
      | [], _ -> failwith @@ Printf.sprintf "%s: missing definition for %s" (Pos.to_string pos) x
      | _ -> ()
    );
    let pos = List.fold_left (fun pos (pos', _) -> Pos.union pos pos') (fst (List.hd cl)) cl in
    Def (x, c, Some a, compile_clauses ~pos (List.map snd cl)) :: group_decls items
