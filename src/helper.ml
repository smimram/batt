(** Helper functions for the parser. *)

open Term

let abs ~pos ?(icit=Explicit) x t = mk ~pos @@ Abs(icit, x, t)

let app ~pos ?(icit=Explicit) t u = mk ~pos @@ App(t, icit, u)

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
  
