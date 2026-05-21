(** Helper functions for the parser. *)

open Lang

let abs ?(icit=Explicit) x t = TAbs(icit, None, x, t)

let app ?(icit=Explicit) t u = TApp(t, icit, u)

(** Multiple abstractions. *)
let rec abss l t =
  match l with
  | [] -> t
  | x::l -> abs x (abss l t)

let abs_pattern x t =
  match x with
  | `Var (x,d) -> TAbs (Explicit, d, x, t)
  | `Unit -> TIndType_ind (`Unit, [t])
  | `Pair (x, y) -> TPair_ind (x, y, t)
  | `Tens (x, y) -> TTens_ind (x, y, t)
  | `Flatten x -> TFlat_ind (x, t)
  | `Refl -> TJ t

let rec abss_pattern l t =
  match l with
  | [] -> t
  | x::l -> abs_pattern x (abss_pattern l t)

(** Multiple pi abstractions. *)
let rec pis l b =
  (* Multiple pi abstractions of the same type. *)
  let rec pis' i c l a b =
    match l with
    | [] -> b
    | x::l -> TPi (i, c, x, a, pis' i c l a b)
  in
  match l with
  | [] -> b
  | (i,c,x,a)::l -> pis' i c x a (pis l b)
  
