(** Helper functions for the parser. *)

open Lang

(** Multiple abstractions. *)
let rec abss l t =
  match l with
  | [] -> t
  | x::l -> TAbs (x, abss l t)

let abs_pattern x t =
  match x with
  | `Var x -> TAbs (x, t)
  | `Tens (x, y) -> TTens_ind (x, y, t)

let rec abss_pattern l t =
  match l with
  | [] -> t
  | x::l -> abs_pattern x (abss_pattern l t)

(** Multiple pi abstractions. *)
let rec pis l b =
  (* Multiple pi abstractions of the same type. *)
  let rec pis' c l a b =
    match l with
    | [] -> b
    | x::l -> TPi (c, x, a, pis' c l a b)
  in
  match l with
  | [] -> b
  | (c,x,a)::l -> pis' c x a (pis l b)
