let enable_colors = ref true

let color ?(bold=false) c =
  if !enable_colors then Printf.sprintf "\027["^string_of_int c^(if bold then ";1" else "")^"m"
  else ""

let color ?bold c =
  let c =
    match c with
    | `Black -> 0
    | `Red -> 31
    | `Green -> 32
    | `Yellow -> 33
    | `Blue -> 34
    | `Purple -> 35
    | `Cyan -> 36
    | `White -> 37
  in
  color ?bold c
