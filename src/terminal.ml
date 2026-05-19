let enable_colors = ref true

let color ?(bold=false) c = Printf.sprintf "\027["^string_of_int c^(if bold then ";1" else "")^"m"

let colorize c ?bold s =
  if !enable_colors then color ?bold c ^ s ^ color 0
  else s

let bold = colorize ~bold:true 0
let red = colorize 31
let green = colorize 32
let yellow = colorize 33
let blue = colorize 34
