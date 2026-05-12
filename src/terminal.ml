let color ?(bold=false) c = Printf.sprintf "\027["^string_of_int c^(if bold then ";1" else "")^"m"

let bold s = color ~bold:true 0 ^ s ^ color 0
let red s = color 31 ^ s ^ color 0
let green s = color 32 ^ s ^ color 0
let yellow s = color 33 ^ s ^ color 0
let blue ?bold s = color ?bold 34 ^ s ^ color 0
