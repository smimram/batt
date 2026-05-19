let show_debug = ref true

let debug fmt =
  if !show_debug then Printf.ksprintf (fun s -> print_string @@ Terminal.yellow s) fmt
  else Printf.ksprintf (fun _ -> ()) fmt

let important fmt = Printf.ksprintf (fun s -> print_string @@ Terminal.blue ~bold:true s) fmt

let error fmt = Printf.ksprintf (fun s -> print_string @@ Terminal.red ~bold:true s) fmt
