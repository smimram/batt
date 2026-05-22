let show_debug = ref true

let debug fmt =
  if !show_debug then
    (
      if !Terminal.enable_colors then print_string (Terminal.color 33);
      Printf.kfprintf
        (fun oc ->
           if !Terminal.enable_colors then output_string oc (Terminal.color 0);
           flush oc)
        stdout fmt
    )
  else Printf.ifprintf stdout fmt

let important fmt = Printf.ksprintf (fun s -> print_string @@ Terminal.blue ~bold:true s) fmt

let error fmt = Printf.ksprintf (fun s -> print_string @@ Terminal.red ~bold:true s) fmt
