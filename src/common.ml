let show_debug = ref true

let debug fmt =
  if !show_debug then
    (
      print_string (Terminal.color `Yellow);
      Printf.kfprintf (fun oc -> output_string oc (Terminal.color `Black); flush oc) stdout fmt
    )
  else Printf.ifprintf stdout fmt

let important fmt =
  Printf.ksprintf (fun s ->
      print_string (Terminal.color ~bold:true `Blue);
      print_string s;
      print_string (Terminal.color `Black)
    ) fmt

let warning fmt =
  Printf.ksprintf (fun s ->
      print_string (Terminal.color ~bold:true `Purple);
      print_string s;
      print_string (Terminal.color `Black)
    ) fmt

let error fmt =
  Printf.ksprintf (fun s ->
      print_string (Terminal.color ~bold:true `Red);
      print_string s;
      print_string (Terminal.color `Black)
    ) fmt
