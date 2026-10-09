let show_debug = ref false

let print_string = ref print_string

let include_directories_list = ref ([] : string list)

let include_directories () = "." :: !include_directories_list

(** Declare builtins. *)
let builtins = ref true

(** Use de Bruijn indices for variables. *)
let de_bruijn = ref false

let print fmt =
  Printf.ksprintf (fun s -> !print_string s; flush stdout) fmt

let debug fmt =
  if !show_debug then
    (
      !print_string (Terminal.color `Yellow);
      Printf.ksprintf (fun s -> !print_string s; !print_string (Terminal.color `Black); flush stdout) fmt
    )
  else Printf.ksprintf ignore fmt

let important fmt =
  Printf.ksprintf (fun s ->
      !print_string (Terminal.color ~bold:true `Blue);
      !print_string s;
      !print_string (Terminal.color `Black);
      flush stdout
    ) fmt

let warning fmt =
  Printf.ksprintf (fun s ->
      !print_string (Terminal.color ~bold:true `Purple);
      !print_string s;
      !print_string (Terminal.color `Black);
      flush stdout
    ) fmt

let error fmt =
  Printf.ksprintf (fun s ->
      !print_string (Terminal.color ~bold:true `Red);
      !print_string s;
      !print_string (Terminal.color `Black);
      flush stdout
    ) fmt
