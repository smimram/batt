let debug fmt = Printf.ksprintf (fun s -> print_string @@ Terminal.yellow s) fmt
