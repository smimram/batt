let debug fmt = Printf.ksprintf (fun s -> print_string @@ Terminal.yellow s) fmt

let important fmt = Printf.ksprintf (fun s -> print_string @@ Terminal.blue ~bold:true s) fmt

let error fmt = Printf.ksprintf (fun s -> print_string @@ Terminal.red ~bold:true s) fmt
