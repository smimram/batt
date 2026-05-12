let () =
  Printexc.record_backtrace true;
  Printf.printf "Welcome to BATT!\n%!";
  let files = List.tl @@ Array.to_list Sys.argv in
  try
    List.iter
      (fun fname ->
         Printf.printf "\nChecking %s...\n%!" fname;
         let ic = open_in fname in
         let lexbuf = Lexing.from_channel ic in
         Lexing.set_filename lexbuf fname;
         let decls =
           try Parser.main (Lexer.token |> Preprocessor.inline_include) lexbuf
           with
           | Failure err ->
             let pos = Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf in
             let err = Printf.sprintf "Lexing error %s: %s" (Pos.to_string pos) err in
             failwith err
           | Parser.Error ->
             let pos = Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf in
             let err = Printf.sprintf "Parsing error %s" (Pos.to_string pos) in
             failwith err
         in
         close_in ic;
         Lang.check_decls_toplevel decls
      ) files
  with
  | Failure err ->
    let bt = Printexc.raw_backtrace_to_string @@ Printexc.get_raw_backtrace () in
    Common.error "\nError: %s\n\n%s%!" err bt;
    exit 1

