let () =
  Printexc.record_backtrace true;
  Printf.printf "Welcome to BATT!\n%!";
  let incdirs =
    let prefix = Filename.dirname @@ Filename.dirname Sys.executable_name in
    let share = Filename.concat (Filename.concat prefix "share") "batt" in
    List.filter Sys.file_exists ["stdlib"; Filename.concat share "stdlib"]
  in
  let incdirs = ref incdirs in
  let files = ref [] in
  Arg.parse
    (Arg.align
       [
         "-I", Arg.String (fun s -> incdirs := s :: !incdirs), " Include directory"
       ]
    )
    (fun s -> files := s :: !files) "batt [options] files";
  let files = List.rev !files in
  let incdirs = "." :: List.rev !incdirs in
  try
    List.iter
      (fun fname ->
         Printf.printf "\nChecking %s...\n%!" fname;
         let ic = open_in fname in
         let lexbuf = Lexing.from_channel ic in
         Lexing.set_filename lexbuf fname;
         let decls =
           try Parser.main (Lexer.token |> Preprocessor.inline_include incdirs) lexbuf
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

