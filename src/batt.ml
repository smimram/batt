let () =
  Printexc.record_backtrace true;
  Printf.printf "Welcome to BATT!\n%!";
  let () =
    let incdirs =
      let prefix = Filename.dirname @@ Filename.dirname Sys.executable_name in
      let share = Filename.concat (Filename.concat prefix "share") "batt" in
      List.filter Sys.file_exists ["celltt"; "stdlib"; Filename.concat share "stdlib"]
    in
    Common.include_directories_list := incdirs
  in
  let files = ref [] in
  Arg.parse
    (Arg.align
       [
         "-I", Arg.String (fun s -> Common.include_directories_list := s :: !Common.include_directories_list), " Include directory";
         "--no-colors", Arg.Unit (fun () -> Terminal.enable_colors := false), " Disable colors";
         "--no-debug", Arg.Unit (fun () -> Common.show_debug := false), " Hide debug messages";
       ]
    )
    (fun s -> files := s :: !files) "batt [options] files";
  let files = List.rev !files in
  try
    List.iter
      (fun fname ->
         Printf.printf "\nChecking %s...\n%!" fname;
         let ic = open_in fname in
         let lexbuf = Sedlexing.Utf8.from_channel ic in
         Sedlexing.set_filename lexbuf fname;
         let decls =
           try MenhirLib.Convert.Simplified.traditional2revised Parser.main (Sedlexing.with_tokenizer Lexer.token lexbuf)
           with
           | Failure err ->
             let pos = Sedlexing.lexing_positions lexbuf in
             let err = Printf.sprintf "Lexing error %s: %s" (Pos.to_string pos) err in
             failwith err
           | Parser.Error ->
             let pos = Sedlexing.lexing_positions lexbuf in
             let err = Printf.sprintf "Parsing error %s" (Pos.to_string pos) in
             failwith err
         in
         close_in ic;
         Lang.check_decls_toplevel decls
      ) files;
    Lang.finalize_unify ();
    Lang.check_meta ()
  with
  | Failure err ->
    let bt = Printexc.raw_backtrace_to_string @@ Printexc.get_raw_backtrace () in
    Common.error "\nError: %s\n\n%s%!" err bt;
    exit 1
