let () =
  Printexc.record_backtrace true;
  Printf.printf "Welcome to BATT!\n%!";
  let incdirs =
    let prefix = Filename.dirname @@ Filename.dirname Sys.executable_name in
    let share = Filename.concat (Filename.concat prefix "share") "batt" in
    List.filter Sys.file_exists ["celltt"; "stdlib"; Filename.concat share "stdlib"]
  in
  let incdirs = ref incdirs in
  let files = ref [] in
  Arg.parse
    (Arg.align
       [
         "-I", Arg.String (fun s -> incdirs := s :: !incdirs), " Include directory";
         "--no-colors", Arg.Unit (fun () -> Terminal.enable_colors := false), " Disable colors";
         "--no-debug", Arg.Unit (fun () -> Common.show_debug := false), " Hide debug messages";
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
         let lexbuf = Sedlexing.Utf8.from_channel ic in
         Sedlexing.set_filename lexbuf fname;
         let (supplier, get_pos) = Preprocessor.inline_include incdirs Lexer.token lexbuf in
         let last_start = ref Lexing.dummy_pos in
         let last_stop = ref Lexing.dummy_pos in
         let tracked_supplier () =
           let (tok, start, stop) = supplier () in
           last_start := start; last_stop := stop;
           (tok, start, stop)
         in
         let decls =
           try
             (MenhirLib.Convert.Simplified.traditional2revised Parser.main) tracked_supplier
           with
           | Failure err ->
             let pos = get_pos () in
             let err = Printf.sprintf "Lexing error %s: %s" (Pos.to_string pos) err in
             failwith err
           | Parser.Error ->
             let err = Printf.sprintf "Parsing error %s" (Pos.to_string (!last_start, !last_stop)) in
             failwith err
         in
         close_in ic;
         Lang.check_decls_toplevel decls
      ) files;
    Lang.check_meta ()
  with
  | Failure err ->
    let bt = Printexc.raw_backtrace_to_string @@ Printexc.get_raw_backtrace () in
    Common.error "\nError: %s\n\n%s%!" err bt;
    exit 1
