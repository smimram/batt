let () =
  Printexc.record_backtrace true;
  Printf.printf "Welcome to BATT!\n%!";
  let () =
    let incdirs =
      let prefix = Filename.dirname @@ Filename.dirname Sys.executable_name in
      let share = Filename.concat (Filename.concat prefix "share") "batt" in
      List.filter Sys.file_exists ["graytt"; "stdlib"; Filename.concat share "stdlib"]
    in
    Common.include_directories_list := incdirs
  in
  let files = ref [] in
  Arg.parse
    (Arg.align
       [
         "-I", Arg.String (fun s -> Common.include_directories_list := s :: !Common.include_directories_list), " Include directory";
         "--debug", Arg.Set Common.show_debug, " Show debug messages";
         "--de-bruijn", Arg.Set Common.de_bruijn, " Use de Bruijn indices";
         "--no-colors", Arg.Clear Terminal.enable_colors, " Disable colors";
         "--no-builtins", Arg.Clear Common.builtins, " Disable builtins";
       ]
    )
    (fun s -> files := s :: !files) "batt [options] files";
  let files = List.rev !files in
  try
    List.iter
      (fun fname ->
         Printf.printf "\nChecking %s...\n%!" fname;
         let decls = Module.parse_file fname in
         Lang.check_decls_toplevel decls
      ) files;
    Lang.finalize_unify ();
    Lang.check_meta ()
  with
  | Failure err ->
    let bt = Printexc.raw_backtrace_to_string @@ Printexc.get_raw_backtrace () in
    Common.error "\nError: %s\n\n%s%!" err bt;
    exit 1
