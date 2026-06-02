(** Open module in given file. *)
let parse_file fname =
  In_channel.with_open_bin fname
    (fun ic ->
       let lexbuf = Sedlexing.Utf8.from_channel ic in
       Sedlexing.set_filename lexbuf fname;
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
    )

(** Open module with given name. *)
let parse ?pos name =
  let dirs = Common.include_directories () in
  let fname = name ^ ".batt" in
  let fname =
    match List.find_map (fun dir ->
        let f = Filename.concat dir fname in
        if Sys.file_exists f then Some f else None) dirs
    with
    | Some f -> f
    | None ->
      failwith @@ Printf.sprintf "%s: could not find library file %s (in %s)" (Pos.opt_to_string pos) fname (String.concat ", " dirs)
  in
  Printf.printf "Include %s...\n%!" fname;
  parse_file fname
