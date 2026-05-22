(** Inline include tokens. *)
let inline_include dirs token =
  let stack = Stack.create () in
  let current_lexbuf = ref None in
  let rec aux () =
    let lexbuf = Option.get !current_lexbuf in
    match token lexbuf with
    | Parser.INCLUDE fname ->
      let fname = fname ^ ".batt" in
      let fname =
        match List.find_map (fun dir -> let fname = Filename.concat dir fname in if Sys.file_exists fname then Some fname else None) dirs with
        | Some fname -> fname
        | None ->
          failwith @@ Printf.sprintf "Could not find library file %s (in %s)" fname (String.concat ", " dirs)
      in
      Printf.printf "Include %s...\n%!" fname;
      let ic = open_in fname in
      let new_lexbuf = Lexing.from_channel ic in
      new_lexbuf.lex_curr_p <- {
        pos_fname = fname;
        pos_lnum = 1;
        pos_bol = 0;
        pos_cnum = 0
      };
      Stack.push (ic, lexbuf) stack;
      current_lexbuf := Some new_lexbuf;
      aux ()
    | EOF ->
      begin
        match Stack.pop_opt stack with
        | None ->
          current_lexbuf := None;
          Parser.EOF
        | Some (ic, lexbuf) ->
          close_in ic;
          current_lexbuf := Some lexbuf;
          aux ()
      end
    | t -> t
  in
  fun lexbuf ->
    if Option.is_none !current_lexbuf then current_lexbuf := Some lexbuf;
    let t = aux () in
    (* Copy position info from the active lexbuf (possibly an included file) back to the main lexbuf so that menhir and callers record the correct file/line/column. *)
    let cur = Option.value !current_lexbuf ~default:lexbuf in
    if cur != lexbuf then begin
      lexbuf.Lexing.lex_start_p <- cur.Lexing.lex_start_p;
      lexbuf.Lexing.lex_curr_p  <- cur.Lexing.lex_curr_p
    end;
    t
