(** Inline include tokens, returning a Menhir token supplier.
    Positions are reflected back into initial_lexbuf after each token so the
    caller can read them via Sedlexing.lexing_positions / lexing_position_curr. *)
let inline_include dirs token initial_lexbuf =
  let current_lexbuf = ref initial_lexbuf in
  (* Stack entries carry the saved curr-position of initial_lexbuf so we can
     restore it when the include ends (prevents corrupting offset state). *)
  let stack = Stack.create () in
  let rec next () =
    let lexbuf = !current_lexbuf in
    match token lexbuf with
    | Parser.INCLUDE fname ->
      let fname = fname ^ ".batt" in
      let fname =
        match List.find_map (fun dir ->
          let f = Filename.concat dir fname in
          if Sys.file_exists f then Some f else None) dirs
        with
        | Some f -> f
        | None ->
          failwith @@ Printf.sprintf "Could not find library file %s (in %s)" fname (String.concat ", " dirs)
      in
      Printf.printf "Include %s...\n%!" fname;
      let ic = open_in fname in
      let new_lexbuf = Sedlexing.Utf8.from_channel ic in
      Sedlexing.set_filename new_lexbuf fname;
      let saved_initial = Sedlexing.lexing_position_curr initial_lexbuf in
      Stack.push (ic, lexbuf, saved_initial) stack;
      current_lexbuf := new_lexbuf;
      next ()
    | Parser.EOF ->
      begin
        match Stack.pop_opt stack with
        | None ->
          let (start, stop) = Sedlexing.lexing_positions !current_lexbuf in
          (Parser.EOF, start, stop)
        | Some (ic, saved_lb, saved_initial) ->
          close_in ic;
          Sedlexing.set_filename initial_lexbuf saved_initial.Lexing.pos_fname;
          Sedlexing.set_position initial_lexbuf saved_initial;
          current_lexbuf := saved_lb;
          next ()
      end
    | t ->
      let (start, stop) = Sedlexing.lexing_positions !current_lexbuf in
      if !current_lexbuf != initial_lexbuf then begin
        Sedlexing.set_filename initial_lexbuf stop.Lexing.pos_fname;
        Sedlexing.set_position initial_lexbuf stop
      end;
      (t, start, stop)
  in
  next
