(** Inline include tokens, returning a Menhir token supplier and a position getter. *)
let inline_include dirs token initial_lexbuf =
  let current_lexbuf = ref initial_lexbuf in
  let stack = Stack.create () in
  let get_pos () = Sedlexing.lexing_positions !current_lexbuf in
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
      Stack.push (ic, lexbuf) stack;
      current_lexbuf := new_lexbuf;
      next ()
    | Parser.EOF ->
      begin
        match Stack.pop_opt stack with
        | None ->
          let (start, stop) = get_pos () in
          (Parser.EOF, start, stop)
        | Some (ic, saved_lb) ->
          close_in ic;
          current_lexbuf := saved_lb;
          next ()
      end
    | t ->
      let (start, stop) = get_pos () in
      (t, start, stop)
  in
  (next, get_pos)
