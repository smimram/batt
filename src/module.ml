let parse fname =
  In_channel.with_open_bin fname (fun ic ->
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
