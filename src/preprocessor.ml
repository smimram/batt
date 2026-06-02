(** Replace "open include m" with "include m open m" *)
let swap_open_include token lexbuf =
  let inq = Queue.create () in
  let outq = Queue.create () in
  let was_open = ref false in
  let rec aux () =
    if not @@ Queue.is_empty outq then Queue.pop outq else
      let token =
        if Queue.is_empty inq then token lexbuf
        else Queue.pop inq
      in
      match token with
      | Parser.OPEN ->
        was_open := true;
        aux ()
      | Parser.IMPORT m when !was_open ->
        was_open := false;
        Queue.push Parser.N outq;
        Queue.push Parser.OPEN outq;
        Queue.push (Parser.IDENT m) outq;
        Parser.IMPORT m
      | t ->
        if !was_open then
          (
            Queue.push t inq;
            was_open := false;
            Parser.OPEN
          )
        else
          t
  in
  aux ()
