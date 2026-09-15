(** Interaction with a webpage. *)

open Js_of_ocaml

module Html = Dom_html

let doc = Html.document

let debug s = Console.console##debug (Js.string s)

let loop s =
  debug "Type checking code";
  Lang.check_decls_toplevel @@ Module.parse_string s

let number_of_int n = Js.number_of_float (float n)

let run _ =
  let jsget x = Js.Opt.get x (fun () -> assert false) in
  let get_element_by_id id = doc##getElementById (Js.string id) |> jsget in
  let files = get_element_by_id "files" |> Html.CoerceTo.select |> jsget in
  let input = get_element_by_id "input" |> Html.CoerceTo.textarea |> jsget in
  let output = get_element_by_id "output" |> Html.CoerceTo.textarea |> jsget in
  let send = get_element_by_id "send" |> Html.CoerceTo.button |> jsget in
  let clear = get_element_by_id "clear" |> Html.CoerceTo.button |> jsget in

  let print s =
    let old = Js.to_string output##.value in
    let s = if old = "" && s.[0] = '\n' then String.sub s 1 (String.length s - 1) else s in
    let s = old ^ s in
    output##.value := Js.string s;
    output##.scrollTop := number_of_int output##.scrollHeight
  in
  let error s =
    print ("^(o.o)^ Error: " ^ s ^ "\n")
  in
  let highlight () = ignore (Js.Unsafe.eval_string "highlight();") in
  let read () =
    Js.to_string input##.value
  in
  let do_send () =
    output##.value := Js.string "";
    try read () |> String.trim |> loop
    with
    | Failure e -> error e
    | e -> error (Printexc.to_string e)
  in
  Common.print_string := print;
  Common.include_directories_list := "stdlib" :: !Common.include_directories_list;

  Sys.readdir "stdlib"
  |> Array.to_list
  |> List.sort Stdlib.compare
  |> List.filter (String.ends_with ~suffix:".batt")
  |> List.iter (fun s ->
      let o = Html.createOption Html.document in
      o##.value := Js.string s;
      o##.innerHTML := Js.string (Filename.remove_extension s);
      Dom.appendChild files o
    );

  send##.onclick :=
    Html.handler
      (fun _ ->
         do_send ();
         Js.bool true
      );
  clear##.onclick :=
    Html.handler
      (fun _ ->
         input##.value := Js.string "";
         highlight ();
         output##.value := Js.string "";
         Js.bool true
      );
  files##.onchange :=
    Html.handler
      (fun _ ->
         let fname = Filename.concat "stdlib" @@ Js.to_string files##.value in
         let s =
           In_channel.with_open_bin fname (fun ic ->
               really_input_string ic (in_channel_length ic)
             )
         in
         input##.value := Js.string s;
         highlight ();
         do_send ();
         Js.bool true
      );

  input##focus;

  ignore (Js.Unsafe.eval_string "init();");

  Js._false

let () =
  Html.window##.onload := Html.handler run
