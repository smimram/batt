(** Separate compilation: once checked, a module [M.batt] is cached in [M.batto]. This file consists of a header in YAML format, describing what the cache depends on, terminated by the end of document marker [...], followed by the marshalled module. *)

module T = Term
module V = Value

(** Version of the format of cached files. *)
let version = "1"

(** Cached file for a source file. *)
let filename fname =
  Filename.remove_extension fname ^ ".batto"

(** Digest of a file, in hexadecimal. *)
let digest fname =
  Digest.to_hex @@ Digest.file fname

(** Digest of the running binary: marshalled data is not safe to read with another binary. *)
let binary = lazy (digest Sys.executable_name)

(** The header of a cached file. *)
type header =
  {
    source : string; (** source file *)
    digest : string; (** digest of the source *)
    dependencies : (string * string) list; (** modules we depend on (transitively, in loading order) along with the digest of their source *)
  }

(** A reference to a global definition or an opaque constant from another module. *)
type reference = [`Global | `Opaque] * V.origin

(** A cached module. In terms, identifiers of global definitions and opaque constants are indices in [references]. *)
type payload =
  {
    references : reference array; (** global definitions and opaque constants referred to *)
    opaques : int; (** number of opaque constants created by the module *)
    globals : (string * T.t) list; (** global definitions created by the module along with their value *)
    record : T.t; (** value of the module *)
    ty : (string * T.qualifier list * [`Type of T.t | `Module of string]) list; (** type of the module: fields which are modules are given by name since their types are large *)
  }

(** Elaborated term of global definitions of modules, along with the environment in which they should be evaluated. *)
let definitions : (int, T.t * V.environment) Hashtbl.t = Hashtbl.create 100

(** Register the elaborated term of a global definition. *)
let register (g:V.global) t env =
  if !Common.cache && !V.Origin.current <> "" then Hashtbl.replace definitions g.id (t, env)

(** Forget the elaborated terms of the global definitions of a module (they are only needed to save it). *)
let forget m =
  Hashtbl.filter_map_inplace (fun id d -> if fst (V.Global.get id).origin = m then None else Some d) definitions

(** Raised when a module cannot be cached. *)
exception Not_cacheable of string

let write_header oc h =
  let p fmt = Printf.fprintf oc fmt in
  p "batto: %s\n" version;
  p "batt: %s\n" (Lazy.force binary);
  p "ocaml: %s\n" Sys.ocaml_version;
  p "builtins: %b\n" !Common.builtins;
  p "source: %s\n" h.source;
  p "digest: %s\n" h.digest;
  if h.dependencies = [] then p "dependencies: []\n"
  else
    (
      p "dependencies:\n";
      List.iter (fun (m, d) -> p "  - module: %s\n    digest: %s\n" m d) h.dependencies
    );
  p "...\n"

(** Parse a header: we only handle the subset of YAML produced by [write_header]. Returns [None] if the header was produced in another setting (other binary, etc.). *)
let parse_header s =
  let key_value l =
    match String.index_opt l ':' with
    | Some i -> String.trim (String.sub l 0 i), String.trim (String.sub l (i+1) (String.length l - i - 1))
    | None -> failwith "invalid line in header"
  in
  let fields, items =
    List.fold_left
      (fun (fields, items) l ->
         if String.starts_with ~prefix:"  - " l then fields, [key_value (String.sub l 4 (String.length l - 4))] :: items
         else if String.starts_with ~prefix:"    " l then
           match items with
           | item :: items -> fields, (key_value l :: item) :: items
           | [] -> failwith "invalid line in header"
         else key_value l :: fields, items
      ) ([], []) (String.split_on_char '\n' s)
  in
  let field k = List.assoc k fields in
  if field "batto" = version && field "batt" = Lazy.force binary && field "ocaml" = Sys.ocaml_version && field "builtins" = string_of_bool !Common.builtins then
    let dependencies = List.rev_map (fun item -> List.assoc "module" item, List.assoc "digest" item) items in
    Some { source = field "source"; digest = field "digest"; dependencies }
  else None

(** Read a cached file: returns its header and its contents (which should only be used once the header has been validated). Returns [None] if the file does not exist or is not valid. *)
let read fname : (header * payload Lazy.t) option =
  try
    let s = In_channel.with_open_bin fname In_channel.input_all in
    let sep = "\n...\n" in
    let rec find i = if String.sub s i (String.length sep) = sep then i else find (i+1) in
    let i = find 0 in
    Option.map
      (fun h -> h, lazy (Marshal.from_string s (i + String.length sep) : payload))
      (parse_header (String.sub s 0 i))
  with e -> Common.debug "Could not read %s: %s\n" fname (Printexc.to_string e); None

(** Cache module [m] whose global definition is [g] and type is [ty]. The function [module_type] gives the type of the modules we depend on. *)
let save ~module_type fname h m (g:V.global) ty =
  let references = Hashtbl.create 100 in
  let reference k o =
    if fst o <> m && fst o <> "" && not (List.mem_assoc (fst o) h.dependencies) then raise (Not_cacheable "refers to a definition outside modules");
    match Hashtbl.find_opt references (k, o) with
    | Some i -> i
    | None ->
      let i = Hashtbl.length references in
      Hashtbl.add references (k, o) i;
      i
  in
  let opaque n = reference `Opaque (V.Opaque.origin n) in
  (* Rename identifiers and inline solved metavariables. *)
  let rec rename t =
    T.map
      (function
        | Global (x, id) -> Some (Global (x, reference `Global (V.Global.get id).origin))
        | Opaque (Some (`Abstract (x, n))) -> Some (Opaque (Some (`Abstract (x, opaque n))))
        | Opaque (Some (`Postulate n)) -> Some (Opaque (Some (`Postulate (opaque n))))
        | Meta (`Generated id) ->
          (
            match (V.Meta.get id).value with
            | Some v -> Some (rename (V.readback 0 v))
            | None -> raise (Not_cacheable "unsolved metavariable")
          )
        | Hole _ -> raise (Not_cacheable "hole")
        | Var _ -> raise (Not_cacheable "named variable")
        | Opaque None | Meta (`Fresh _) | Import _ | RecordDecls _ -> assert false
        | _ -> None
      ) t
  in
  (* Close the term of a global definition with respect to its environment. *)
  let export (g:V.global) =
    let t, env = Hashtbl.find definitions g.id in
    let env = Array.of_list env in
    let values = Array.map (fun (_, v) -> lazy (V.readback 0 v)) env in
    rename @@ T.subst_free (fun n -> Lazy.force values.(n)) t
  in
  let globals =
    V.Meta.Dynarray.to_list V.Global.definitions
    |> List.filter (fun (g':V.global) -> fst g'.origin = m && g'.id <> g.id)
    |> List.map (fun (g:V.global) -> g.name, export g)
  in
  let record = export g in
  let ty =
    match ty with
    | V.RecordType l ->
      List.map
        (fun (x, q, a) ->
           match List.find_opt (fun (m, _) -> module_type m == a) h.dependencies with
           | Some (m, _) -> x, q, `Module m
           | None -> x, q, `Type (rename @@ V.readback 0 a)
        ) l
    | _ -> assert false
  in
  let references =
    let a = Array.make (Hashtbl.length references) (`Global, ("", 0)) in
    Hashtbl.iter (fun r i -> a.(i) <- r) references;
    a
  in
  let payload = { references; opaques = V.Origin.count `Opaque m; globals; record; ty } in
  (* Write to a temporary file first so that the cached file is never partially written. *)
  let tmp = fname ^ ".tmp" in
  Out_channel.with_open_bin tmp (fun oc -> write_header oc h; Marshal.to_channel oc payload []);
  Sys.rename tmp fname

(** Load cached module [m] in the current session: modules it depends on should already be loaded, their type being given by [module_type]. Returns its global definition and its type. *)
let load ~module_type m (p:payload) =
  (* Make sure that the references can be resolved before modifying the state. *)
  assert (V.Origin.count `Global m = 0 && V.Origin.count `Opaque m = 0);
  Array.iter
    (fun (k, (m', i)) ->
       if m' = m then
         (
           let n = match k with `Global -> List.length p.globals + 1 | `Opaque -> p.opaques in
           if i >= n then failwith "invalid reference"
         )
       else
         try
           match k with
           | `Global -> ignore (V.Global.of_origin (m', i))
           | `Opaque -> ignore (V.Opaque.of_origin (m', i))
         with Not_found -> failwith (Printf.sprintf "unresolved reference to %s.%d" m' i)
    ) p.references;
  let import t =
    let opaque n = V.Opaque.of_origin (snd p.references.(n)) in
    T.map
      (function
        | Global (x, n) -> Some (Global (x, V.Global.of_origin (snd p.references.(n))))
        | Opaque (Some (`Abstract (x, n))) -> Some (Opaque (Some (`Abstract (x, opaque n))))
        | Opaque (Some (`Postulate n)) -> Some (Opaque (Some (`Postulate (opaque n))))
        | _ -> None
      ) t
  in
  let current = !V.Origin.current in
  V.Origin.current := m;
  Fun.protect ~finally:(fun () -> V.Origin.current := current)
    (fun () ->
       try
         for _ = 1 to p.opaques do ignore (V.Opaque.fresh ()) done;
         List.iter (fun (x, t) -> ignore @@ V.Global.fresh x (lazy (V.eval [] (import t)))) p.globals;
         let g = V.Global.fresh m (lazy (V.eval [] (import p.record))) in
         let ty = List.map (fun (x, q, a) -> x, q, match a with `Type a -> V.eval [] (import a) | `Module m -> module_type m) p.ty in
         g, V.RecordType ty
       with e ->
         (* Make sure that the origins are the expected ones when the module is checked instead. *)
         V.Origin.reset m;
         raise e
    )
