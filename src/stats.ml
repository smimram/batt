(** Statistics about a run, displayed at the end. *)

(** Wall-clock time at startup. *)
let start = Unix.gettimeofday ()

(** Number of declarations checked. *)
let declarations = ref 0

(** Number of modules checked. *)
let modules_checked = ref 0

(** Number of modules loaded from the cache. *)
let modules_loaded = ref 0

(** Number of unifications requested by the type checker. *)
let unifications = ref 0

(** Number of unification problems deferred. *)
let deferred = ref 0

(** Maximal number of unification problems deferred at the same time. *)
let max_deferred = ref 0

(** Number of tentative unifications which were undone. *)
let backtracks = ref 0

(** Display the statistics. *)
let print ~metas ~solved ~globals =
  let gc = Gc.stat () in
  let mb words = float_of_int (words * (Sys.word_size / 8)) /. 1048576. in
  let p fmt = Common.print fmt in
  p "\nStatistics:\n";
  p "  time         : %.2fs (%.2fs CPU)\n" (Unix.gettimeofday () -. start) (Sys.time ());
  p "  declarations : %d\n" !declarations;
  p "  modules      : %d checked, %d loaded from cache\n" !modules_checked !modules_loaded;
  p "  definitions  : %d global\n" globals;
  p "  metavariables: %d created, %d solved\n" metas solved;
  p "  unifications : %d, %d problems deferred (at most %d at once), %d backtracks\n" !unifications !deferred !max_deferred !backtracks;
  p "  memory       : %.1f MB peak heap, %.1f MB allocated\n" (mb gc.top_heap_words) (mb (int_of_float (gc.minor_words +. gc.major_words -. gc.promoted_words)));
  p "  GC           : %d minor, %d major collections\n%!" gc.minor_collections gc.major_collections
