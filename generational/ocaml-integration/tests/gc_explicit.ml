(* Gc.major, Gc.full_major and Gc.compact under the verified collector.
   ====================================================================

   Stock OCaml implements these with its own incremental major collector and
   compactor, which must not run once the verified collector owns the heap.
   The verified runtime runs one stop-the-world verified collection of both
   generations instead (verified_do_full_gc).

   Checked under both runtimes:
   - a data structure spread over both generations survives every call,
     with every value intact;
   - the counters move as the stock documentation says: each call completes
     at least one major collection; Gc.full_major and Gc.compact are forced
     major collections and Gc.major is not;
   - minor_words is not counted twice.  The words allocated in the nursery
     before a full collection must be counted once, by that collection, and
     not again by the next minor collection.  (Native code keeps the nursery
     fill level in young_ptr, which the full collection must reset.)

   Checked only with GC_EXPLICIT_RUNTIME=verified: each call is exactly one
   major collection (stock's full_major and compact run two cycles), and
   Gc.compact does not count a compaction (the verified heap is non-moving).

   Exits 1 if any check fails. *)

let failures = ref 0

let check name ok =
  if not ok then begin
    incr failures;
    Printf.printf "  FAIL  %s\n%!" name
  end

let verified = Sys.getenv_opt "GC_EXPLICIT_RUNTIME" = Some "verified"

(* Live data in both generations: an old table and young lists hanging off it
   (major -> minor pointers), plus a young structure held only by a local. *)
let old_table = Array.make 1000 [] (* > Max_young_wosize: major heap *)

let fill round =
  for i = 0 to Array.length old_table - 1 do
    old_table.(i) <- [ i; round; i + round ]
  done

let check_table round =
  let ok = ref true in
  Array.iteri
    (fun i l -> if l <> [ i; round; i + round ] then ok := false)
    old_table;
  !ok

let young_list n = List.init n (fun i -> (i, string_of_int i))

let check_young l n =
  List.length l = n
  && List.for_all (fun (i, s) -> s = string_of_int i) l
  && fst (List.nth l (n - 1)) = n - 1

let run name f ~forced =
  let round = Hashtbl.hash name land 0xffff in
  fill round;
  let local = young_list 500 in
  let s0 = Gc.quick_stat () in
  f ();
  let s1 = Gc.quick_stat () in
  check (name ^ ": old table intact") (check_table round);
  check (name ^ ": young local intact") (check_young local 500);
  let majors = s1.Gc.major_collections - s0.Gc.major_collections in
  let forced_d =
    s1.Gc.forced_major_collections - s0.Gc.forced_major_collections
  in
  check (name ^ ": completed a major collection") (majors >= 1);
  check
    (Printf.sprintf "%s: forced_major_collections +%d (want +%d)" name
       forced_d forced)
    (forced_d = forced);
  if verified then begin
    check (Printf.sprintf "%s: exactly one major collection (got %d)" name majors)
      (majors = 1);
    check (name ^ ": no compaction counted")
      (s1.Gc.compactions = s0.Gc.compactions)
  end

(* Words allocated in the nursery just before a full collection must be
   counted once.  Allocate ~[n] words, collect fully, then run a minor
   collection: minor_words must grow by about [n], not [2n]. *)
let minor_words_once name f =
  Gc.minor ();
  let m0 = Gc.minor_words () in
  let n = 30_000 in
  let keep = young_list (n / 9) in   (* (i, s) :: _, string: ~9 words each *)
  f ();
  Gc.minor ();
  let grew = Gc.minor_words () -. m0 in
  check (name ^ ": kept list intact") (check_young keep (n / 9));
  check
    (Printf.sprintf "%s: minor_words grew by %.0f for ~%d words allocated"
       name grew n)
    (grew > 0.5 *. float n && grew < 1.5 *. float n)

let () =
  run "Gc.major" Gc.major ~forced:0;
  run "Gc.full_major" Gc.full_major ~forced:1;
  run "Gc.compact" Gc.compact ~forced:1;
  minor_words_once "Gc.full_major" Gc.full_major;
  minor_words_once "Gc.major" Gc.major;
  minor_words_once "Gc.compact" Gc.compact;
  if !failures = 0 then print_endline "gc_explicit: all checks passed"
  else begin
    Printf.printf "gc_explicit: %d check(s) failed\n" !failures;
    exit 1
  end
