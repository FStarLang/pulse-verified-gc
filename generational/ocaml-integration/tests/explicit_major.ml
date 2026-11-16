(* Regression test: Gc.full_major & co. must not run stock's major collector.
   =========================================================================

   caml_gc_full_major, caml_gc_major, caml_gc_compaction and Gc.set's policy
   change call stock's caml_finish_major_cycle, and caml_gc_dispatch calls
   caml_major_collection_slice.  Before the fix these ran STOCK's mark and
   sweep.  The verified major heap is registered In_heap in the page table, so
   stock's mark darkened every object reachable in it, and stock's sweep --
   which walks only stock's own (empty) chunks -- never whitened them again.
   The idle heap was then full of black objects.  A white object stored into
   one of them afterwards was invisible to the next verified mark (it does not
   rescan a black object), and the verified sweep freed it while it was still
   reachable.

   The runtime patch now runs the verified collector instead
   (runtime/gc_ctrl.c and runtime/major_gc.c -> verified_do_full_gc /
   verified_major_collection_slice in verified_gc/alloc_gen.c).

   Each section calls an explicit collection, then stores fresh major
   objects into an old container, then forces verified collections by
   allocating, then checks the stored objects.  Before the fix the first
   section crashed (SIGSEGV) under the verified runtime.  Both runtimes must
   print the same report. *)

let failures = ref 0

let check name ok =
  if not ok then begin
    incr failures;
    Printf.printf "  FAIL  %s\n%!" name
  end

(* Force at least [k] major collections by allocating short-lived garbage. *)
let churn_majors k =
  let m0 = (Gc.quick_stat ()).Gc.major_collections in
  let keep = ref [] in
  let spins = ref 0 in
  while (Gc.quick_stat ()).Gc.major_collections < m0 + k && !spins < 50_000_000 do
    keep := Array.make 20 !spins :: (if !spins mod 5000 = 0 then [] else !keep);
    incr spins
  done;
  ignore (Sys.opaque_identity !keep)

let n = 2000

let section name explicit =
  let a = Array.make n [||] in                 (* n > 256: born in the major heap *)
  explicit ();
  for i = 0 to n - 1 do a.(i) <- Array.make 300 i done;   (* fresh major objects *)
  churn_majors 3;
  let ok = ref true in
  for i = 0 to n - 1 do
    let b = a.(i) in
    if Array.length b <> 300 || b.(0) <> i || b.(299) <> i then ok := false
  done;
  check name !ok;
  Printf.printf "%s: %s\n%!" name (if !ok then "intact" else "CORRUPTED")

let () =
  section "Gc.full_major" Gc.full_major;
  section "Gc.major" Gc.major;
  section "Gc.compact" Gc.compact;
  section "Gc.major_slice" (fun () -> ignore (Gc.major_slice 0));
  section "Gc.full_major twice" (fun () -> Gc.full_major (); Gc.full_major ());
  if !failures = 0 then print_endline "explicit_major: all sections intact"
  else begin
    Printf.printf "explicit_major: %d section(s) corrupted\n" !failures;
    exit 1
  end
