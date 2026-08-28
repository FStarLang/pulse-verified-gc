(* Regression test: caml_minor_collection() must really collect.
   ==============================================================

   Several C primitives in the OCaml runtime establish the invariant "the
   value I am holding is no longer in the minor heap" by calling
   [caml_minor_collection ()], and then rely on that invariant to store the
   value WITHOUT a write barrier.  caml_make_vect (runtime/array.c) is the
   sharpest example:

       if (Is_block(init) && Is_young(init)) caml_minor_collection ();
       CAMLassert(!(Is_block(init) && Is_young(init)));
       res = caml_alloc_shr(size, 0);
       // "We now know that [init] is not in the minor heap, so there is
       //  no need to call [caml_initialize]."
       for (i = 0; i < size; i++) Field(res, i) = init;

   The verified runtime used to stub [caml_minor_collection] out to an empty
   body ("Disabled: we use our own verified GC").  With an empty body [init]
   stays young, the CAMLassert is compiled out of a release build, and those
   `size` raw stores create major->minor pointers recorded in neither the
   ref_table nor any root set.  The next minor collection then promotes the
   target without updating them, leaving every slot dangling.

   Every case below is ordinary OCaml -- no Obj, no Bytes, no unsafe feature.
   Under the stubbed runtime the first three sections report corruption and
   this program exits 1.  Both runtimes must now agree that nothing is
   damaged.

   The trigger is `Array.make n x` / `Array.init n f` with n > 256
   (Max_young_wosize), which is what forces the container into the major
   heap and takes the caml_make_vect path above. *)

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  if not ok then begin
    incr failures;
    Printf.printf "  FAIL  %s\n%!" name
  end

(* Force [k] minor collections by allocating short-lived garbage.
   [Gc.minor] is not wired to the verified collector, so collections are
   driven the way a real program drives them: by allocating. *)
let churn_minors k =
  let m0 = (Gc.quick_stat ()).Gc.minor_collections in
  let spins = ref 0 in
  while (Gc.quick_stat ()).Gc.minor_collections < m0 + k
        && !spins < 5_000_000 do
    ignore (Sys.opaque_identity (Array.make 24 0));
    incr spins
  done;
  check (Printf.sprintf "forced %d minor collection(s)" k)
    ((Gc.quick_stat ()).Gc.minor_collections >= m0 + k)

let intact (a : int array) n v =
  match Array.length a with
  | l -> l = n && a.(n - 1) = v
  | exception _ -> false

(* 1. The minimal case: one young value, one large (major) container. *)
let test_make_vect_young_init () =
  print_endline "1. Array.make <big> <young value>";
  let y = Array.make 4 7 in            (* young *)
  let outer = Array.make 300 y in      (* major container, unbarriered stores *)
  churn_minors 3;
  let bad = ref 0 in
  for i = 0 to 299 do
    if not (intact outer.(i) 4 7) then incr bad
  done;
  check "all 300 slots still reach the (promoted) init value" (!bad = 0);
  if !bad > 0 then Printf.printf "    %d of 300 slots dangling\n%!" !bad;
  ignore (Sys.opaque_identity outer)

(* 2. Array.init crossing the Max_young_wosize boundary.  256 goes to the
      minor heap and was always fine; 257 takes the caml_make_vect path. *)
let test_array_init_boundary () =
  print_endline "2. Array.init across the Max_young_wosize (256) boundary";
  List.iter
    (fun n ->
      let keep = Array.init n (fun i -> Array.make 4 i) in
      churn_minors 2;
      let bad = ref 0 in
      for i = 0 to n - 1 do
        if not (intact keep.(i) 4 i) then incr bad
      done;
      check (Printf.sprintf "Array.init %d: every element intact" n) (!bad = 0);
      if !bad > 0 then Printf.printf "    n=%d: %d of %d dangling\n%!" n !bad n;
      ignore (Sys.opaque_identity keep))
    [ 200; 256; 257; 300; 800 ]

(* 3. Repeated heavy promotion: the shape that first exposed the bug. *)
let test_repeated_promotion () =
  print_endline "3. repeated promotion of a large young live set";
  let iterations = 10 and n = 300 in
  let total_bad = ref 0 in
  for _ = 1 to iterations do
    let anchors = Array.init n (fun i -> Array.make 8 i) in
    let payloads = Array.init n (fun i -> Array.make 256 i) in
    let bad = ref 0 in
    for i = 0 to n - 1 do
      if not (intact anchors.(i) 8 i) then incr bad
    done;
    total_bad := !total_bad + !bad;
    ignore (Sys.opaque_identity payloads);
    ignore (Sys.opaque_identity anchors)
  done;
  check
    (Printf.sprintf "%d iterations x %d anchors survive promotion"
       iterations n)
    (!total_bad = 0);
  if !total_bad > 0 then
    Printf.printf "    %d anchor corruptions\n%!" !total_bad

(* 4. The other callers of caml_minor_collection use the same contract.
      `0L` is a young custom block, so `Array.make 300 0L` takes exactly the
      caml_make_vect path above with a custom-tagged init value. *)
let test_other_barrier_callers () =
  print_endline "4. large container of boxed (custom-block) values";
  let boxes = Array.make 300 0L in     (* 0L is a young custom block *)
  churn_minors 2;
  check "boxed Int64 container intact"
    (try Array.for_all (fun v -> Int64.equal v 0L) boxes with _ -> false);
  let nboxes = Array.make 300 0n in    (* nativeint: also a custom block *)
  churn_minors 2;
  check "boxed nativeint container intact"
    (try Array.for_all (fun v -> Nativeint.equal v 0n) nboxes with _ -> false);
  ignore (Sys.opaque_identity (boxes, nboxes))

let () =
  (* Compaction would move blocks under us; turn it off so the test means
     the same thing under both runtimes. *)
  (try Gc.set { (Gc.get ()) with Gc.max_overhead = 1_000_000 } with _ -> ());
  print_endline "=== caml_minor_collection write-barrier contract ===";
  test_make_vect_young_init ();
  test_array_init_boundary ();
  test_repeated_promotion ();
  test_other_barrier_callers ();
  let st = Gc.quick_stat () in
  Printf.printf "collections observed: %d minor, %d major\n%!"
    st.Gc.minor_collections st.Gc.major_collections;
  if !failures = 0 then
    Printf.printf "=== make_vect_barrier: %d checks passed ===\n%!" !checks
  else begin
    Printf.printf "=== make_vect_barrier: %d of %d checks FAILED ===\n%!"
      !failures !checks;
    exit 1
  end
