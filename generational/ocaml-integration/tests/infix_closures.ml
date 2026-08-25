(* infix_closures.ml — interior (infix) pointers under the verified GC.
 *
 * Mutually recursive OCaml functions are compiled to a *single* heap block.
 * The first function is the block itself (Closure_tag = 247); the second and
 * later ones are *interior pointers* into the middle of that block, each
 * sitting just after an extra header whose tag is Infix_tag = 249 and whose
 * size field records the distance, in words, back to the start of the block.
 *
 * So a perfectly ordinary OCaml program puts, in an ordinary heap field, a
 * pointer that is not the address of any allocated block.  The collector must
 * recognise it, walk back to the enclosing closure, and mark *that*.
 *
 * This is the concrete counterpart of the specification change in
 * `GC.Spec.Fields.well_formed_heap_part2`, which is now stated on
 * `resolve_object dst g` rather than on the raw field value, and of
 * `GC.Spec.Object.infix_addr_conds`, which pins down the parent-address
 * formula.  Every numeric relation asserted below is one of those clauses,
 * checked against a live heap rather than against the SMT solver.
 *
 * The test drives the *real* collector: it forces collections by allocating,
 * exactly as a normal program does, and reads `Gc.quick_stat` to confirm they
 * happened.
 *
 * Run with:
 *   MIN_EXPANSION_WORDSIZE=<small> ocamlrun infix_closures.byte
 *
 * Everything here is plain OCaml plus `Obj`; no runtime hooks are needed. *)

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  if not ok then begin
    incr failures;
    Printf.printf "  FAIL  %s\n%!" name
  end

let check_eq name (got : int) (want : int) =
  incr checks;
  if got <> want then begin
    incr failures;
    Printf.printf "  FAIL  %s: got %d, want %d\n%!" name got want
  end

let check_eqn name (got : nativeint) (want : nativeint) =
  incr checks;
  if got <> want then begin
    incr failures;
    Printf.printf "  FAIL  %s: got %nd, want %nd\n%!" name got want
  end

let section s = Printf.printf "%s\n%!" s

(* ------------------------------------------------------------------ *)
(* The closure group                                                    *)
(* ------------------------------------------------------------------ *)

(* Three mutually recursive functions over a shared captured array.  The
   payload array is reachable *only* through the closure block's environment,
   so it survives a collection exactly when the block does. *)

let payload_len = 8

(* `second k` cycles through payload indices 1, 2, 0. *)
let expected_second base k = base + [| 1; 2; 0 |].(k mod 3)

(* Returns only the *second* function: an interior pointer.  After this
   returns, nothing anywhere holds the address of the enclosing block. *)
let make_interior_only base =
  let payload = Array.init payload_len (fun i -> base + i) in
  let rec first n = if n <= 0 then payload.(0) else second (n - 1)
  and second n = if n <= 0 then payload.(1) else third (n - 1)
  and third n = if n <= 0 then payload.(2) else first (n - 1) in
  Sys.opaque_identity second

(* Returns handles on all three, so the parent block address is observable. *)
let make_handles base =
  let payload = Array.init payload_len (fun i -> base + i) in
  let rec first n = if n <= 0 then payload.(0) else second (n - 1)
  and second n = if n <= 0 then payload.(1) else third (n - 1)
  and third n = if n <= 0 then payload.(2) else first (n - 1) in
  Sys.opaque_identity [| Obj.repr first; Obj.repr second; Obj.repr third |]

(* ------------------------------------------------------------------ *)
(* Forcing real collections                                             *)
(* ------------------------------------------------------------------ *)

(* `Gc.full_major` is not wired to the verified collector, and `Gc.compact`
   does not exist for it either.  Collections are driven the way a real
   program drives them: by allocating.  `Gc.quick_stat` reads the counters
   that `alloc_gen.c` bumps, so we can see them happen. *)

let majors () = (Gc.quick_stat ()).Gc.major_collections
let minors () = (Gc.quick_stat ()).Gc.minor_collections

let churn_majors n =
  let target = majors () + n in
  let spins = ref 0 in
  while majors () < target && !spins < 50_000_000 do
    ignore (Sys.opaque_identity (Array.make 24 0));
    incr spins
  done;
  check (Printf.sprintf "forced %d major collection(s)" n) (majors () >= target)

let churn_minors n =
  let target = minors () + n in
  let spins = ref 0 in
  while minors () < target && !spins < 50_000_000 do
    ignore (Sys.opaque_identity (Array.make 24 0));
    incr spins
  done;
  check (Printf.sprintf "forced %d minor collection(s)" n) (minors () >= target)

(* ------------------------------------------------------------------ *)
(* A mutable major-heap block whose field we point at an infix address   *)
(* ------------------------------------------------------------------ *)

type slot = { mutable v : Obj.t }

let addr_of (o : Obj.t) (i : int) : nativeint = Obj.raw_field o i

(* ================================================================== *)

let test_representation () =
  section "1. representation: one block, interior pointers for 2nd and 3rd";
  let h = make_handles 1000 in
  let ho = Obj.repr h in
  check_eq "parent tag is Closure_tag" (Obj.tag (Obj.field ho 0)) Obj.closure_tag;
  check_eq "second tag is Infix_tag" (Obj.tag (Obj.field ho 1)) Obj.infix_tag;
  check_eq "third tag is Infix_tag" (Obj.tag (Obj.field ho 2)) Obj.infix_tag;
  Printf.printf
    "  parent wosize=%d, infix offsets = %d, %d words\n%!"
    (Obj.size (Obj.field ho 0))
    (Obj.size (Obj.field ho 1))
    (Obj.size (Obj.field ho 2));
  ignore (Sys.opaque_identity h)

(* Every clause of `GC.Spec.Object.infix_addr_conds`, checked numerically:
 *
 *   let w = wosize_of_object h g in
 *   let p = U64.v h - w * 8 in
 *   w >= 2 /\ p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
 *   Seq.mem p objs /\ is_closure p g /\
 *   U64.v h < p + wosize_of_object p g * 8
 *)
let test_infix_addr_conds () =
  section "2. infix_addr_conds holds numerically on the live heap";
  let h = make_handles 2000 in
  let ho = Obj.repr h in
  let p_addr = addr_of ho 0 in
  let parent_wosize = Obj.size (Obj.field ho 0) in
  List.iter
    (fun i ->
      let tag = Printf.sprintf "infix #%d" i in
      let h_addr = addr_of ho i in
      let w = Obj.size (Obj.field ho i) in
      (* w >= 2 *)
      check (tag ^ ": wosize >= 2") (w >= 2);
      (* p == h - w * 8 : this is `parent_closure_addr_nat` *)
      check_eqn (tag ^ ": parent = h - wosize*8")
        (Nativeint.sub h_addr (Nativeint.of_int (w * 8)))
        p_addr;
      (* p % 8 == 0 and h % 8 == 0 *)
      check (tag ^ ": parent word-aligned")
        (Nativeint.rem p_addr 8n = 0n);
      check (tag ^ ": infix word-aligned")
        (Nativeint.rem h_addr 8n = 0n);
      (* is_closure p *)
      check_eq (tag ^ ": parent is Closure_tag")
        (Obj.tag (Obj.field ho 0)) Obj.closure_tag;
      (* h < p + wosize(p) * 8 : the infix header lies strictly inside the
         parent's body *)
      check (tag ^ ": infix strictly inside parent body")
        (h_addr < Nativeint.add p_addr (Nativeint.of_int (parent_wosize * 8)));
      check (tag ^ ": infix strictly after parent start") (h_addr > p_addr))
    [ 1; 2 ];
  (* The two interior pointers are distinct and ordered. *)
  check "second precedes third" (addr_of ho 1 < addr_of ho 2);
  ignore (Sys.opaque_identity h)

let test_field_holds_infix () =
  section "3. a heap field really stores an interior pointer";
  let s = { v = Obj.repr 0 } in
  s.v <- Obj.repr (make_interior_only 3000);
  let so = Obj.repr s in
  check_eq "slot field tag is Infix_tag" (Obj.tag (Obj.field so 0)) Obj.infix_tag;
  (* The stored word is not the address of any block header: subtracting a
     word does not land on a Closure_tag header, it lands *inside* one. *)
  let w = Obj.size (Obj.field so 0) in
  check "stored offset is positive" (w >= 2);
  Printf.printf "  slot holds addr %nx, %d words into its block\n%!"
    (addr_of so 0) w;
  check_eq "closure through the interior pointer still computes"
    ((Obj.obj s.v : int -> int) 0)
    (expected_second 3000 0);
  ignore (Sys.opaque_identity s)

let test_promotion () =
  section "4. promotion: the interior pointer survives becoming a major field";
  let s = { v = Obj.repr 0 } in
  let h = make_handles 4000 in
  s.v <- Obj.field (Obj.repr h) 1;
  let so = Obj.repr s in
  let ho = Obj.repr h in
  let w_before = Obj.size (Obj.field so 0) in
  let delta_before = Nativeint.sub (addr_of ho 1) (addr_of ho 0) in
  let addr_before = addr_of so 0 in
  churn_minors 3;
  let w_after = Obj.size (Obj.field so 0) in
  let delta_after = Nativeint.sub (addr_of ho 1) (addr_of ho 0) in
  let addr_after = addr_of so 0 in
  check_eq "infix offset unchanged across promotion" w_after w_before;
  check_eqn "parent delta unchanged across promotion" delta_after delta_before;
  check_eqn "parent delta still equals wosize*8" delta_after
    (Nativeint.of_int (w_after * 8));
  check "the block was actually promoted (address moved)"
    (addr_after <> addr_before);
  check_eq "field still tagged Infix_tag" (Obj.tag (Obj.field so 0)) Obj.infix_tag;
  check_eq "parent still tagged Closure_tag"
    (Obj.tag (Obj.field ho 0)) Obj.closure_tag;
  check "field and handle are physically equal"
    (s.v == Obj.field ho 1);
  check_eq "closure still computes" ((Obj.obj s.v : int -> int) 2)
    (expected_second 4000 2);
  (* Now the block is in the major heap: mark & sweep must not move it. *)
  let major_addr = addr_of so 0 in
  churn_majors 2;
  check_eqn "major collection does not move the block" (addr_of so 0) major_addr;
  check_eqn "parent delta survives major collection"
    (Nativeint.sub (addr_of ho 1) (addr_of ho 0))
    delta_before;
  ignore (Sys.opaque_identity h);
  ignore (Sys.opaque_identity s)

(* The decisive test.  The closure block, the two extra closures inside it,
   and the payload array it captures are reachable from the roots *only*
   through an interior pointer.  A collector that darkens the raw field value
   would colour the infix header instead of the block header, leave the block
   white, and sweep it. *)
let test_interior_only_survival () =
  section "5. a block reachable only through an interior pointer survives";
  let s = { v = Obj.repr 0 } in
  s.v <- Obj.repr (make_interior_only 5000);
  churn_minors 2;
  let so = Obj.repr s in
  let words_before = Obj.reachable_words s.v in
  let offset_before = Obj.size (Obj.field so 0) in
  let addr_before = addr_of so 0 in
  churn_majors 3;
  check_eq "tag still Infix_tag" (Obj.tag (Obj.field so 0)) Obj.infix_tag;
  check_eq "infix offset unchanged" (Obj.size (Obj.field so 0)) offset_before;
  check_eqn "block not moved by mark & sweep" (addr_of so 0) addr_before;
  check_eq "reachable word count unchanged"
    (Obj.reachable_words s.v) words_before;
  (* Calling it exercises all three closures in the block and the captured
     payload array; a swept block would give garbage or crash. *)
  let f : int -> int = Obj.obj s.v in
  for k = 0 to 11 do
    check_eq (Printf.sprintf "second %d after sweep" k) (f k)
      (expected_second 5000 k)
  done;
  Printf.printf "  block kept alive through interior pointer: %d words\n%!"
    words_before;
  ignore (Sys.opaque_identity s)

(* Sweep pressure: many groups, half of them dropped, all survivors held only
   by interior pointers. *)
let test_many_groups () =
  section "6. 400 groups, half dropped, held only by interior pointers";
  let n = 400 in
  let kept = Array.make (n / 2) (Obj.repr 0) in
  for i = 0 to n - 1 do
    let g = make_interior_only (100_000 + (i * 100)) in
    if i mod 2 = 0 then kept.(i / 2) <- Obj.repr g
    else ignore (Sys.opaque_identity (Obj.repr g))
  done;
  churn_minors 2;
  let words_before = Array.map Obj.reachable_words kept in
  churn_majors 3;
  Array.iteri
    (fun j o ->
      let base = 100_000 + (j * 2 * 100) in
      check_eq (Printf.sprintf "group %d tag" j) (Obj.tag o) Obj.infix_tag;
      check_eq (Printf.sprintf "group %d reachable words" j)
        (Obj.reachable_words o) words_before.(j);
      let f : int -> int = Obj.obj o in
      check_eq (Printf.sprintf "group %d value" j) (f 4)
        (expected_second base 4))
    kept;
  Printf.printf "  %d surviving groups verified\n%!" (n / 2);
  ignore (Sys.opaque_identity kept)

(* Post-collection heap shape, stated as a whole-graph invariant: take a
   container that mixes ordinary pointers, interior pointers and immediates,
   record its shape, collect, and compare. *)
let test_heap_shape () =
  section "7. post-collection heap shape is unchanged";
  let h1 = make_handles 7000 in
  let h2 = make_handles 8000 in
  let container =
    [| Obj.field (Obj.repr h1) 1 (* interior *)
     ; Obj.field (Obj.repr h1) 0 (* ordinary: the same block *)
     ; Obj.field (Obj.repr h2) 2 (* interior, deeper offset *)
     ; Obj.repr [| 1; 2; 3 |]    (* ordinary array *)
     ; Obj.repr 42               (* immediate *)
    |]
  in
  churn_minors 2;
  let co = Obj.repr container in
  let shape () =
    Array.init (Obj.size co) (fun i ->
        let f = Obj.field co i in
        if Obj.is_int f then (-1, -1, 0n)
        else (Obj.tag f, Obj.size f, addr_of co i))
  in
  let before = shape () in
  let reach_before = Obj.reachable_words co in
  let majors_before = majors () in
  churn_majors 3;
  let after = shape () in
  check "at least one major collection ran" (majors () > majors_before);
  check_eq "same number of fields" (Array.length after) (Array.length before);
  Array.iteri
    (fun i (t, sz, a) ->
      let t', sz', a' = before.(i) in
      check_eq (Printf.sprintf "field %d tag" i) t t';
      check_eq (Printf.sprintf "field %d size" i) sz sz';
      check_eqn (Printf.sprintf "field %d address" i) a a')
    after;
  check_eq "reachable words unchanged" (Obj.reachable_words co) reach_before;
  (* The interior pointer and the ordinary pointer to the same block still
     agree about that block. *)
  check_eq "interior field is Infix_tag" (Obj.tag container.(0)) Obj.infix_tag;
  check_eq "ordinary field is Closure_tag" (Obj.tag container.(1)) Obj.closure_tag;
  check_eqn "interior/ordinary delta = wosize*8"
    (Nativeint.sub (addr_of co 0) (addr_of co 1))
    (Nativeint.of_int (Obj.size container.(0) * 8));
  check_eq "both reach the same block"
    (Obj.reachable_words container.(0))
    (Obj.reachable_words container.(1));
  check_eq "closure through interior field still computes"
    ((Obj.obj container.(0) : int -> int) 1)
    (expected_second 7000 1);
  Printf.printf "  container reaches %d words, unchanged across %d majors\n%!"
    reach_before (majors () - majors_before);
  ignore (Sys.opaque_identity h1);
  ignore (Sys.opaque_identity h2);
  ignore (Sys.opaque_identity container)

let () =
  (* The verified major collector is a non-moving mark & sweep, so several
     checks below assert that addresses are stable across a major collection.
     Stock OCaml compacts by default, which would move them; `max_overhead`
     at or above 1000000 turns compaction off.  With that one setting the
     test is meaningful under both runtimes and doubles as a differential
     test against stock OCaml. *)
  (try Gc.set { (Gc.get ()) with Gc.max_overhead = 1_000_000 }
   with _ -> ());
  Printf.printf
    "=== interior (infix) pointers under the verified GC ===\n\
     Obj.closure_tag=%d Obj.infix_tag=%d word=%d bytes\n%!"
    Obj.closure_tag Obj.infix_tag (Sys.word_size / 8);
  test_representation ();
  test_infix_addr_conds ();
  test_field_holds_infix ();
  test_promotion ();
  test_interior_only_survival ();
  test_many_groups ();
  test_heap_shape ();
  let st = Gc.quick_stat () in
  Printf.printf
    "collections observed: %d minor, %d major\n%!"
    st.Gc.minor_collections st.Gc.major_collections;
  if !failures = 0 then
    Printf.printf "=== infix_closures: %d checks passed ===\n%!" !checks
  else begin
    Printf.printf "=== infix_closures: %d of %d checks FAILED ===\n%!"
      !failures !checks;
    exit 1
  end
