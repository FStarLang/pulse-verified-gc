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
 * Groups 1-7 are about the major heap.  Groups 8-10 and 13 are about the nursery,
 * where the same pointer is harder: mutually recursive closures are allocated
 * young, so Cheney copying has to forward the *enclosing* block and then
 * re-apply the offset.  That is the concrete counterpart of
 * `GC.Gen.MinorCollectForwarding.Helpers.fwd_image_resolves` and of the
 * removal of the two nursery interior-pointer restrictions from
 * `GC.Gen.HeapInvariant`.
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

(* ------------------------------------------------------------------ *)
(* Nursery interior pointers                                            *)
(* ------------------------------------------------------------------ *)

(* Sections 1-7 above are about the major heap.  Sections 8 and 9 are about
 * the *minor* collector, which is where interior pointers are hardest.
 *
 * Mutually recursive closures are allocated in the nursery -- the bytecode
 * interpreter's CLOSUREREC instruction calls `caml_alloc_small` whenever the
 * group fits in `Max_young_wosize` (256 words), and the native compiler emits
 * the same young allocation.  So an interior pointer to such a group is a
 * pointer *into the middle of a young block*, and Cheney copying has to
 * forward it rather than the block it points into.  Stock OCaml does this in
 * `caml_oldify_one` (`runtime/minor_gc.c`):
 *
 *     offset = Infix_offset_hd(hd);
 *     caml_oldify_one(v - offset, p);
 *     *p += offset;
 *
 * i.e. forward the *parent*, then re-apply the offset, so the promoted field
 * is again an interior pointer at the same distance into the copy.
 *
 * That is exactly the specification `GC.Gen.MinorCollectForwarding.Helpers.
 * fwd_image_resolves` states, and `spot/GC.SPOT.MinorInfix` audits: the image
 * of an interior nursery address is an interior address of the post-collection
 * major heap resolving to the image of its parent.  The checks below are the
 * same statement against a live heap.
 *
 * Two edges are covered separately, because the collector reaches them by
 * different routes:
 *
 *   - major -> minor (section 8), which arrives through the remembered set
 *     that `caml_modify` populates.  Note `caml_modify` has no infix special
 *     case, so the raw interior word is what gets recorded -- which is why the
 *     specification keys the forwarding map on the raw address.
 *   - minor -> minor (section 9), which arrives through Cheney scanning of a
 *     young object's fields. *)

(* The address of a value, obtained by reading it back out of a container.
   (`Obj.raw_field o i` yields the raw word stored in field `i`, so putting a
   value in a one-element array and reading field 0 gives that value's
   address.) *)
let addr_of_value (o : Obj.t) : nativeint = addr_of (Obj.repr [| o |]) 0

(* Section 8: the decisive nursery test.  The closure group lives in the
   nursery and is reachable *only* through an interior pointer stored in a
   major-heap field.  A collector that forwarded the raw word would copy
   starting from the middle of the block; one that forwarded the parent but
   dropped the offset would hand back a pointer to the wrong function. *)
let test_nursery_major_to_minor () =
  section "8. major -> minor interior pointer survives a minor collection";
  (* Force `s` into the major heap, and confirm it got there: a major-heap
     block is not moved by a minor collection. *)
  let s = { v = Obj.repr 0 } in
  let holder = [| Obj.repr s |] in
  churn_minors 3;
  let s_addr = addr_of (Obj.repr holder) 0 in
  churn_minors 2;
  check "the slot is in the major heap (unmoved by a minor collection)"
    (addr_of (Obj.repr holder) 0 = s_addr);
  let so = Obj.repr s in
  (* Store an interior pointer to a brand-new (hence young) closure group.
     Nothing else holds the group: `make_interior_only` returns the second
     function only, and the result is not bound to a local. *)
  s.v <- Obj.repr (make_interior_only 9000);
  check_eq "major field holds an Infix_tag pointer"
    (Obj.tag (Obj.field so 0)) Obj.infix_tag;
  let young_addr = addr_of so 0 in
  let offset_words = Obj.size (Obj.field so 0) in
  let words_before = Obj.reachable_words s.v in
  check "interior offset is a real offset" (offset_words >= 2);
  churn_minors 1;
  let old_addr = addr_of so 0 in
  (* The target moved, so it really was in the nursery.  This is the check
     that makes the whole section about the minor collector. *)
  check "the closure group was young: the minor collection moved it"
    (old_addr <> young_addr);
  check_eq "field is still an Infix_tag pointer after promotion"
    (Obj.tag (Obj.field so 0)) Obj.infix_tag;
  check_eq "interior offset preserved across promotion (`*p += offset`)"
    (Obj.size (Obj.field so 0)) offset_words;
  check_eq "nothing was lost: reachable word count unchanged"
    (Obj.reachable_words s.v) words_before;
  (* Now it is a major-heap block, so it must not move again. *)
  churn_minors 2;
  check_eqn "promoted group is stable across later minor collections"
    (addr_of so 0) old_addr;
  churn_majors 2;
  check_eqn "promoted group is not moved by mark & sweep"
    (addr_of so 0) old_addr;
  check_eq "field still Infix_tag after mark & sweep"
    (Obj.tag (Obj.field so 0)) Obj.infix_tag;
  check_eq "interior offset still preserved"
    (Obj.size (Obj.field so 0)) offset_words;
  check_eq "reachable word count still unchanged"
    (Obj.reachable_words s.v) words_before;
  (* Calling it exercises all three closures in the group and the payload
     array captured in its environment.  If the offset had been dropped, this
     would enter the wrong function; if the block had been copied from the
     middle, it would read garbage. *)
  let f : int -> int = Obj.obj s.v in
  for k = 0 to 11 do
    check_eq (Printf.sprintf "second %d through the promoted interior pointer" k)
      (f k) (expected_second 9000 k)
  done;
  Printf.printf
    "  young %nx -> promoted %nx, %d words in, %d words reachable\n%!"
    young_addr old_addr offset_words words_before;
  ignore (Sys.opaque_identity holder);
  ignore (Sys.opaque_identity s)

(* Section 9: minor -> minor.  Both the referrer and the closure group are
   young, so the interior edge is discovered by Cheney scanning rather than by
   the remembered set, and both objects are promoted in the same pass.  Here
   the parent block is observable, so the offset relation can be checked as an
   address difference and not just as a header size. *)
let test_nursery_minor_to_minor () =
  section "9. minor -> minor interior pointer, both promoted together";
  let h = make_handles 10_000 in
  let box = { v = Obj.field (Obj.repr h) 1 } in
  let bo = Obj.repr box in
  let ho = Obj.repr h in
  check_eq "young field holds an Infix_tag pointer"
    (Obj.tag (Obj.field bo 0)) Obj.infix_tag;
  let box_before = addr_of_value bo in
  let parent_before = addr_of ho 0 in
  let target_before = addr_of bo 0 in
  let delta = Nativeint.sub target_before parent_before in
  let words_before = Obj.reachable_words bo in
  check_eqn "before: interior - parent = wosize*8" delta
    (Nativeint.of_int (Obj.size (Obj.field bo 0) * 8));
  churn_minors 1;
  let box_after = addr_of_value bo in
  let parent_after = addr_of ho 0 in
  let target_after = addr_of bo 0 in
  check "the referrer was young: it moved" (box_after <> box_before);
  check "the closure group was young: it moved" (parent_after <> parent_before);
  check_eq "field is still an Infix_tag pointer" (Obj.tag (Obj.field bo 0))
    Obj.infix_tag;
  check_eq "parent is still a Closure_tag block" (Obj.tag (Obj.field ho 0))
    Obj.closure_tag;
  check_eqn "after: interior - parent unchanged"
    (Nativeint.sub target_after parent_after) delta;
  check_eqn "after: interior - parent = wosize*8"
    (Nativeint.sub target_after parent_after)
    (Nativeint.of_int (Obj.size (Obj.field bo 0) * 8));
  (* Sharing is preserved: the field and the handle array's slot were the same
     address before, and are the same address after -- the collector forwarded
     the interior pointer consistently through two different referrers. *)
  check "field and handle still physically equal" (box.v == Obj.field ho 1);
  check_eqn "field and handle agree on the address" target_after (addr_of ho 1);
  check_eq "reachable word count unchanged" (Obj.reachable_words bo)
    words_before;
  check_eq "closure through the interior field still computes"
    ((Obj.obj box.v : int -> int) 7)
    (expected_second 10_000 7);
  (* Both are now major-heap blocks. *)
  churn_majors 2;
  check_eqn "mark & sweep does not move the promoted group"
    (addr_of ho 0) parent_after;
  check_eqn "mark & sweep does not move the promoted interior pointer"
    (addr_of bo 0) target_after;
  check_eq "closure still computes after mark & sweep"
    ((Obj.obj box.v : int -> int) 8)
    (expected_second 10_000 8);
  Printf.printf
    "  parent %nx -> %nx, interior offset %nd bytes preserved\n%!"
    parent_before parent_after delta;
  ignore (Sys.opaque_identity h);
  ignore (Sys.opaque_identity box)

(* Section 10: sweep pressure on the nursery path.  Many groups are created
   young, half of them are anchored from a major-heap array (so the edges go
   through the remembered set) and half are dropped, and every survivor is
   held only by an interior pointer. *)
let test_nursery_many_groups () =
  section "10. 200 nursery groups anchored only by interior pointers";
  let n = 400 in
  let kept = Array.make (n / 2) (Obj.repr 0) in
  (* Promote `kept` itself, so that every store into it is a major -> minor
     write that must go through the remembered set. *)
  churn_minors 3;
  let ko = Obj.repr kept in
  for i = 0 to n - 1 do
    if i mod 2 = 0 then kept.(i / 2) <- Obj.repr (make_interior_only (200_000 + (i * 100)))
    else ignore (Sys.opaque_identity (Obj.repr (make_interior_only (200_000 + (i * 100)))))
  done;
  Array.iteri
    (fun j _ -> check_eq (Printf.sprintf "group %d young tag" j)
        (Obj.tag (Obj.field ko j)) Obj.infix_tag)
    kept;
  let young = Array.init (n / 2) (fun j -> addr_of ko j) in
  let offsets = Array.init (n / 2) (fun j -> Obj.size (Obj.field ko j)) in
  let words = Array.map Obj.reachable_words kept in
  churn_minors 1;
  let moved = ref 0 in
  Array.iteri
    (fun j o ->
      let base = 200_000 + (j * 2 * 100) in
      if addr_of ko j <> young.(j) then incr moved;
      check_eq (Printf.sprintf "group %d tag after promotion" j) (Obj.tag o)
        Obj.infix_tag;
      check_eq (Printf.sprintf "group %d offset preserved" j) (Obj.size o)
        offsets.(j);
      check_eq (Printf.sprintf "group %d reachable words" j)
        (Obj.reachable_words o) words.(j);
      let f : int -> int = Obj.obj o in
      check_eq (Printf.sprintf "group %d value" j) (f 4) (expected_second base 4))
    kept;
  check "every group was promoted out of the nursery" (!moved = n / 2);
  churn_majors 3;
  Array.iteri
    (fun j o ->
      let base = 200_000 + (j * 2 * 100) in
      check_eq (Printf.sprintf "group %d survives mark & sweep" j) (Obj.tag o)
        Obj.infix_tag;
      let f : int -> int = Obj.obj o in
      check_eq (Printf.sprintf "group %d value after sweep" j) (f 9)
        (expected_second base 9))
    kept;
  Printf.printf "  %d nursery groups promoted and verified\n%!" (n / 2);
  ignore (Sys.opaque_identity kept)

(* ------------------------------------------------------------------ *)
(* 11. an interior pointer held only in a *root*                        *)
(* ------------------------------------------------------------------ *)
(* Groups 3-10 keep the interior pointer in a heap field.  A root is the
   other place OCaml puts one, and it is the harder case for the collector:
   a root cannot simply be replaced by its enclosing closure, because the
   mutator goes on calling through it, so the *offset* has to survive the
   collection.  The nursery collector therefore forwards the enclosing block
   and re-applies the delta in place, and the major collector resolves the
   root before greying it.

   Here the closure block is referenced by nothing whatsoever except the
   local variable `f`.  The bytecode runtime scans that stack slot verbatim
   (`runtime/roots_byt.c:39`), so the only thing keeping the block alive is
   a root that is an interior pointer.

   `GC.Gen.Impl.Cheney`'s root loop dispatches to `forward_if_minor_infix`
   on Infix_tag, and `GC.Impl.MarkBounded.check_and_darken_bounded_spec`
   applies `resolve_object` to every root before darkening it, so both
   collectors handle this.  Phase H of `docs/minor-infix-support-plan.md`
   brought the specifications into line: `root_valid_for_darkening` and
   `roots_valid_for_minor_collection` now speak of the object a root *names*
   rather than of the root itself. *)

let check_group_alive what base (f : int -> int) =
  let fo = Obj.repr f in
  check_eq (what ^ ": Infix_tag") (Obj.tag fo) Obj.infix_tag;
  for k = 0 to 11 do
    check_eq (Printf.sprintf "%s: value %d" what k)
      (f k) (expected_second base k)
  done

let test_interior_root () =
  section "11. a block reachable only from an interior-pointer root";
  let base = 9000 in
  let f = make_interior_only base in
  let delta = Obj.size (Obj.repr f) in
  check "root infix offset >= 2" (delta >= 2);
  check_group_alive "before collection" base f;
  let words_before = Obj.reachable_words (Obj.repr f) in

  (* Minor collections first: the block is young and this root is its only
     reference, so Cheney must forward it through the infix header. *)
  churn_minors 3;
  check_eq "offset unchanged by promotion" (Obj.size (Obj.repr f)) delta;
  check_group_alive "after promotion" base f;
  check_eq "reachable words unchanged by promotion"
    (Obj.reachable_words (Obj.repr f)) words_before;

  (* Then major collections.  The verified major collector does not move, so
     the promoted block must now stay put. *)
  let addr_after_promotion = addr_of_value (Obj.repr f) in
  churn_majors 3;
  check_eq "offset unchanged by mark & sweep" (Obj.size (Obj.repr f)) delta;
  check_eqn "promoted block not moved by mark & sweep"
    (addr_of_value (Obj.repr f)) addr_after_promotion;
  check_group_alive "after mark & sweep" base f;
  check_eq "reachable words unchanged by mark & sweep"
    (Obj.reachable_words (Obj.repr f)) words_before;
  Printf.printf "  block kept alive by an interior-pointer root: %d words\n%!"
    words_before;
  ignore (Sys.opaque_identity (Obj.repr f))

(* Many interior roots live *simultaneously*: each frame of this recursion
   holds one, and the collections happen at the bottom, with every frame
   still on the stack.  A collector that mishandled one root out of `depth`
   would show up as a wrong value on the way back out. *)
let rec nest_interior_roots depth =
  if depth <= 0 then begin
    churn_minors 2;
    churn_majors 2;
    0
  end else begin
    let base = 20_000 + depth * 100 in
    let f = make_interior_only base in
    check_eq (Printf.sprintf "frame %d: Infix_tag" depth)
      (Obj.tag (Obj.repr f)) Obj.infix_tag;
    let n = nest_interior_roots (depth - 1) in
    (* `f` was a live stack root across both collections. *)
    check_group_alive (Printf.sprintf "frame %d" depth) base f;
    n + 1
  end

let test_many_interior_roots () =
  section "12. many interior-pointer roots live across a collection";
  let depth = 24 in
  let n = nest_interior_roots depth in
  check_eq "all frames returned" n depth;
  Printf.printf "  %d simultaneous interior-pointer roots survived\n%!" depth

(* ------------------------------------------------------------------ *)
(* 13. the nursery entry invariant, checked before the collection       *)
(* ------------------------------------------------------------------ *)
(* Groups 8-12 observe what the collector *did*.  This group observes the
   heap the collector was *handed*: it establishes, on the live heap and
   before any collection is forced, that

     (a) the closure group is in the nursery,
     (b) a *root* holds an interior pointer into it,
     (c) a *nursery field* holds an interior pointer into another young
         closure group, and
     (d) every clause of `GC.Spec.Object.infix_addr_conds` holds of both,

   which together are exactly the shape that
   `GC.Gen.HeapInvariant.collection_heap_shape` and
   `GC.Gen.MinorCollectForwarding.Helpers.roots_valid_for_minor_collection`
   now admit and previously forbade.  Then it forces exactly one minor
   collection and checks the resulting heap.

   `roots_valid_for_minor_collection`'s minor branch reads

     Promote.is_minor_pointer r ==>
       Seq.mem (resolve_minor minor r) (minor_objects minor) /\
       minor_wosize minor (resolve_minor minor r) > 0

   -- the *resolution* must be an enumerated nursery object, not the root
   itself.  Clause (b) below is a heap that satisfies that and does not
   satisfy the old form.  `spot/GC.SPOT.MajorToMinorInfix` is the machine-
   checked counterpart on a concrete symbolic heap. *)

(* Nursery residency, checked positionally rather than by guessing address
   ranges.  Objects allocated in sequence with no intervening collection are
   contiguous in the minor heap, so two sentinels bracketing an allocation
   burst enclose everything allocated between them, and the whole burst fits
   in a few hundred bytes.  A major-heap block satisfies neither property.
   The bump direction is deliberately not assumed: stock OCaml allocates the
   minor heap downwards, and the check should hold under both runtimes. *)
let nursery_span = 4096n

let nmin (a : nativeint) (b : nativeint) = if a < b then a else b
let nmax (a : nativeint) (b : nativeint) = if a < b then b else a

(* `infix_addr_conds`, as a reusable check: `h` is an interior pointer whose
   enclosing closure is `p`. *)
let check_infix_addr_conds what (h_addr : nativeint) (p_addr : nativeint)
    (h_wosize : int) (parent_tag : int) (parent_wosize : int) =
  check (what ^ ": wosize >= 2") (h_wosize >= 2);
  check_eqn (what ^ ": parent = h - wosize*8")
    (Nativeint.sub h_addr (Nativeint.of_int (h_wosize * 8))) p_addr;
  check (what ^ ": parent word-aligned") (Nativeint.rem p_addr 8n = 0n);
  check (what ^ ": infix word-aligned") (Nativeint.rem h_addr 8n = 0n);
  check_eq (what ^ ": parent is Closure_tag") parent_tag Obj.closure_tag;
  check (what ^ ": infix strictly after parent start") (h_addr > p_addr);
  check (what ^ ": infix strictly inside parent body")
    (h_addr < Nativeint.add p_addr (Nativeint.of_int (parent_wosize * 8)))

(* Everything the pre-collection audit needs, read in one burst. *)
type young_shape = {
  y_before : nativeint;   (* sentinel allocated before the groups *)
  y_after  : nativeint;   (* sentinel allocated after them *)
  y_root   : nativeint;   (* the interior-pointer root's value *)
  y_rootp  : nativeint;   (* its enclosing closure *)
  y_rootw  : int;         (* its interior offset, in words *)
  y_box    : nativeint;   (* the young referrer *)
  y_field  : nativeint;   (* the interior pointer in its field 0 *)
  y_fieldp : nativeint;
  y_fieldw : int;
}

let test_nursery_entry_invariant () =
  section "13. nursery entry invariant: an interior root and an interior \
           nursery field";
  let root_base = 31_000 and field_base = 32_000 in

  (* Build the scenario *and* read every address inside one collection-free
     window, so the positional checks below are all about a single nursery
     and a single set of addresses.  `addr_of_value` allocates, so the
     reading is part of the window too. *)
  let attempt () =
    let m0 = minors () in
    let before = Sys.opaque_identity (Array.make 4 0) in
    (* (b) the interior root: `f` is a local, i.e. a stack root, and it is an
       interior pointer.  `make_interior_only` returns the second function of
       the group, so nothing anywhere names the enclosing block. *)
    let f = make_interior_only root_base in
    (* (c) the interior nursery field: `box` is young, and its field holds an
       interior pointer into a second young closure group.  Because `box` is
       young this edge is found by Cheney scanning, not by the write
       barrier. *)
    let box = { v = Obj.repr (make_interior_only field_base) } in
    let after = Sys.opaque_identity (Array.make 4 0) in
    let fo = Obj.repr f and bo = Obj.repr box in
    let y_root = addr_of_value fo in
    let y_rootw = Obj.size fo in
    let y_field = addr_of bo 0 in
    let y_fieldw = Obj.size (Obj.field bo 0) in
    let shape = {
      y_before = addr_of_value (Obj.repr before);
      y_after  = addr_of_value (Obj.repr after);
      y_root; y_rootw;
      y_rootp  = Nativeint.sub y_root (Nativeint.of_int (y_rootw * 8));
      y_box    = addr_of_value bo;
      y_field; y_fieldw;
      y_fieldp = Nativeint.sub y_field (Nativeint.of_int (y_fieldw * 8));
    } in
    if minors () <> m0 then None else Some (f, box, before, after, shape)
  in
  let rec settle n =
    if n <= 0 then None
    else match attempt () with Some r -> Some r | None -> settle (n - 1)
  in
  match settle 100 with
  | None ->
    check "could not build the scenario without an intervening collection"
      false
  | Some (f, box, before, after, y) ->
    let fo = Obj.repr f in
    let bo = Obj.repr box in

    (* -------- (b) the root really is an interior pointer -------------- *)
    check_eq "root value is Infix_tag" (Obj.tag fo) Obj.infix_tag;
    check "root: interior offset is a real offset" (y.y_rootw >= 2);
    check "root: parent is word-aligned" (Nativeint.rem y.y_rootp 8n = 0n);
    check "root: interior address is word-aligned"
      (Nativeint.rem y.y_root 8n = 0n);
    check "root: parent lies strictly below the interior address"
      (y.y_rootp < y.y_root);

    (* -------- (c) a young field really holds an interior pointer ------ *)
    check_eq "young field value is Infix_tag" (Obj.tag (Obj.field bo 0))
      Obj.infix_tag;
    check "field: interior offset is a real offset" (y.y_fieldw >= 2);
    check "field: parent is word-aligned" (Nativeint.rem y.y_fieldp 8n = 0n);
    check "field: parent lies strictly below the interior address"
      (y.y_fieldp < y.y_field);

    (* -------- (a) everything is in the nursery, positionally ---------- *)
    let lo = nmin y.y_before y.y_after and hi = nmax y.y_before y.y_after in
    check "the allocation burst is nursery-sized"
      (Nativeint.sub hi lo < nursery_span);
    let between what a = check (Printf.sprintf "%s (%nx) is inside the burst" what a)
        (lo < a && a < hi) in
    between "root's closure block" y.y_rootp;
    between "field's closure block" y.y_fieldp;
    between "the young referrer" y.y_box;
    (* The two groups are laid out in allocation order, in whichever
       direction this runtime bumps. *)
    check "the two groups are in allocation order"
      (if y.y_after > y.y_before then y.y_rootp < y.y_fieldp
       else y.y_rootp > y.y_fieldp);

    (* -------- everything still computes before the collection --------- *)
    check_group_alive "root, before collection" root_base f;
    check_eq "field, before collection"
      ((Obj.obj box.v : int -> int) 5) (expected_second field_base 5);
    let root_words = Obj.reachable_words fo in
    let field_words = Obj.reachable_words box.v in

    Printf.printf
      "  nursery burst %nx..%nx (%nd bytes): root block %nx (+%d words), \
       field block %nx (+%d words)\n%!"
      lo hi (Nativeint.sub hi lo) y.y_rootp y.y_rootw y.y_fieldp y.y_fieldw;

    (* -------- one minor collection ------------------------------------ *)
    churn_minors 1;

    (* Everything was young, so everything moved. *)
    check "the first sentinel was young: it moved"
      (addr_of_value (Obj.repr before) <> y.y_before);
    check "the second sentinel was young: it moved"
      (addr_of_value (Obj.repr after) <> y.y_after);
    check "the interior root's block was young: it moved"
      (addr_of_value fo <> y.y_root);
    check "the interior field's block was young: it moved"
      (addr_of bo 0 <> y.y_field);
    check "the young referrer was promoted too" (addr_of_value bo <> y.y_box);

    (* -------- the promoted heap has the expected shape ----------------- *)
    let root_addr' = addr_of_value fo in
    let root_off' = Obj.size fo in
    let root_parent' =
      Nativeint.sub root_addr' (Nativeint.of_int (root_off' * 8))
    in
    check_eq "root: interior offset preserved by promotion" root_off' y.y_rootw;
    check_eq "root: still Infix_tag" (Obj.tag fo) Obj.infix_tag;
    check "root: promoted parent is word-aligned"
      (Nativeint.rem root_parent' 8n = 0n);
    check_group_alive "root, after collection" root_base f;
    check_eq "root: reachable words unchanged" (Obj.reachable_words fo)
      root_words;

    let field_addr' = addr_of bo 0 in
    let field_off' = Obj.size (Obj.field bo 0) in
    check_eq "field: interior offset preserved by promotion" field_off'
      y.y_fieldw;
    check_eq "field: still Infix_tag" (Obj.tag (Obj.field bo 0)) Obj.infix_tag;
    check_eq "field: reachable words unchanged" (Obj.reachable_words box.v)
      field_words;
    check_eq "field, after collection"
      ((Obj.obj box.v : int -> int) 6) (expected_second field_base 6);
    (* The two groups were distinct young blocks and are still distinct. *)
    check "the two promoted groups are distinct" (root_parent' <> field_addr');

    (* -------- the promoted blocks have left the nursery ---------------- *)
    let fresh = Sys.opaque_identity (Array.make 4 0) in
    let fresh_addr = addr_of_value (Obj.repr fresh) in
    let far what (a : nativeint) =
      check
        (Printf.sprintf "%s (%nx) is outside the nursery" what a)
        (Nativeint.abs (Nativeint.sub a fresh_addr) >= nursery_span)
    in
    far "promoted root block" root_parent';
    far "promoted field target" field_addr';

    (* -------- and the major collector leaves them alone ---------------- *)
    churn_majors 2;
    check_eqn "root block not moved by mark & sweep" (addr_of_value fo)
      root_addr';
    check_eqn "field target not moved by mark & sweep" (addr_of bo 0)
      field_addr';
    check_group_alive "root, after mark & sweep" root_base f;
    check_eq "field, after mark & sweep"
      ((Obj.obj box.v : int -> int) 10) (expected_second field_base 10);

    (* One last cross-check of `infix_addr_conds`, this time against a group
       whose parent handle is observable, so the parent's tag and wosize can
       be read directly rather than inferred from the offset. *)
    let h = make_handles 33_000 in
    let ho = Obj.repr h in
    churn_minors 1;
    check_infix_addr_conds "promoted handle group" (addr_of ho 1)
      (addr_of ho 0)
      (Obj.size (Obj.field ho 1))
      (Obj.tag (Obj.field ho 0))
      (Obj.size (Obj.field ho 0));
    Printf.printf
      "  after one minor collection: root block %nx, field target %nx, \
       offsets %d/%d preserved\n%!"
      root_parent' field_addr' root_off' field_off';
    ignore (Sys.opaque_identity h);
    ignore (Sys.opaque_identity before);
    ignore (Sys.opaque_identity after);
    ignore (Sys.opaque_identity fo);
    ignore (Sys.opaque_identity box)

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
  test_nursery_major_to_minor ();
  test_nursery_minor_to_minor ();
  test_nursery_many_groups ();
  test_interior_root ();
  test_many_interior_roots ();
  test_nursery_entry_invariant ();
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
