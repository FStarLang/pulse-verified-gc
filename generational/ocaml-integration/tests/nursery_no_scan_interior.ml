(* KNOWN GAP: no-scan blocks in the nursery are still scanned.
   =========================================================

   This program is NOT part of the `correctness` target.  It documents a
   soundness gap that is still open in the verified generational collector,
   and it is expected to FAIL (abort) under ocaml-4.14-verified-gen while
   passing under stock OCaml.  See docs/known-issues.md.

   Background
   ----------
   A block whose tag is >= no_scan_tag (251) -- string/Bytes, Int64/Int32/
   nativeint boxes, Bigarray, flat float arrays, and custom blocks -- holds
   raw bytes, not fields.  The collector must never interpret its contents as
   pointers, because those bytes are ordinary program data and can hold any
   bit pattern at all, including things that look exactly like heap addresses.

   The major heap gets this right.  In the extracted collector
   (generational/snapshot/GC_Gen_Impl.c) both major-heap passes are guarded:

       update_all_objects : if (tag >= no_scan_tag) { ...skip body... }
       mark_and_push      : if (!(tag >= no_scan_tag)) push_children_...

   The nursery does not.  `scan_loop` reads the header, takes `wosize`, and
   walks every field with no tag test whatsoever:

       uint64_t hdr    = minor_read(minor, obj - 8);
       uint64_t wosize = hdr >> 10;
       ...
       while (field_idx < wosize) { ...treat each word as a pointer... }

   So every word of a young `Bytes.t` is a candidate pointer during a minor
   collection.  Worse, that loop contains the infix-aware path: a word that
   is 8-aligned and lands inside the nursery is looked up in the forwarding
   array, and if the block it points at carries tag 249 the collector reads a
   *synthetic* infix header and walks backwards to a "parent closure".
   Applied to arbitrary bytes this promotes nonsense.

   On the specification side the matching gap is that
   GC.Gen.CombinedGraph.major_object_edges skips no-scan sources but
   minor_object_edges does not, so `gen_gc` still carries a nursery
   counterpart of the no_scan_invariant that real OCaml heaps violate.

   What this program does
   ----------------------
   It writes, into small (nursery-resident) Bytes values, a word-aligned
   address that points into the *interior* of another young block -- exactly
   the bit pattern that a length-prefixed binary format or a serialized
   pointer-like value produces by accident.  Nothing here is unsafe from
   OCaml's point of view: Bytes contents are ordinary data.

   Expected: stock OCaml is untroubled; the verified collector aborts with
   "promotion failed - major heap full" because it follows the forged
   interior pointers and promotes garbage. *)

let addr_of (o : Obj.t) (i : int) : nativeint = Obj.raw_field o i

(* The address of [o] itself, read back out of a one-element array. *)
let addr_of_value (o : Obj.t) : nativeint = addr_of (Obj.repr [| o |]) 0

let churn_minors k =
  let m0 = (Gc.quick_stat ()).Gc.minor_collections in
  let spins = ref 0 in
  while (Gc.quick_stat ()).Gc.minor_collections < m0 + k
        && !spins < 5_000_000 do
    ignore (Sys.opaque_identity (Array.make 24 0));
    incr spins
  done

(* [mode] selects the bit pattern written into the no-scan payload:
     plain    - the exact address of a live young block   (tolerated today)
     interior - that address plus one word, i.e. a pointer into the middle
                of the block                              (breaks the GC)
     odd      - the same value tagged as an OCaml immediate (never followed)
   Only the payload bytes differ; the allocation pattern is identical. *)
let run mode n =
  Printf.printf "  mode=%-9s n=%d ... %!" mode n;
  let keep = Array.make n (Obj.repr 0) in
  let anchors = Array.init n (fun i -> Array.make 4 i) in
  for i = 0 to n - 1 do
    let b = Bytes.make 48 '\000' in
    let a = Int64.of_nativeint (addr_of_value (Obj.repr anchors.(i))) in
    let v =
      match mode with
      | "plain" -> a
      | "interior" -> Int64.add a 8L
      | _ -> Int64.logor a 1L
    in
    Bytes.set_int64_ne b 0 v;
    Bytes.set_int64_ne b 8 v;
    Bytes.set_int64_ne b 40 v;
    keep.(i) <- Obj.repr b
  done;
  churn_minors 2;
  let bad = ref 0 in
  for i = 0 to n - 1 do
    let b : Bytes.t = Obj.obj keep.(i) in
    if Bytes.length b <> 48 || Bytes.get_int64_ne b 0 <> Bytes.get_int64_ne b 8
    then incr bad
  done;
  ignore (Sys.opaque_identity (keep, anchors));
  Printf.printf "survived (%d/%d payloads damaged)\n%!" !bad n;
  !bad

let () =
  (try Gc.set { (Gc.get ()) with Gc.max_overhead = 1_000_000 } with _ -> ());
  print_endline "=== KNOWN GAP: no-scan blocks in the nursery are scanned ===";
  print_endline
    "  (expected to abort under the verified GC; see docs/known-issues.md)";
  let bad = ref 0 in
  bad := !bad + run "odd" 400;
  bad := !bad + run "plain" 400;
  bad := !bad + run "interior" 400;
  if !bad = 0 then
    print_endline "=== nursery_no_scan_interior: no damage observed ==="
  else begin
    Printf.printf "=== nursery_no_scan_interior: %d damaged payloads ===\n%!"
      !bad;
    exit 1
  end
