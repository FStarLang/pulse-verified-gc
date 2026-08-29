(* Regression test: no-scan blocks in the nursery must not be scanned.
   ==================================================================

   A block whose tag is >= no_scan_tag (251) -- string/Bytes, Int64/Int32/
   nativeint boxes, Bigarray, flat float arrays, and custom blocks -- holds
   raw bytes, not fields.  The collector must never interpret its contents as
   pointers, because those bytes are ordinary program data and can hold any
   bit pattern at all, including things that look exactly like heap addresses.

   The major heap has always got this right.  In the extracted collector
   (generational/snapshot/GC_Gen_Impl.c) both major-heap passes are guarded:

       update_all_objects : if (tag >= no_scan_tag) { ...skip body... }
       mark_and_push      : if (!(tag >= no_scan_tag)) push_children_...

   The nursery used to not be.  `scan_loop` read the header, took `wosize`,
   and walked every field with no tag test whatsoever, so every word of a
   young `Bytes.t` was a candidate pointer during a minor collection.  Worse,
   that loop contains the infix-aware path: a word that is 8-aligned and lands
   inside the nursery is looked up in the forwarding array, and if the block it
   points at carries tag 249 the collector reads a *synthetic* infix header and
   walks backwards to a "parent closure".  Applied to arbitrary bytes that
   promotes nonsense, and the run dies with "promotion failed -- major heap
   full".  That message is a misnomer: the heap is nearly empty and no
   allocation fails.  The forged word makes the scan read field 0 of an anchor
   as a header; that word is the immediate 2i+1, whose tag byte is 249 for
   i in {124, 252, 380}, and whose wosize is (2i+1) >> 10 == 0.  The infix walk
   therefore computes parent = child - 0 == child and the promoter takes its
   defensive "cannot promote a zero-word object" branch, which sets the same
   `oom` flag a genuine exhaustion would.

   The gap was masked in the proof by a precondition: `gen_gc` required
   `GC.Gen.Promote.minor_no_scan_invariant`, which simply *assumed* that no
   field of a young no-scan block ever looks like a pointer.  Under that
   hypothesis the missing guard is provably redundant -- and the hypothesis is
   routinely false for real OCaml programs, and the C boundary never checks it.

   The fix makes the nursery scan window
   `GC.Gen.MinorHeap.minor_scan_wosize` (0 for tag >= 251) everywhere the
   collector *reads* a young body, exactly mirroring
   `GC.Gen.CombinedGraph.major_object_edges`.  The precondition is gone.

   What this program does
   ----------------------
   It writes, into small (nursery-resident) Bytes values, a word-aligned
   address that points into the *interior* of another young block -- exactly
   the bit pattern that a length-prefixed binary format or a serialized
   pointer-like value produces by accident.  Nothing here is unsafe from
   OCaml's point of view: Bytes contents are ordinary data.

   Expected: identical behaviour under stock OCaml and the verified
   collector, with every payload byte and every anchor intact. *)

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
    (* Every payload word must still read back identically (the addresses
       themselves move, so we compare the three copies against each other),
       and the anchor the forged pointer aimed at must be intact. *)
    if Bytes.length b <> 48
       || Bytes.get_int64_ne b 0 <> Bytes.get_int64_ne b 8
       || Bytes.get_int64_ne b 0 <> Bytes.get_int64_ne b 40
       || Array.length anchors.(i) <> 4
       || anchors.(i).(0) <> i || anchors.(i).(3) <> i
    then incr bad
  done;
  ignore (Sys.opaque_identity (keep, anchors));
  Printf.printf "survived (%d/%d payloads damaged)\n%!" !bad n;
  !bad

let () =
  (try Gc.set { (Gc.get ()) with Gc.max_overhead = 1_000_000 } with _ -> ());
  print_endline "=== nursery no-scan blocks are not scanned ===";
  let bad = ref 0 in
  bad := !bad + run "odd" 400;
  bad := !bad + run "plain" 400;
  bad := !bad + run "interior" 400;
  if !bad = 0 then
    print_endline "=== nursery_no_scan_interior: PASS (no damage observed) ==="
  else begin
    Printf.printf "=== nursery_no_scan_interior: %d damaged payloads ===\n%!"
      !bad;
    exit 1
  end
