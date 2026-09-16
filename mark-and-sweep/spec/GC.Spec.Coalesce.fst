/// ---------------------------------------------------------------------------
/// GC.Spec.Coalesce - Free-object coalescing pass
/// ---------------------------------------------------------------------------
///
/// Applied after sweep to merge adjacent blue (free) blocks into larger
/// free blocks, reducing fragmentation.
///
/// Design: Spec is defined separately from sweep, preserving all existing
/// sweep proofs. A Pulse implementation can fuse sweep + coalesce into a
/// single pass, proved equivalent to (coalesce ∘ sweep).
///
/// Key invariant: coalescing only writes to blue object regions.
/// Survivor (white) objects are byte-identical before and after.
///
/// After coalescing, merged blue blocks have:
///   - Header: correct merged wosize, blue color, tag 0
///   - Field 1: free list link
///   - Fields 2+: zeroed (to maintain well_formed_heap_part2)

module GC.Spec.Coalesce

#set-options "--z3rlimit 12 --fuel 2 --ifuel 1"

open FStar.Seq

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.FreeList
module HeapGraph = GC.Spec.HeapGraph
module Alloc = GC.Spec.Allocator

/// ---------------------------------------------------------------------------
/// Post-sweep heap predicate
/// ---------------------------------------------------------------------------

/// A heap where all objects are white or blue (output of sweep)
let post_sweep (g: heap) : prop =
  well_formed_heap g /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
    is_white x g \/ is_blue x g)

/// ---------------------------------------------------------------------------
/// Flush a blue run
/// ---------------------------------------------------------------------------

/// Flush accumulated blue run: write merged header, link to free list,
/// zero garbage fields.
///
/// - run_words = 0: no pending run, no-op
/// - run_words = 1: wosize=0 block (just header, no fields) — write header
///   but don't link to free list (no room for link pointer)
/// - run_words >= 2: wosize>=1 block — write header, link field 1, zero rest
///
/// Returns (updated_heap, new_free_list_head).

let flush_blue (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : GTot (heap & U64.t)
  = if run_words = 0 then (g, fp)
    else if U64.v first_blue < U64.v mword
         || U64.v first_blue >= heap_size
         || U64.v first_blue % U64.v mword <> 0
    then (g, fp)
    else
      let fb : obj_addr = first_blue in
      let hd = hd_address fb in
      let wz = run_words - 1 in
      if wz >= pow2 54 then (g, fp)
      else begin
        FStar.Math.Lemmas.pow2_lt_compat 64 54;
        let wz_u64 : wosize = U64.uint_to_t wz in
        let hdr = makeHeader wz_u64 Blue 0UL in
        let g1 = write_word g hd hdr in
        if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
          assert (U64.v (hd_address fb) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
          let g2 = HeapGraph.set_field g1 fb 1UL fp in
          let zero_start_nat = U64.v fb + U64.v mword in
          if wz >= 2 && zero_start_nat < pow2 64 then
            let g3 = Alloc.zero_fields g2 (U64.uint_to_t zero_start_nat) (wz - 1) in
            (g3, fb)
          else
            (g2, fb)
        end
        else
          (g1, fp)
      end

/// ---------------------------------------------------------------------------
/// Coalesce pass
/// ---------------------------------------------------------------------------

/// Walk objects, merging consecutive blue runs.
///
/// g0: original post-sweep heap (used for color checks — avoids needing
///     to re-establish color properties on modified intermediate heaps)
/// g: current heap (modified by flush_blue calls)
/// first_blue: obj_addr of first blue in current run (unused when run_words=0)
/// run_words: total words accumulated in current blue run (0 = no pending run)
/// fp: free list pointer being threaded through

let rec coalesce_aux (g0: heap) (g: heap) (objs: seq obj_addr)
    (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : GTot (heap & U64.t) (decreases Seq.length objs)
  = if Seq.length objs = 0 then
      flush_blue g first_blue run_words fp
    else
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      if is_blue obj g0 then
        let ws = U64.v (wosize_of_object obj g0) in
        let new_first : U64.t = if run_words = 0 then obj else first_blue in
        coalesce_aux g0 g rest new_first (run_words + ws + 1) fp
      else begin
        // White object: flush pending blue run, then continue
        let (g', fp') = flush_blue g first_blue run_words fp in
        coalesce_aux g0 g' rest 0UL 0 fp'
      end

/// Top-level coalesce: walk all objects, build fresh free list.
let coalesce (g: heap) : GTot (heap & U64.t) =
  coalesce_aux g g (objects zero_addr g) 0UL 0 0UL
/// ---------------------------------------------------------------------------
/// Opaque heap projection — prevents Z3 from unfolding coalesce_aux in
/// postconditions of walk property proofs.  All reasoning about coalesce_heap
/// goes through the step lemmas below.
/// ---------------------------------------------------------------------------

[@@"opaque_to_smt"]
let coalesce_heap (g0 g: heap) (objs: seq obj_addr)
    (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : GTot heap
  = fst (coalesce_aux g0 g objs first_blue run_words fp)

/// Step lemma: empty case
let coalesce_heap_empty (g0 g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma (coalesce_heap g0 g Seq.empty first_blue run_words fp ==
           fst (flush_blue g first_blue run_words fp))
  = reveal_opaque (`%coalesce_heap) (coalesce_heap g0 g Seq.empty first_blue run_words fp)

/// Step lemma: blue case
let coalesce_heap_blue_step
  (g0 g: heap) (objs: seq obj_addr) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires Seq.length objs > 0 /\ is_blue (Seq.head objs) g0)
    (ensures (
      let obj = Seq.head objs in
      let ws = U64.v (wosize_of_object obj g0) in
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      coalesce_heap g0 g objs first_blue run_words fp ==
        coalesce_heap g0 g (Seq.tail objs) new_first (run_words + ws + 1) fp))
  = reveal_opaque (`%coalesce_heap) (coalesce_heap g0 g objs first_blue run_words fp);
    reveal_opaque (`%coalesce_heap)
      (coalesce_heap g0 g (Seq.tail objs)
        (if run_words = 0 then Seq.head objs else first_blue)
        (run_words + U64.v (wosize_of_object (Seq.head objs) g0) + 1) fp)

/// Step lemma: white (non-blue) case
let coalesce_heap_white_step
  (g0 g: heap) (objs: seq obj_addr) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (gf: heap) (fpf: U64.t)
  : Lemma
    (requires Seq.length objs > 0 /\ ~(is_blue (Seq.head objs) g0) /\
              gf == fst (flush_blue g first_blue run_words fp) /\
              fpf == snd (flush_blue g first_blue run_words fp))
    (ensures
      coalesce_heap g0 g objs first_blue run_words fp ==
        coalesce_heap g0 gf (Seq.tail objs) 0UL 0 fpf)
  = reveal_opaque (`%coalesce_heap) (coalesce_heap g0 g objs first_blue run_words fp);
    reveal_opaque (`%coalesce_heap) (coalesce_heap g0 gf (Seq.tail objs) 0UL 0 fpf)

/// Bridge: coalesce_heap equals fst(coalesce_aux) — for use in callers that
/// need to connect opaque coalesce_heap to transparent coalesce_aux results
#push-options "--fuel 0 --ifuel 0"
let coalesce_heap_unfold (g0 g: heap) (objs: seq obj_addr)
    (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma (coalesce_heap g0 g objs first_blue run_words fp ==
           fst (coalesce_aux g0 g objs first_blue run_words fp))
  = reveal_opaque (`%coalesce_heap) (coalesce_heap g0 g objs first_blue run_words fp)
#pop-options

/// ---------------------------------------------------------------------------
/// Object region disjointness helper
/// ---------------------------------------------------------------------------

/// Addresses within one object's region are outside any other object's region.
/// Follows from objects_separated which shows non-overlapping layout.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
val addr_in_object_outside_other
  (g: heap) (x o: obj_addr) (addr: hp_addr)
  : Lemma
    (requires
      Seq.mem x (objects zero_addr g) /\ Seq.mem o (objects zero_addr g) /\
      is_white x g /\ is_blue o g /\
      U64.v addr >= U64.v (hd_address x) /\
      U64.v addr < U64.v (hd_address x) + (U64.v (wosize_of_object x g) + 1) * U64.v mword)
    (ensures
      U64.v addr + U64.v mword <= U64.v (hd_address o) \/
      U64.v addr >= U64.v (hd_address o) + (U64.v (wosize_of_object o g) + 1) * U64.v mword)

let addr_in_object_outside_other g x o addr =
  hd_address_spec x;
  hd_address_spec o;
  wosize_of_object_spec x g;
  wosize_of_object_spec o g;
  wosize_of_object_bound x g;
  wosize_of_object_bound o g;
  let wz_x = wosize_of_object x g in
  let wz_o = wosize_of_object o g in
  // x is white and o is blue → different colors → x ≠ o
  is_white_iff x g;
  is_blue_iff o g;
  assert (color_of_object x g = White);
  assert (color_of_object o g = Blue);
  assert (x <> o);
  if U64.v x < U64.v o then begin
    objects_separated zero_addr g x o;
    // objects_separated gives: o > x + wosize_of_object_as_wosize(x,g) * 8
    assert (U64.v o > U64.v x + (U64.v wz_x * 8));
    // hd_address(o) = o - 8, hd_address(x) = x - 8
    // addr < hd(x) + (wz_x + 1) * 8 = x - 8 + (wz_x + 1) * 8 = x + wz_x * 8
    // o > x + wz_x * 8 → hd(o) = o - 8 >= x + wz_x * 8 = hd(x) + (wz_x + 1) * 8 > addr
    assert (U64.v addr < U64.v x + (U64.v wz_x * 8));
    assert (U64.v (hd_address o) >= U64.v x + (U64.v wz_x * 8));
    assert (U64.v addr + U64.v mword <= U64.v (hd_address o))
  end else begin
    assert (U64.v x > U64.v o);
    objects_separated zero_addr g o x;
    // x > o + wosize_of_object_as_wosize(o,g) * 8
    assert (U64.v x > U64.v o + (U64.v wz_o * 8));
    // hd(x) = x - 8 >= o + wz_o * 8 = hd(o) + (wz_o + 1) * 8
    // addr >= hd(x) ≥ hd(o) + (wz_o + 1) * 8
    assert (U64.v (hd_address x) >= U64.v o + (U64.v wz_o * 8));
    assert (U64.v addr >= U64.v (hd_address o) + (U64.v wz_o + 1) * U64.v mword)
  end
#pop-options

/// For a white object x, any address in x's region is outside all blue objects' regions
val white_addr_outside_all_blue (g: heap) (x: obj_addr) (addr: hp_addr)
  : Lemma
    (requires
      Seq.mem x (objects zero_addr g) /\ is_white x g /\
      U64.v addr >= U64.v (hd_address x) /\
      U64.v addr < U64.v (hd_address x) + (U64.v (wosize_of_object x g) + 1) * U64.v mword)
    (ensures
      forall (o: obj_addr). Seq.mem o (objects zero_addr g) /\ is_blue o g ==>
        (U64.v addr + U64.v mword <= U64.v (hd_address o) \/
         U64.v addr >= U64.v (hd_address o) + (U64.v (wosize_of_object o g) + 1) * U64.v mword))

let white_addr_outside_all_blue g x addr =
  let aux (o: obj_addr)
    : Lemma
      (requires Seq.mem o (objects zero_addr g) /\ is_blue o g)
      (ensures U64.v addr + U64.v mword <= U64.v (hd_address o) \/
               U64.v addr >= U64.v (hd_address o) + (U64.v (wosize_of_object o g) + 1) * U64.v mword)
    = addr_in_object_outside_other g x o addr
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// zero_fields helpers
/// ---------------------------------------------------------------------------

/// zero_fields preserves heap length
let rec zero_fields_preserves_length (g: heap) (addr: U64.t) (n: nat)
  : Lemma (ensures Seq.length (Alloc.zero_fields g addr n) == Seq.length g)
          (decreases n)
  = if n = 0 then ()
    else if U64.v addr + 8 > heap_size then ()
    else if U64.v addr >= heap_size then ()
    else if U64.v addr % 8 <> 0 then ()
    else begin
      let g' = write_word g (addr <: hp_addr) 0UL in
      if U64.v addr + 8 >= pow2 64 then ()
      else zero_fields_preserves_length g' (U64.uint_to_t (U64.v addr + 8)) (n - 1)
    end

/// zero_fields preserves reads at addresses before the zeroed range
let rec zero_fields_preserves_before (g: heap) (start: U64.t) (n: nat) (addr: hp_addr)
  : Lemma
    (requires U64.v addr + U64.v mword <= U64.v start)
    (ensures read_word (Alloc.zero_fields g start n) addr == read_word g addr)
    (decreases n)
  = if n = 0 then ()
    else if U64.v start + 8 > heap_size then ()
    else if U64.v start >= heap_size then ()
    else if U64.v start % 8 <> 0 then ()
    else begin
      let g' = write_word g (start <: hp_addr) 0UL in
      read_write_different g (start <: hp_addr) addr 0UL;
      if U64.v start + 8 >= pow2 64 then ()
      else begin
        let next = U64.uint_to_t (U64.v start + 8) in
        zero_fields_preserves_before g' next (n - 1) addr
      end
    end

/// zero_fields preserves reads at addresses after the zeroed range
let rec zero_fields_preserves_after (g: heap) (start: U64.t) (n: nat) (addr: hp_addr)
  : Lemma
    (requires U64.v addr >= U64.v start + n * U64.v mword)
    (ensures read_word (Alloc.zero_fields g start n) addr == read_word g addr)
    (decreases n)
  = if n = 0 then ()
    else if U64.v start + 8 > heap_size then ()
    else if U64.v start >= heap_size then ()
    else if U64.v start % 8 <> 0 then ()
    else begin
      let g' = write_word g (start <: hp_addr) 0UL in
      read_write_different g (start <: hp_addr) addr 0UL;
      if U64.v start + 8 >= pow2 64 then ()
      else begin
        let next = U64.uint_to_t (U64.v start + 8) in
        zero_fields_preserves_after g' next (n - 1) addr
      end
    end

/// ---------------------------------------------------------------------------
/// Flush locality: writes stay within the blue run
/// ---------------------------------------------------------------------------

/// flush_blue preserves reads at addresses outside [hd_address fb, hd_address fb + run_words*8)
val flush_blue_preserves_outside
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (addr: hp_addr)
  : Lemma
    (requires run_words > 0 ==>
      (U64.v first_blue >= U64.v mword /\
       U64.v first_blue < heap_size /\
       U64.v first_blue % U64.v mword == 0 /\
       (U64.v addr + U64.v mword <= U64.v first_blue - U64.v mword \/
        U64.v addr >= U64.v first_blue - U64.v mword + run_words * U64.v mword)))
    (ensures read_word (fst (flush_blue g first_blue run_words fp)) addr
          == read_word g addr)

#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
let flush_blue_preserves_outside g first_blue run_words fp addr =
  if run_words = 0 then ()
  else if U64.v first_blue < U64.v mword
       || U64.v first_blue >= heap_size
       || U64.v first_blue % U64.v mword <> 0
  then ()
  else
    let fb : obj_addr = first_blue in
    let hd = hd_address fb in
    hd_address_spec fb;
    let wz = run_words - 1 in
    if wz >= pow2 54 then ()
    else begin
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      let wz_u64 : wosize = U64.uint_to_t wz in
      let hdr = makeHeader wz_u64 Blue 0UL in
      let g1 = write_word g hd hdr in
      assert (hd <> addr);
      read_write_different g hd addr hdr;
      if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        assert (U64.v (hd_address fb) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
        let field1_addr : hp_addr = U64.add (hd_address fb) (U64.mul mword 1UL) in
        assert (U64.v field1_addr == U64.v fb);
        assert (field1_addr <> addr);
        let g2 = HeapGraph.set_field g1 fb 1UL fp in
        read_write_different g1 field1_addr addr fp;
        let zero_start_nat = U64.v fb + U64.v mword in
        if wz >= 2 && zero_start_nat < pow2 64 then begin
          let zero_start = U64.uint_to_t zero_start_nat in
          if U64.v addr + U64.v mword <= U64.v zero_start then
            zero_fields_preserves_before g2 zero_start (wz - 1) addr
          else
            zero_fields_preserves_after g2 zero_start (wz - 1) addr
        end else ()
      end
      else ()
    end
#pop-options

/// flush_blue preserves heap length
val flush_blue_preserves_length
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma (Seq.length (fst (flush_blue g first_blue run_words fp)) == Seq.length g)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let flush_blue_preserves_length g first_blue run_words fp =
  if run_words = 0 then ()
  else if U64.v first_blue < U64.v mword
       || U64.v first_blue >= heap_size
       || U64.v first_blue % U64.v mword <> 0
  then ()
  else
    let fb : obj_addr = first_blue in
    let hd = hd_address fb in
    let wz = run_words - 1 in
    if wz >= pow2 54 then ()
    else begin
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      let wz_u64 : wosize = U64.uint_to_t wz in
      let hdr = makeHeader wz_u64 Blue 0UL in
      let g1 = write_word g hd hdr in
      if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        assert (U64.v (hd_address fb) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
        let g2 = HeapGraph.set_field g1 fb 1UL fp in
        let zero_start_nat = U64.v fb + U64.v mword in
        if wz >= 2 && zero_start_nat < pow2 64 then
          zero_fields_preserves_length g2 (U64.uint_to_t zero_start_nat) (wz - 1)
        else ()
      end
      else ()
    end
#pop-options

/// ---------------------------------------------------------------------------
/// flush_blue header spec: what header flush_blue writes
/// ---------------------------------------------------------------------------

/// After flush_blue with run_words > 0, the header at hd(first_blue) is the
/// merged header makeHeader(run_words-1, Blue, 0).
val flush_blue_header_spec
  (g: heap) (first_blue: obj_addr) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      run_words > 0 /\
      run_words - 1 < pow2 54 /\
      U64.v (hd_address first_blue) + run_words * U64.v mword <= heap_size /\
      Seq.length g == heap_size)
    (ensures (
      let (g', _) = flush_blue g first_blue run_words fp in
      read_word g' (hd_address first_blue) ==
        makeHeader (U64.uint_to_t (run_words - 1)) Blue 0UL))

#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
let flush_blue_header_spec g first_blue run_words fp =
  let fb = first_blue in
  let hd = hd_address fb in
  hd_address_spec fb;
  let wz = run_words - 1 in
  assert (wz < pow2 54);
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  let wz_u64 : wosize = U64.uint_to_t wz in
  let hdr = makeHeader wz_u64 Blue 0UL in
  let g1 = write_word g hd hdr in
  read_write_same g hd hdr;
  if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
    assert (U64.v (hd_address fb) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
    let g2 = HeapGraph.set_field g1 fb 1UL fp in
    let field1_addr : hp_addr = U64.add (hd_address fb) (U64.mul mword 1UL) in
    assert (U64.v field1_addr == U64.v fb);
    assert (field1_addr <> hd);
    read_write_different g1 field1_addr hd fp;
    let zero_start_nat = U64.v fb + U64.v mword in
    if wz >= 2 && zero_start_nat < pow2 64 then begin
      let zero_start = U64.uint_to_t zero_start_nat in
      assert (U64.v hd + U64.v mword <= U64.v zero_start);
      zero_fields_preserves_before g2 zero_start (wz - 1) hd
    end else ()
  end
  else ()
#pop-options

/// ---------------------------------------------------------------------------
/// flush_blue wosize spec: getWosize of the merged header
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// Walk structure helpers (moved early for use by later lemmas)
/// ---------------------------------------------------------------------------

/// When objects walk ends (next >= heap_size), tail is empty.
/// This follows from the objects definition with fuel 2.
#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
val objects_tail_empty_when_done (start: hp_addr) (g: heap)
  : Lemma
    (requires
      Seq.length (objects start g) > 0 /\
      (let wz = getWosize (read_word g start) in
       let next = U64.v start + (U64.v wz + 1) * U64.v mword in
       next <= Seq.length g /\ next < pow2 64 /\ next >= heap_size))
    (ensures Seq.tail (objects start g) == Seq.empty)

let objects_tail_empty_when_done start g = ()
#pop-options

/// ---------------------------------------------------------------------------
/// coalesce_aux preserves reads before run start
/// ---------------------------------------------------------------------------

/// Reads at positions before the start of the pending blue run (or before
/// the current walk position if no run) are preserved by coalesce_aux.
val coalesce_aux_preserves_before_run_start
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (addr: hp_addr)
  : Lemma
    (requires
      objs == objects start g0 /\
      Seq.length g0 == Seq.length g /\
      Seq.length g0 == heap_size /\
      (run_words > 0 ==>
        U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
        U64.v first_blue % U64.v mword == 0 /\
        U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start) /\
      U64.v addr + U64.v mword <=
        (if run_words > 0 then U64.v first_blue - U64.v mword else U64.v start))
    (ensures read_word (fst (coalesce_aux g0 g objs first_blue run_words fp)) addr
           == read_word g addr)
    (decreases Seq.length objs)

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec coalesce_aux_preserves_before_run_start g0 g start objs first_blue run_words fp addr =
  if Seq.length objs = 0 then begin
    // flush_blue: addr is before the run, so preserved
    flush_blue_preserves_outside g first_blue run_words fp addr
  end
  else begin
    objects_nonempty_next start g0;
    let header = read_word g0 start in
    let wz = getWosize header in
    let obj = f_address start in
    f_address_spec start;
    hd_address_spec obj;
    wosize_of_object_spec obj g0;
    let ws = U64.v (wosize_of_object obj g0) in
    let rest_start_nat = U64.v start + (U64.v wz + 1) * U64.v mword in
    if is_blue obj g0 then begin
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      let new_rw = run_words + ws + 1 in
      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        coalesce_aux_preserves_before_run_start g0 g next (Seq.tail objs)
          new_first new_rw fp addr
      end else begin
        objects_tail_empty_when_done start g0;
        flush_blue_preserves_outside g new_first new_rw fp addr
      end
    end
    else begin
      // White: flush, then recurse
      let (g', fp') = flush_blue g first_blue run_words fp in
      flush_blue_preserves_outside g first_blue run_words fp addr;
      flush_blue_preserves_length g first_blue run_words fp;
      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        coalesce_aux_preserves_before_run_start g0 g' next (Seq.tail objs)
          0UL 0 fp' addr
      end else begin
        objects_tail_empty_when_done start g0
      end
    end
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Coalesce preserves survivor data
/// ---------------------------------------------------------------------------

/// Helper: coalesce_aux preserves reads at addresses outside all blue regions
/// and outside the pending run.
///
/// Key strengthening: objs == objects start g0 links the remaining objects
/// to the heap walk structure, enabling contiguity proofs.
val coalesce_aux_preserves_outside
  (g0: heap) (g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr) (addr: hp_addr)
  : Lemma
    (requires
      objs == objects start g0 /\
      all_objs == objects zero_addr g0 /\
      Seq.length g0 == Seq.length g /\
      // all objects in objs are also in all_objs
      (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o all_objs) /\
      // addr is outside the pending blue run
      (run_words > 0 ==>
        (U64.v first_blue >= U64.v mword /\
         U64.v first_blue < heap_size /\
         U64.v first_blue % U64.v mword == 0 /\
         U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start /\
         (U64.v addr + U64.v mword <= U64.v first_blue - U64.v mword \/
          U64.v addr >= U64.v first_blue - U64.v mword + run_words * U64.v mword))) /\
      // addr is outside every blue object's region in the full objects list
      (forall (o: obj_addr). Seq.mem o all_objs /\ is_blue o g0 ==>
        (U64.v addr + U64.v mword <= U64.v (hd_address o) \/
         U64.v addr >= U64.v (hd_address o) + (U64.v (wosize_of_object o g0) + 1) * U64.v mword)))
    (ensures read_word (fst (coalesce_aux g0 g objs first_blue run_words fp)) addr
          == read_word g addr)
    (decreases Seq.length objs)

/// Geometric helper: extending a blue run preserves the "addr outside" property.
/// When run_words = 0, the run starts fresh at obj.
/// When run_words > 0, the old run is contiguous with obj.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
val extend_run_preserves_outside
  (addr: hp_addr) (first_blue: U64.t) (run_words: nat) (obj: obj_addr) (ws: nat)
  (start_val: nat)
  : Lemma
    (requires
      // obj starts at start_val
      U64.v (hd_address obj) == start_val /\
      (run_words > 0 ==>
        (U64.v first_blue >= U64.v mword /\
         U64.v first_blue < heap_size /\
         U64.v first_blue % U64.v mword == 0 /\
         U64.v first_blue - U64.v mword + run_words * U64.v mword == start_val /\
         (U64.v addr + U64.v mword <= U64.v first_blue - U64.v mword \/
          U64.v addr >= U64.v first_blue - U64.v mword + run_words * U64.v mword))) /\
      // addr outside obj region
      (U64.v addr + U64.v mword <= U64.v (hd_address obj) \/
       U64.v addr >= U64.v (hd_address obj) + (ws + 1) * U64.v mword))
    (ensures (
      let new_first = if run_words = 0 then obj else first_blue in
      let new_rw = run_words + ws + 1 in
      U64.v new_first >= U64.v mword /\
      U64.v new_first < heap_size /\
      U64.v new_first % U64.v mword == 0 /\
      (U64.v addr + U64.v mword <= U64.v new_first - U64.v mword \/
       U64.v addr >= U64.v new_first - U64.v mword + new_rw * U64.v mword)))

let extend_run_preserves_outside addr first_blue run_words obj ws start_val =
  hd_address_spec obj;
  if run_words = 0 then begin
    // new_first = obj, new run = [hd(obj), hd(obj) + (ws+1)*8)
    // addr outside obj region gives exactly what we need
    assert (U64.v obj >= U64.v mword);  // obj_addr >= 8
    ()
  end else begin
    // Contiguity: first_blue - 8 + run_words * 8 = start_val = hd(obj)
    // old run: [first_blue - 8, first_blue - 8 + run_words * 8) = [first_blue - 8, start_val)
    // obj: [start_val, start_val + (ws+1)*8)
    // extended run: [first_blue - 8, first_blue - 8 + (run_words + ws + 1) * 8)
    //             = [first_blue - 8, start_val + (ws+1)*8)
    //
    // addr outside old run: addr + 8 <= first_blue - 8  ∨  addr >= start_val
    // addr outside obj: addr + 8 <= start_val  ∨  addr >= start_val + (ws+1)*8
    //
    // Case analysis:
    //   addr + 8 <= first_blue - 8 ==> addr + 8 <= new_first - 8 ✓
    //   addr >= start_val ∧ addr + 8 <= start_val ==> impossible (addr >= start_val > start_val - 8 >= addr)
    //   addr >= start_val ∧ addr >= start_val + (ws+1)*8 ==> addr >= start_val + (ws+1)*8
    //     = addr >= first_blue - 8 + run_words * 8 + (ws+1)*8
    //     = addr >= first_blue - 8 + (run_words + ws + 1) * 8 ✓
    ()
  end
#pop-options

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec coalesce_aux_preserves_outside g0 g start objs first_blue run_words fp all_objs addr =
  if Seq.length objs = 0 then
    flush_blue_preserves_outside g first_blue run_words fp addr
  else begin
    objects_nonempty_next start g0;
    let header = read_word g0 start in
    let wz = getWosize header in
    let obj = f_address start in
    f_address_spec start;
    hd_address_spec obj;
    assert (U64.v (hd_address obj) == U64.v start);
    let rest_start_nat = U64.v start + (U64.v wz + 1) * U64.v mword in
    assert (obj == Seq.head objs);
    wosize_of_object_spec obj g0;
    let ws = U64.v (wosize_of_object obj g0) in
    assert (ws == U64.v wz);
    // obj ∈ objs (it's the head), and objs ⊆ all_objs, so obj ∈ all_objs
    mem_cons_lemma obj obj (Seq.tail objs);
    assert (Seq.mem obj objs);
    // Establish subset: tail ⊆ objs ⊆ all_objs for the recursive call
    let tail_subset (o: obj_addr)
      : Lemma (Seq.mem o (Seq.tail objs) ==> Seq.mem o all_objs)
      = mem_cons_lemma o obj (Seq.tail objs)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires tail_subset);
    if is_blue obj g0 then begin
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      extend_run_preserves_outside addr first_blue run_words obj ws (U64.v start);

      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        // objects_nonempty_next gives: objects start g0 == cons obj (objects next g0)
        // So tail objs == objects next g0
        Seq.lemma_tl obj (objects next g0);
        assert (Seq.tail objs == objects next g0);
        assert (U64.v new_first - U64.v mword + (run_words + ws + 1) * U64.v mword == rest_start_nat);
        coalesce_aux_preserves_outside g0 g next (Seq.tail objs)
          new_first (run_words + ws + 1) fp all_objs addr
      end else begin
        objects_tail_empty_when_done start g0;
        assert (Seq.tail objs == Seq.empty);
        flush_blue_preserves_outside g new_first (run_words + ws + 1) fp addr
      end
    end
    else begin
      let (g', fp') = flush_blue g first_blue run_words fp in
      flush_blue_preserves_outside g first_blue run_words fp addr;
      flush_blue_preserves_length g first_blue run_words fp;
      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        assert (Seq.tail objs == objects next g0);
        coalesce_aux_preserves_outside g0 g' next (Seq.tail objs) 0UL 0 fp' all_objs addr
      end else begin
        objects_tail_empty_when_done start g0;
        assert (Seq.tail objs == Seq.empty)
      end
    end
  end
#pop-options

/// Coalesce preserves survivor headers
val coalesce_preserves_survivor_header (g: heap) (x: obj_addr)
  : Lemma
    (requires post_sweep g /\ Seq.mem x (objects zero_addr g) /\ is_white x g)
    (ensures read_word (fst (coalesce g)) (hd_address x)
          == read_word g (hd_address x))

#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
let coalesce_preserves_survivor_header g x =
  hd_address_spec x;
  wosize_of_object_bound x g;
  let addr = hd_address x in
  white_addr_outside_all_blue g x addr;
  coalesce_aux_preserves_outside g g zero_addr (objects zero_addr g) 0UL 0 0UL (objects zero_addr g) addr
#pop-options

/// Coalesce preserves survivor fields
val coalesce_preserves_survivor_field
  (g: heap) (x: obj_addr) (i: U64.t{U64.v i >= 1})
  : Lemma
    (requires post_sweep g /\
             Seq.mem x (objects zero_addr g) /\ is_white x g /\
             U64.v i <= U64.v (wosize_of_object x g))
    (ensures HeapGraph.get_field (fst (coalesce g)) x i
          == HeapGraph.get_field g x i)

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let coalesce_preserves_survivor_field g x i =
  hd_address_spec x;
  wosize_of_object_bound x g;
  let hd = hd_address x in
  if U64.v hd + U64.v mword * U64.v i + U64.v mword <= heap_size then begin
    let field_addr_nat = U64.v hd + U64.v mword * U64.v i in
    assert (field_addr_nat < heap_size);
    assert (field_addr_nat % U64.v mword == 0);
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    assert (field_addr_nat < pow2 64);
    let field_addr : hp_addr = U64.uint_to_t field_addr_nat in
    // field_addr is in x's region: hd(x) <= field_addr < hd(x) + (wz+1)*8
    // since field index i >= 1 and i <= wz, field_addr = hd + i*8 where hd = x-8
    white_addr_outside_all_blue g x field_addr;
    coalesce_aux_preserves_outside g g zero_addr (objects zero_addr g) 0UL 0 0UL (objects zero_addr g) field_addr
  end else ()
#pop-options

/// ---------------------------------------------------------------------------
/// Heap length preservation (needed before walk characterization)
/// ---------------------------------------------------------------------------

let rec coalesce_aux_preserves_length
  (g0: heap) (g: heap) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma (ensures Seq.length (fst (coalesce_aux g0 g objs first_blue run_words fp)) == Seq.length g)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then
      flush_blue_preserves_length g first_blue run_words fp
    else
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      if is_blue obj g0 then
        let ws = U64.v (wosize_of_object obj g0) in
        let new_first : U64.t = if run_words = 0 then obj else first_blue in
        coalesce_aux_preserves_length g0 g rest new_first (run_words + ws + 1) fp
      else begin
        let (g', fp') = flush_blue g first_blue run_words fp in
        flush_blue_preserves_length g first_blue run_words fp;
        coalesce_aux_preserves_length g0 g' rest 0UL 0 fp'
      end

val coalesce_preserves_length (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures Seq.length (fst (coalesce g)) == Seq.length g)

let coalesce_preserves_length g =
  coalesce_aux_preserves_length g g (objects zero_addr g) 0UL 0 0UL

/// ---------------------------------------------------------------------------
/// coalesce_heap wrapper lemmas — bridge opaque coalesce_heap to transparent
/// coalesce_aux proofs, keeping coalesce_aux out of walk-property Z3 queries.
/// ---------------------------------------------------------------------------

let coalesce_heap_preserves_length
  (g0 g: heap) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma (Seq.length (coalesce_heap g0 g objs first_blue run_words fp) == Seq.length g)
  = coalesce_heap_unfold g0 g objs first_blue run_words fp;
    coalesce_aux_preserves_length g0 g objs first_blue run_words fp

#push-options "--fuel 0 --ifuel 0 --z3rlimit 12"
let coalesce_heap_preserves_outside
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr) (addr: hp_addr)
  : Lemma
    (requires
      objs == objects start g0 /\
      all_objs == objects zero_addr g0 /\
      Seq.length g0 == Seq.length g /\
      (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o all_objs) /\
      (run_words > 0 ==>
        (U64.v first_blue >= U64.v mword /\
         U64.v first_blue < heap_size /\
         U64.v first_blue % U64.v mword == 0 /\
         U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start /\
         (U64.v addr + U64.v mword <= U64.v first_blue - U64.v mword \/
          U64.v addr >= U64.v first_blue - U64.v mword + run_words * U64.v mword))) /\
      (forall (o: obj_addr). Seq.mem o all_objs /\ is_blue o g0 ==>
        (U64.v addr + U64.v mword <= U64.v (hd_address o) \/
         U64.v addr >= U64.v (hd_address o) + (U64.v (wosize_of_object o g0) + 1) * U64.v mword)))
    (ensures read_word (coalesce_heap g0 g objs first_blue run_words fp) addr
          == read_word g addr)
  = coalesce_heap_unfold g0 g objs first_blue run_words fp;
    coalesce_aux_preserves_outside g0 g start objs first_blue run_words fp all_objs addr
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 12"
let coalesce_heap_preserves_before_run_start
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (addr: hp_addr)
  : Lemma
    (requires
      objs == objects start g0 /\
      Seq.length g0 == Seq.length g /\
      Seq.length g0 == heap_size /\
      (run_words > 0 ==>
        U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
        U64.v first_blue % U64.v mword == 0 /\
        U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start) /\
      U64.v addr + U64.v mword <=
        (if run_words > 0 then U64.v first_blue - U64.v mword else U64.v start))
    (ensures
      read_word (coalesce_heap g0 g objs first_blue run_words fp) addr
      == read_word g addr)
  = coalesce_heap_unfold g0 g objs first_blue run_words fp;
    coalesce_aux_preserves_before_run_start g0 g start objs first_blue run_words fp addr
#pop-options

/// ---------------------------------------------------------------------------
/// Walk Property A: white survivors appear in coalesced walk
/// Walk Property B: all objects in coalesced walk are white or blue
/// ---------------------------------------------------------------------------

/// Preconditions bundle for walk property induction.
/// Includes invariant that g agrees with g0 at all white object headers.
let walk_pre (g0 g: heap) (start: hp_addr) (objs all_objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) : prop =
  objs == objects start g0 /\
  all_objs == objects zero_addr g0 /\
  Seq.length g0 == heap_size /\
  Seq.length g == heap_size /\
  post_sweep g0 /\
  (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o all_objs) /\
  (run_words > 0 ==>
    (U64.v first_blue >= U64.v mword /\
     U64.v first_blue < heap_size /\
     U64.v first_blue % U64.v mword == 0 /\
     U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start)) /\
  // g agrees with g0 at all white headers in objs
  (forall (o: obj_addr). Seq.mem o objs /\ is_white o g0 ==>
    read_word g (hd_address o) == read_word g0 (hd_address o))

/// Helper: objects walk is non-empty when start is a valid walk position
/// with a valid header producing a bounded next.
#push-options "--z3rlimit 12 --fuel 2 --ifuel 1"
let objects_nonempty_at (start: hp_addr) (g g0: heap)
  : Lemma
    (requires
      Seq.length g == Seq.length g0 /\
      Seq.length g == heap_size /\
      Seq.length (objects start g0) > 0 /\
      read_word g start == read_word g0 start)
    (ensures Seq.length (objects start g) > 0)
  = ()
#pop-options

/// Helper: derive run_words bound from walk_pre constraints.
/// When run_words > 0 and walk_pre holds, run_words < pow2 54.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let run_words_bound
  (fb: U64.t) (run_words: pos) (start: hp_addr)
  : Lemma
    (requires
      U64.v fb >= U64.v mword /\
      U64.v fb - U64.v mword + run_words * U64.v mword == U64.v start)
    (ensures run_words - 1 < pow2 54)
  = // fb >= mword, so fb - mword >= 0
    // run_words * mword = start - fb + mword = start - (fb - mword)
    // Since fb >= mword: fb - mword >= 0, so run_words * mword <= start
    // start < heap_size (hp_addr), heap_size <= pow2 57
    // run_words * 8 <= start < heap_size <= pow2 57
    // run_words <= start / 8 < pow2 57 / 8 = pow2 54
    assert (run_words * U64.v mword <= U64.v start);
    assert (U64.v start < heap_size);
    assert (heap_size <= pow2 57);
    FStar.Math.Lemmas.lemma_div_le (run_words * U64.v mword) (pow2 57 - 1) (U64.v mword);
    assert_norm (pow2 57 = pow2 54 * 8);
    FStar.Math.Lemmas.cancel_mul_div run_words (U64.v mword);
    ()
#pop-options

/// Same bound, for a run that ends exactly at the end of the heap.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let run_words_bound_le
  (fb: U64.t) (run_words: pos) (run_end: U64.t)
  : Lemma
    (requires
      U64.v fb >= U64.v mword /\
      U64.v run_end <= heap_size /\
      U64.v fb - U64.v mword + run_words * U64.v mword == U64.v run_end)
    (ensures run_words - 1 < pow2 54)
  = assert (run_words * U64.v mword <= U64.v run_end);
    assert (heap_size <= pow2 57);
    FStar.Math.Lemmas.lemma_div_le (run_words * U64.v mword) (pow2 57) (U64.v mword);
    assert_norm (pow2 57 = pow2 54 * 8);
    FStar.Math.Lemmas.cancel_mul_div run_words (U64.v mword);
    assert_norm ((pow2 54 * 8) / 8 == pow2 54)
#pop-options

/// Same bound again, for a run whose end is `heap_size` itself (not
/// representable as an `hp_addr`, hence a separate `nat`-ended variant).
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let run_words_bound_top
  (fb: U64.t) (run_words: pos)
  : Lemma
    (requires
      U64.v fb >= U64.v mword /\
      U64.v fb - U64.v mword + run_words * U64.v mword == heap_size)
    (ensures run_words - 1 < pow2 54)
  = assert (run_words * U64.v mword <= heap_size);
    assert (heap_size <= pow2 57);
    FStar.Math.Lemmas.lemma_div_le (run_words * U64.v mword) (pow2 57) (U64.v mword);
    assert_norm (pow2 57 = pow2 54 * 8);
    FStar.Math.Lemmas.cancel_mul_div run_words (U64.v mword);
    assert_norm ((pow2 54 * 8) / 8 == pow2 54)
#pop-options

/// `mk_hp_addr (fb - mword)` and `hd_address (fb <: obj_addr)` are the same
/// address, spelled two ways: `white_inv`'s H-reachability clause (clause 6)
/// uses the former (a plain scalar, needing no `obj_addr` cast on `fb`); the
/// `flush_white_transfer`/`flush_density_transfer`/`flush_reaches_run_end`
/// family, whose signatures predate that clause, use the latter.  Bridges
/// the two so a `walk_visits` fact about one transfers to the other.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let h_addr_agree (fb: U64.t)
  : Lemma
    (requires U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\ U64.v fb % U64.v mword == 0)
    (ensures mk_hp_addr (U64.v fb - U64.v mword) == hd_address (fb <: obj_addr))
  = hd_address_spec (fb <: obj_addr)
#pop-options

/// Helper: stepping over a merged blue block.
/// If the merged header at hd_address fb has wosize = run_words - 1,
/// and the next from there equals start, then:
/// - objects (hd_address fb) g' is non-empty
/// - fb is in that list
/// - any x in objects start g' is also in that list
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let merged_block_step
  (g': heap) (fb: obj_addr) (run_words: pos) (start: hp_addr) (x: obj_addr)
  : Lemma
    (requires
      Seq.length g' == heap_size /\
      U64.v fb >= U64.v mword /\
      U64.v fb < heap_size /\
      U64.v fb % U64.v mword == 0 /\
      U64.v fb - U64.v mword + run_words * U64.v mword == U64.v start /\
      run_words - 1 < pow2 54 /\
      U64.v start <= heap_size /\
      read_word g' (hd_address fb) == makeHeader (U64.uint_to_t (run_words - 1)) Blue 0UL)
    (ensures (
      Seq.length (objects (hd_address fb) g') > 0 /\
      Seq.mem fb (objects (hd_address fb) g') /\
      (U64.v start < heap_size /\ Seq.mem x (objects start g') ==>
       Seq.mem x (objects (hd_address fb) g'))))
  = hd_address_spec fb;
    let sync = hd_address fb in
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    f_address_spec sync;
    if U64.v start >= heap_size then begin
      mem_cons_lemma x fb Seq.empty;
      mem_cons_lemma fb fb Seq.empty
    end
    else begin
      mem_cons_lemma x fb (objects start g');
      mem_cons_lemma fb fb (objects start g')
    end
#pop-options

/// Helper: if the merged header is present, the object is blue.
#push-options "--z3rlimit 25 --fuel 1 --ifuel 1"
private let merged_block_is_blue
  (g': heap) (fb: obj_addr) (wz: wosize)
  : Lemma
    (requires
      Seq.length g' == heap_size /\
      read_word g' (hd_address fb) == makeHeader wz Blue 0UL)
    (ensures is_blue fb g')
  = makeHeader_getColor wz Blue 0UL;
    color_of_object_spec fb g';
    is_blue_iff fb g'
#pop-options

/// Helper: decompose membership in the merged block walk.
/// If y ∈ objects (hd_address fb) g', then either y = fb or y ∈ objects start g'.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let merged_block_decompose
  (g': heap) (fb: obj_addr) (run_words: pos) (start: U64.t) (y: obj_addr)
  : Lemma
    (requires
      Seq.length g' == heap_size /\
      U64.v fb >= U64.v mword /\
      U64.v fb < heap_size /\
      U64.v fb % U64.v mword == 0 /\
      U64.v fb - U64.v mword + run_words * U64.v mword == U64.v start /\
      run_words - 1 < pow2 54 /\
      U64.v start <= heap_size /\
      U64.v start % U64.v mword == 0 /\
      read_word g' (hd_address fb) == makeHeader (U64.uint_to_t (run_words - 1)) Blue 0UL /\
      Seq.mem y (objects (hd_address fb) g'))
    (ensures
      y = fb \/ (U64.v start < heap_size /\ Seq.mem y (objects (start <: hp_addr) g')))
  = hd_address_spec fb;
    let sync = hd_address fb in
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    f_address_spec sync;
    objects_nonempty_next sync g';
    Seq.cons_head_tail (objects sync g');
    mem_cons_lemma y fb (Seq.tail (objects sync g'));
    if y = fb then ()
    else begin
      if U64.v start >= heap_size then begin
        // objects sync g' = [fb], so y = fb, contradiction
        assert (Seq.mem y (Seq.tail (objects sync g')));
        ()
      end
      else begin
        Seq.lemma_tl fb (objects (start <: hp_addr) g');
        assert (Seq.mem y (objects (start <: hp_addr) g'))
      end
    end
#pop-options

private let merged_block_recompose
  (g': heap) (fb: obj_addr) (run_words: pos) (start: U64.t) (y: obj_addr)
  : Lemma
    (requires
      Seq.length g' == heap_size /\
      U64.v fb >= U64.v mword /\
      U64.v fb < heap_size /\
      U64.v fb % U64.v mword == 0 /\
      U64.v fb - U64.v mword + run_words * U64.v mword == U64.v start /\
      run_words - 1 < pow2 54 /\
      U64.v start < heap_size /\
      U64.v start % U64.v mword == 0 /\
      read_word g' (hd_address fb) == makeHeader (U64.uint_to_t (run_words - 1)) Blue 0UL /\
      Seq.mem y (objects (start <: hp_addr) g'))
    (ensures Seq.mem y (objects (hd_address fb) g'))
  = hd_address_spec fb;
    let sync = hd_address fb in
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    f_address_spec sync;
    objects_nonempty_next sync g';
    Seq.lemma_tl fb (objects (start <: hp_addr) g');
    mem_cons_lemma y fb (Seq.tail (objects sync g'))

/// Helper: flush preserves headers of white objects that come later in the walk.
/// Used to maintain the walk_pre invariant across the white case.
/// ---------------------------------------------------------------------------
/// Property A: white survivors appear in coalesced walk
/// ---------------------------------------------------------------------------

val coalesce_aux_survivors_in_walk
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr) (x: obj_addr)
  : Lemma
    (requires
      walk_pre g0 g start objs all_objs first_blue run_words /\
      Seq.mem x objs /\ is_white x g0)
    (ensures (
      let sync : hp_addr =
        if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
      Seq.mem x (objects sync (coalesce_heap g0 g objs first_blue run_words fp))))
    (decreases Seq.length objs)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let rec coalesce_aux_survivors_in_walk g0 g start objs first_blue run_words fp all_objs x =
  if Seq.length objs = 0 then ()
  else begin
    objects_nonempty_next start g0;
    let header = read_word g0 start in
    let wz = getWosize header in
    let obj = f_address start in
    f_address_spec start;
    hd_address_spec obj;
    let rest_start_nat = U64.v start + (U64.v wz + 1) * U64.v mword in
    assert (obj == Seq.head objs);
    Seq.cons_head_tail objs;
    wosize_of_object_spec obj g0;
    let ws = U64.v (wosize_of_object obj g0) in

    let tail_sub (o: obj_addr)
      : Lemma (Seq.mem o (Seq.tail objs) ==> Seq.mem o all_objs)
      = mem_cons_lemma o obj (Seq.tail objs)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires tail_sub);
    mem_cons_lemma x obj (Seq.tail objs);

    if is_blue obj g0 then begin
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      is_white_iff x g0; is_blue_iff obj g0;
      assert (x <> obj);
      assert (Seq.mem x (Seq.tail objs));

      let tail_white_inv (o: obj_addr)
        : Lemma (Seq.mem o (Seq.tail objs) /\ is_white o g0 ==>
                 read_word g (hd_address o) == read_word g0 (hd_address o))
        = mem_cons_lemma o obj (Seq.tail objs)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires tail_white_inv);

      coalesce_heap_blue_step g0 g objs first_blue run_words fp;

      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        assert (Seq.tail objs == objects next g0);
        coalesce_aux_survivors_in_walk g0 g next (Seq.tail objs)
          new_first (run_words + ws + 1) fp all_objs x
      end
      else begin
        objects_tail_empty_when_done start g0;
        assert (Seq.tail objs == Seq.empty)
      end
    end
    else begin
      mem_cons_lemma obj obj (Seq.tail objs);
      assert (Seq.mem obj all_objs);
      is_blue_iff obj g0; is_white_iff obj g0;
      assert (is_white obj g0);

      let (g_flush, fp_flush) = flush_blue g first_blue run_words fp in
      flush_blue_preserves_length g first_blue run_words fp;

      coalesce_heap_white_step g0 g objs first_blue run_words fp g_flush fp_flush;
      let g_result = coalesce_heap g0 g_flush (Seq.tail objs) 0UL 0 fp_flush in
      coalesce_heap_preserves_length g0 g_flush (Seq.tail objs) 0UL 0 fp_flush;
      assert (Seq.length g_result == heap_size);

      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        assert (Seq.tail objs == objects next g0);

        let flush_white_hdr_inv (o: obj_addr)
          : Lemma
            (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
            (ensures read_word g_flush (hd_address o) == read_word g0 (hd_address o))
          = mem_cons_lemma o obj (Seq.tail objs);
            objects_addresses_gt_start next g0 o;
            hd_address_spec o;
            flush_blue_preserves_outside g first_blue run_words fp (hd_address o)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires flush_white_hdr_inv);

        white_addr_outside_all_blue g0 obj start;
        flush_blue_preserves_outside g first_blue run_words fp start;
        coalesce_heap_preserves_outside g0 g_flush next (Seq.tail objs)
          0UL 0 fp_flush all_objs start;
        assert (read_word g_result start == read_word g0 start);

        objects_nonempty_at start g_result g0;
        objects_nonempty_next start g_result;

        if x = obj then begin
          // obj = f_address start = Seq.head (objects start g_result)
          mem_cons_lemma obj (f_address start) (Seq.tail (objects start g_result));
          assert (Seq.mem obj (objects start g_result));
          if run_words > 0 then begin
            // Need merged header in g_result
            hd_address_spec (first_blue <: obj_addr);
            run_words_bound first_blue run_words start;
            flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
            // Preserve header from g_flush to g_result
            assert (U64.v first_blue <= U64.v next);
            coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
              0UL 0 fp_flush (hd_address (first_blue <: obj_addr));
            merged_block_step g_result (first_blue <: obj_addr) run_words start obj
          end
        end
        else begin
          assert (Seq.mem x (Seq.tail objs));
          // IH gives Seq.mem x (objects next g_result) since run_words_IH = 0
          coalesce_aux_survivors_in_walk g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs x;
          // Lift from next to start
          objects_later_subset start g_result x;
          if run_words > 0 then begin
            assert (Seq.mem x (objects start g_result));
            hd_address_spec (first_blue <: obj_addr);
            run_words_bound first_blue run_words start;
            flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
            assert (U64.v first_blue <= U64.v next);
            coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
              0UL 0 fp_flush (hd_address (first_blue <: obj_addr));
            merged_block_step g_result (first_blue <: obj_addr) run_words start x
          end
        end
      end
      else begin
        objects_tail_empty_when_done start g0;
        assert (Seq.length (Seq.tail objs) = 0);
        coalesce_heap_empty g0 g_flush 0UL 0 fp_flush;

        if x = obj then begin
          flush_blue_preserves_outside g first_blue run_words fp start;
          objects_nonempty_at start g_flush g0;
          objects_nonempty_next start g_flush;
          mem_cons_lemma obj (f_address start) (Seq.tail (objects start g_flush));
          assert (Seq.mem obj (objects start g_flush));
          if run_words > 0 then begin
            hd_address_spec (first_blue <: obj_addr);
            run_words_bound first_blue run_words start;
            flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
            assert (U64.v start <= heap_size);
            merged_block_step g_flush (first_blue <: obj_addr) run_words start obj
          end
        end
        else begin
          assert (~(Seq.mem x (Seq.tail objs)))
        end
      end
    end
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Property A': the free-list head produced by the walk is a walk object
/// ---------------------------------------------------------------------------

/// A merged blue block is the head of the object walk that starts at its own
/// header.  Unlike `merged_block_step` this says nothing about what follows it,
/// so it also applies when the merged block runs to the very end of the heap.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let merged_block_head (g': heap) (fb: obj_addr) (run_words: pos)
  : Lemma
    (requires
      Seq.length g' == heap_size /\
      run_words - 1 < pow2 54 /\
      U64.v (hd_address fb) + run_words * U64.v mword <= heap_size /\
      read_word g' (hd_address fb) == makeHeader (U64.uint_to_t (run_words - 1)) Blue 0UL)
    (ensures Seq.mem fb (objects (hd_address fb) g'))
  = hd_address_spec fb;
    let sync = hd_address fb in
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    f_address_spec sync;
    if U64.v sync + (run_words) * U64.v mword >= heap_size then
      mem_cons_lemma fb fb Seq.empty
    else
      mem_cons_lemma fb fb
        (objects (U64.uint_to_t (U64.v sync + run_words * U64.v mword) <: hp_addr) g')
#pop-options

/// Helper for the flush at the end of a run: the head the flush returns is
/// either the head it was given or the merged block it just wrote, and the
/// merged block is an object of the walk that begins at the run's start.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
private let flush_blue_head_in_walk
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t) (run_end: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v run_end <= heap_size /\
      (run_words > 0 ==>
        U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
        U64.v first_blue % U64.v mword == 0 /\
        U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v run_end))
    (ensures (
      let r = flush_blue g first_blue run_words fp in
      snd r == fp \/
      (run_words > 0 /\ snd r == first_blue /\
       U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
       U64.v first_blue % U64.v mword == 0 /\
       Seq.mem (first_blue <: obj_addr) (objects (hd_address (first_blue <: obj_addr)) (fst r)))))
  = if run_words = 0 then ()
    else begin
      let fb : obj_addr = first_blue in
      hd_address_spec fb;
      run_words_bound_le first_blue run_words run_end;
      flush_blue_preserves_length g first_blue run_words fp;
      flush_blue_header_spec g fb run_words fp;
      let r = flush_blue g first_blue run_words fp in
      if snd r = fp then () else merged_block_head (fst r) fb run_words
    end
#pop-options

/// **The walk's free-list head is a walk object.**
///
/// `coalesce` rebuilds the free list from scratch, so its head is either the
/// null head it started from or one of the merged blocks it wrote -- and every
/// merged block is an object of the coalesced walk.  This is the one fact the
/// descending-chain argument in `GC.Spec.Coalesce.Descending` cannot supply,
/// because `fl_desc_chain` deliberately avoids reading the object walk.
val coalesce_aux_head_in_walk
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires walk_pre g0 g start objs all_objs first_blue run_words)
    (ensures (
      let r = coalesce_aux g0 g objs first_blue run_words fp in
      let sync : hp_addr =
        if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
      snd r == fp \/
      (U64.v (snd r) >= U64.v mword /\ U64.v (snd r) < heap_size /\
       U64.v (snd r) % U64.v mword == 0 /\
       Seq.mem (snd r <: obj_addr)
         (objects sync (coalesce_heap g0 g objs first_blue run_words fp)))))
    (decreases Seq.length objs)

#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let rec coalesce_aux_head_in_walk g0 g start objs first_blue run_words fp all_objs =
  let sync : hp_addr =
    if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
  if Seq.length objs = 0 then begin
    coalesce_heap_empty g0 g first_blue run_words fp;
    flush_blue_head_in_walk g first_blue run_words fp start
  end
  else begin
    objects_nonempty_next start g0;
    let header = read_word g0 start in
    let wz = getWosize header in
    let obj = f_address start in
    f_address_spec start;
    hd_address_spec obj;
    let rest_start_nat = U64.v start + (U64.v wz + 1) * U64.v mword in
    assert (obj == Seq.head objs);
    Seq.cons_head_tail objs;
    wosize_of_object_spec obj g0;
    let ws = U64.v (wosize_of_object obj g0) in

    let tail_sub (o: obj_addr)
      : Lemma (Seq.mem o (Seq.tail objs) ==> Seq.mem o all_objs)
      = mem_cons_lemma o obj (Seq.tail objs)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires tail_sub);

    if is_blue obj g0 then begin
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      let new_rw = run_words + ws + 1 in
      // The run's floor -- and hence the walk position the merged block will be
      // reported against -- does not move when the run grows.
      assert (hd_address (new_first <: obj_addr) == sync);

      let tail_white_inv (o: obj_addr)
        : Lemma (Seq.mem o (Seq.tail objs) /\ is_white o g0 ==>
                 read_word g (hd_address o) == read_word g0 (hd_address o))
        = mem_cons_lemma o obj (Seq.tail objs)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires tail_white_inv);

      coalesce_heap_blue_step g0 g objs first_blue run_words fp;

      assert (coalesce_aux g0 g objs first_blue run_words fp ==
              coalesce_aux g0 g (Seq.tail objs) new_first new_rw fp);
      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        coalesce_aux_head_in_walk g0 g next (Seq.tail objs) new_first new_rw fp all_objs
      end
      else begin
        objects_tail_empty_when_done start g0;
        flush_blue_head_in_walk g new_first new_rw fp (U64.uint_to_t rest_start_nat);
        coalesce_heap_empty g0 g new_first new_rw fp
      end
    end
    else begin
      mem_cons_lemma obj obj (Seq.tail objs);
      is_blue_iff obj g0; is_white_iff obj g0;
      assert (is_white obj g0);

      let (g_flush, fp_flush) = flush_blue g first_blue run_words fp in
      flush_blue_preserves_length g first_blue run_words fp;
      flush_blue_head_in_walk g first_blue run_words fp start;

      coalesce_heap_white_step g0 g objs first_blue run_words fp g_flush fp_flush;
      let g_result = coalesce_heap g0 g_flush (Seq.tail objs) 0UL 0 fp_flush in
      coalesce_heap_preserves_length g0 g_flush (Seq.tail objs) 0UL 0 fp_flush;

      // Wherever the merged block of the just-flushed run ends up being
      // reported, its header survives the rest of the walk: the walk only
      // writes at or above `start`, and the block lies strictly below it.
      let merged_survives () : Lemma
        (requires run_words > 0 /\ fp_flush == first_blue)
        (ensures Seq.mem (first_blue <: obj_addr) (objects sync g_result))
        = hd_address_spec (first_blue <: obj_addr);
          run_words_bound first_blue run_words start;
          flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
          if rest_start_nat < heap_size then begin
            let next : hp_addr = U64.uint_to_t rest_start_nat in
            Seq.lemma_tl obj (objects next g0);
            assert (U64.v first_blue <= U64.v next);
            coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
              0UL 0 fp_flush (hd_address (first_blue <: obj_addr))
          end
          else begin
            objects_tail_empty_when_done start g0;
            coalesce_heap_empty g0 g_flush 0UL 0 fp_flush
          end;
          merged_block_head g_result (first_blue <: obj_addr) run_words
      in

      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);

        let flush_white_hdr_inv (o: obj_addr)
          : Lemma
            (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
            (ensures read_word g_flush (hd_address o) == read_word g0 (hd_address o))
          = mem_cons_lemma o obj (Seq.tail objs);
            objects_addresses_gt_start next g0 o;
            hd_address_spec o;
            flush_blue_preserves_outside g first_blue run_words fp (hd_address o)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires flush_white_hdr_inv);

        white_addr_outside_all_blue g0 obj start;
        flush_blue_preserves_outside g first_blue run_words fp start;
        coalesce_heap_preserves_outside g0 g_flush next (Seq.tail objs)
          0UL 0 fp_flush all_objs start;
        objects_nonempty_at start g_result g0;
        objects_nonempty_next start g_result;

        coalesce_aux_head_in_walk g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs;
        let res = snd (coalesce_aux g0 g_flush (Seq.tail objs) 0UL 0 fp_flush) in
        assert (snd (coalesce_aux g0 g objs first_blue run_words fp) == res);
        if res = fp_flush then begin
          if run_words > 0 && fp_flush <> fp then merged_survives ()
        end
        else begin
          objects_later_subset start g_result (res <: obj_addr);
          if run_words > 0 then begin
            hd_address_spec (first_blue <: obj_addr);
            run_words_bound first_blue run_words start;
            flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
            coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
              0UL 0 fp_flush (hd_address (first_blue <: obj_addr));
            merged_block_step g_result (first_blue <: obj_addr) run_words start
              (res <: obj_addr)
          end
        end
      end
      else begin
        objects_tail_empty_when_done start g0;
        coalesce_heap_empty g0 g_flush 0UL 0 fp_flush;
        assert (snd (coalesce_aux g0 g objs first_blue run_words fp) == fp_flush);
        if run_words > 0 && fp_flush <> fp then merged_survives ()
      end
    end
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Property B: all objects in coalesced walk are white or blue
/// ---------------------------------------------------------------------------

val coalesce_aux_walk_all_wb_tag
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr) (y: obj_addr)
  : Lemma
    (requires
      walk_pre g0 g start objs all_objs first_blue run_words /\
      (run_words > 0 ==> Seq.mem (first_blue <: obj_addr) all_objs) /\
      (forall (addr: hp_addr). U64.v addr >= U64.v start ==>
        read_word g addr == read_word g0 addr) /\
      (let sync : hp_addr =
         if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
       Seq.mem y (objects sync (coalesce_heap g0 g objs first_blue run_words fp))))
    (ensures (
      let g' = coalesce_heap g0 g objs first_blue run_words fp in
      Seq.mem y all_objs /\
      ((Seq.mem y objs /\ is_white y g0 /\ ~(is_blue y g')) \/
       (is_blue y g' /\ tag_of_object y g' == 0UL))))
    (decreases Seq.length objs)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let rec coalesce_aux_walk_all_wb_tag g0 g start objs first_blue run_words fp all_objs y =
  let g' = coalesce_heap g0 g objs first_blue run_words fp in
  if Seq.length objs = 0 then begin
    assert (Seq.equal objs Seq.empty);
    coalesce_heap_empty g0 g first_blue run_words fp;
    if run_words > 0 then begin
      flush_blue_preserves_length g first_blue run_words fp;
      hd_address_spec (first_blue <: obj_addr);
      run_words_bound first_blue run_words start;
      flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
      let wz : wosize = U64.uint_to_t (run_words - 1) in
      merged_block_decompose g' (first_blue <: obj_addr) run_words start y;
      if y = (first_blue <: obj_addr) then begin
        merged_block_is_blue g' (first_blue <: obj_addr) wz;
        makeHeader_getTag wz Blue 0UL;
        tag_of_object_spec y g';
        assert (Seq.mem (first_blue <: obj_addr) all_objs)
      end
      else begin
        // y <> first_blue, so from merged_block_decompose: y in objects start g'
        // objects start g' = objects start g0 = Seq.empty -> contradiction
        flush_blue_preserves_outside g first_blue run_words fp start;
        assert (read_word g' start == read_word g start);
        assert (read_word g start == read_word g0 start);
        assert (read_word g' start == read_word g0 start);
        assert (Seq.length g' == heap_size)
      end
    end else ()
  end
  else begin
    objects_nonempty_next start g0;
    let header = read_word g0 start in
    let wz = getWosize header in
    let obj = f_address start in
    f_address_spec start;
    hd_address_spec obj;
    let rest_start_nat = U64.v start + (U64.v wz + 1) * U64.v mword in
    assert (obj == Seq.head objs);
    Seq.cons_head_tail objs;
    wosize_of_object_spec obj g0;
    let ws = U64.v (wosize_of_object obj g0) in

    let tail_sub (o: obj_addr)
      : Lemma (Seq.mem o (Seq.tail objs) ==> Seq.mem o all_objs)
      = mem_cons_lemma o obj (Seq.tail objs)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires tail_sub);

    if is_blue obj g0 then begin
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      let new_rw = run_words + ws + 1 in

      let tail_white_inv (o: obj_addr)
        : Lemma (Seq.mem o (Seq.tail objs) /\ is_white o g0 ==>
                 read_word g (hd_address o) == read_word g0 (hd_address o))
        = mem_cons_lemma o obj (Seq.tail objs)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires tail_white_inv);

      coalesce_heap_blue_step g0 g objs first_blue run_words fp;

      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        assert (Seq.tail objs == objects next g0);
        // Maintain the all_objs hypothesis: new_rw > 0 always, and new_first is
        // either obj (when run_words = 0) or first_blue (when run_words > 0).
        assert (Seq.mem (new_first <: obj_addr) all_objs);
        coalesce_aux_walk_all_wb_tag g0 g next (Seq.tail objs)
          new_first new_rw fp all_objs y
      end
      else begin
        objects_tail_empty_when_done start g0;
        assert (Seq.equal (Seq.tail objs) Seq.empty);
        coalesce_heap_empty g0 g new_first new_rw fp;
        flush_blue_preserves_length g new_first new_rw fp;
        hd_address_spec (new_first <: obj_addr);
        let rest_u64 : U64.t = U64.uint_to_t rest_start_nat in
        assert (new_rw * U64.v mword <= heap_size);
        FStar.Math.Lemmas.lemma_div_le (new_rw * 8) (pow2 57) 8;
        FStar.Math.Lemmas.cancel_mul_div new_rw 8;
        FStar.Math.Lemmas.pow2_lt_compat 64 54;
        assert_norm (pow2 54 == 0x40000000000000);
        assert_norm (pow2 57 == 0x200000000000000);
        assert (new_rw * 8 <= pow2 57);
        assert (new_rw <= pow2 54);
        assert (new_rw - 1 < pow2 54);
        let wz_merged : wosize = U64.uint_to_t (new_rw - 1) in
        flush_blue_header_spec g (new_first <: obj_addr) new_rw fp;
        merged_block_decompose g' (new_first <: obj_addr) new_rw rest_u64 y;
        // rest is empty, so y must be new_first
        merged_block_is_blue g' (new_first <: obj_addr) wz_merged;
        makeHeader_getTag wz_merged Blue 0UL;
        tag_of_object_spec y g';
        assert (Seq.mem (new_first <: obj_addr) all_objs)
      end
    end
    else begin
      // White case: obj is white in g0
      mem_cons_lemma obj obj (Seq.tail objs);
      assert (Seq.mem obj all_objs);
      is_blue_iff obj g0; is_white_iff obj g0;
      assert (is_white obj g0);

      let (g_flush, fp_flush) = flush_blue g first_blue run_words fp in
      flush_blue_preserves_length g first_blue run_words fp;

      coalesce_heap_white_step g0 g objs first_blue run_words fp g_flush fp_flush;
      coalesce_heap_preserves_length g0 g_flush (Seq.tail objs) 0UL 0 fp_flush;
      assert (Seq.length g' == heap_size);

      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        assert (Seq.tail objs == objects next g0);

        // g' preserves reads before next (run_start for tail = next since rw=0)
        coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
          0UL 0 fp_flush start;
        // g_flush preserves reads at start (outside blue run)
        flush_blue_preserves_outside g first_blue run_words fp start;
        // Chain: read_word g' start == read_word g_flush start == read_word g start == read_word g0 start
        assert (read_word g' start == read_word g0 start);

        // objects start g' is non-empty (same header as g0 at start)
        objects_nonempty_at start g' g0;
        objects_nonempty_next start g';
        Seq.cons_head_tail (objects start g');
        f_address_spec start;
        mem_cons_lemma y (f_address start) (Seq.tail (objects start g'));
        Seq.lemma_tl obj (objects next g');

        if run_words > 0 then begin
          // sync = hd_address first_blue; need merged header in g' for decomposition
          hd_address_spec (first_blue <: obj_addr);
          run_words_bound first_blue run_words start;
          flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
          coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
            0UL 0 fp_flush (hd_address (first_blue <: obj_addr));
          let wz_fb : wosize = U64.uint_to_t (run_words - 1) in
          merged_block_decompose g' (first_blue <: obj_addr) run_words start y;
          if y = (first_blue <: obj_addr) then begin
            merged_block_is_blue g' (first_blue <: obj_addr) wz_fb;
            makeHeader_getTag wz_fb Blue 0UL;
            tag_of_object_spec y g';
            assert (Seq.mem (first_blue <: obj_addr) all_objs)
          end
          else begin
            // y in objects start g': either y = obj or y in objects next g'
            if y = obj then begin
              // obj is white in g0 and its header at start is preserved into g'
              color_of_header_eq obj g0 g';
              is_blue_iff obj g'; is_blue_iff obj g0;
              assert (Seq.mem obj all_objs)
            end
            else begin
              assert (Seq.mem y (objects next g'));
              // Maintain new invariant for IH
              let flush_addr_inv (addr: hp_addr)
                : Lemma (requires U64.v addr >= U64.v next)
                        (ensures read_word g_flush addr == read_word g0 addr)
                = flush_blue_preserves_outside g first_blue run_words fp addr
              in
              FStar.Classical.forall_intro (FStar.Classical.move_requires flush_addr_inv);
              // Maintain walk_pre for IH
              let flush_white_hdr_inv (o: obj_addr)
                : Lemma
                  (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
                  (ensures read_word g_flush (hd_address o) == read_word g0 (hd_address o))
                = mem_cons_lemma o obj (Seq.tail objs);
                  objects_addresses_gt_start next g0 o;
                  hd_address_spec o;
                  flush_blue_preserves_outside g first_blue run_words fp (hd_address o)
              in
              FStar.Classical.forall_intro (FStar.Classical.move_requires flush_white_hdr_inv);
              coalesce_aux_walk_all_wb_tag g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs y;
              if Seq.mem y (Seq.tail objs) then
                mem_cons_lemma y obj (Seq.tail objs)
            end
          end
        end
        else begin
          // run_words = 0, sync = start: y = obj or y in objects next g'
          if y = obj then begin
            color_of_header_eq obj g0 g';
            is_blue_iff obj g'; is_blue_iff obj g0;
            assert (Seq.mem obj all_objs)
          end
          else begin
            assert (Seq.mem y (objects next g'));
            // Maintain invariants for IH
            let flush_addr_inv (addr: hp_addr)
              : Lemma (requires U64.v addr >= U64.v next)
                      (ensures read_word g_flush addr == read_word g0 addr)
              = flush_blue_preserves_outside g first_blue run_words fp addr
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires flush_addr_inv);
            let flush_white_hdr_inv (o: obj_addr)
              : Lemma
                (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
                (ensures read_word g_flush (hd_address o) == read_word g0 (hd_address o))
              = mem_cons_lemma o obj (Seq.tail objs);
                objects_addresses_gt_start next g0 o;
                hd_address_spec o;
                flush_blue_preserves_outside g first_blue run_words fp (hd_address o)
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires flush_white_hdr_inv);
            coalesce_aux_walk_all_wb_tag g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs y;
            if Seq.mem y (Seq.tail objs) then
              mem_cons_lemma y obj (Seq.tail objs)
          end
        end
      end
      else begin
        objects_tail_empty_when_done start g0;
        assert (Seq.equal (Seq.tail objs) Seq.empty);
        coalesce_heap_empty g0 g_flush 0UL 0 fp_flush;

        if run_words > 0 then begin
          hd_address_spec (first_blue <: obj_addr);
          run_words_bound first_blue run_words start;
          flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
          let wz_fb : wosize = U64.uint_to_t (run_words - 1) in
          merged_block_decompose g' (first_blue <: obj_addr) run_words start y;
          if y = (first_blue <: obj_addr) then begin
            merged_block_is_blue g' (first_blue <: obj_addr) wz_fb;
            makeHeader_getTag wz_fb Blue 0UL;
            tag_of_object_spec y g';
            assert (Seq.mem (first_blue <: obj_addr) all_objs)
          end
          else begin
            // y in objects start g', but rest_start >= heap_size, so y = obj
            flush_blue_preserves_outside g first_blue run_words fp start;
            assert (read_word g' start == read_word g0 start);
            objects_nonempty_at start g' g0;
            objects_nonempty_next start g';
            mem_cons_lemma y (f_address start) (Seq.tail (objects start g'));
            assert (y == obj);
            assert (Seq.mem y objs /\ is_white y g0);
            assert (Seq.mem obj all_objs);
            color_of_header_eq y g0 g';
            is_blue_iff y g'; is_blue_iff y g0
          end
        end
        else begin
          // run_words = 0, sync = start, g' = g_flush = g (no-op flush)
          flush_blue_preserves_outside g first_blue run_words fp start;
          assert (read_word g' start == read_word g0 start);
          objects_nonempty_at start g' g0;
          objects_nonempty_next start g';
          mem_cons_lemma y (f_address start) (Seq.tail (objects start g'));
          assert (y == obj);
          assert (Seq.mem y objs /\ is_white y g0);
          assert (Seq.mem obj all_objs);
          color_of_header_eq y g0 g';
          is_blue_iff y g'; is_blue_iff y g0
        end
      end
    end
  end
#pop-options

/// Corollary: every object in the coalesced walk is either an untouched white
/// object or a blue (merged) block.
val coalesce_aux_walk_all_wb
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr) (y: obj_addr)
  : Lemma
    (requires
      walk_pre g0 g start objs all_objs first_blue run_words /\
      (run_words > 0 ==> Seq.mem (first_blue <: obj_addr) all_objs) /\
      (forall (addr: hp_addr). U64.v addr >= U64.v start ==>
        read_word g addr == read_word g0 addr) /\
      (let sync : hp_addr =
         if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
       Seq.mem y (objects sync (coalesce_heap g0 g objs first_blue run_words fp))))
    (ensures (
      let g' = coalesce_heap g0 g objs first_blue run_words fp in
      (Seq.mem y objs /\ is_white y g0) \/ is_blue y g'))

let coalesce_aux_walk_all_wb g0 g start objs first_blue run_words fp all_objs y =
  coalesce_aux_walk_all_wb_tag g0 g start objs first_blue run_words fp all_objs y

/// ---------------------------------------------------------------------------

val coalesce_survivors_in_objects (g: heap) (x: obj_addr)
  : Lemma
    (requires post_sweep g /\ Seq.mem x (objects zero_addr g) /\ is_white x g)
    (ensures Seq.mem x (objects zero_addr (fst (coalesce g))))

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
let coalesce_survivors_in_objects g x =
  coalesce_aux_survivors_in_walk g g zero_addr (objects zero_addr g) 0UL 0 0UL (objects zero_addr g) x;
  coalesce_heap_unfold g g (objects zero_addr g) 0UL 0 0UL
#pop-options

val coalesce_all_white_or_blue (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures (forall (x: obj_addr).
               Seq.mem x (objects zero_addr (fst (coalesce g))) ==>
               is_white x (fst (coalesce g)) \/ is_blue x (fst (coalesce g))))

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let coalesce_all_white_or_blue g =
  coalesce_heap_unfold g g (objects zero_addr g) 0UL 0 0UL;
  let g' = fst (coalesce g) in
  assert (g' == coalesce_heap g g (objects zero_addr g) 0UL 0 0UL);
  let aux (x: obj_addr)
    : Lemma (requires Seq.mem x (objects zero_addr g'))
            (ensures is_white x g' \/ is_blue x g')
    = coalesce_aux_walk_all_wb g g zero_addr (objects zero_addr g) 0UL 0 0UL (objects zero_addr g) x;
      // walk_all_wb gives: (mem x (objects zero_addr g) /\ is_white x g) \/ is_blue x g'
      // White case: coalesce preserves white headers → is_white x g'
      if Seq.mem x (objects zero_addr g) && is_white x g then begin
        coalesce_preserves_survivor_header g x;
        color_of_header_eq x g g'
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// Well-formedness (stronger precondition needed)
/// ---------------------------------------------------------------------------

let post_sweep_strong (g: heap) : prop =
  post_sweep g /\
  (forall (x: obj_addr) (i: nat).
    Seq.mem x (objects zero_addr g) /\ is_white x g /\ fields_constrained g x /\
    i >= 1 /\ i <= U64.v (wosize_of_object x g) /\ i < pow2 64 ==>
    (let iu = U64.uint_to_t i in
     let field_val = HeapGraph.get_field g x iu in
     U64.v field_val < U64.v zero_addr + U64.v mword \/
     U64.v field_val >= heap_size \/
     U64.v field_val % U64.v mword <> 0 \/
     ~(Seq.mem (GC.Spec.Object.resolve_object (field_val <: obj_addr) g) (objects zero_addr g) /\
       is_blue (GC.Spec.Object.resolve_object (field_val <: obj_addr) g) g)))

val coalesce_preserves_wf (g: heap)
  : Lemma
    (requires post_sweep_strong g)
    (ensures well_formed_heap (fst (coalesce g)))

/// Free-list cells hold no interior pointers after coalescing.
///
/// This is the *establishment* half of `GC.Spec.Fields.blue_fields_non_infix`,
/// which `GC.Gen.HeapInvariant.major_heap_shape` carries.  It is true for a
/// concrete, operational reason rather than by luck: `flush_blue` zeroes every
/// field of a merged free block above the link word (see `Alloc.zero_fields` in
/// its definition, extracted as `zero_fields_loop`), so a blue cell's only
/// pointer-shaped field is its free-list link -- an object address, never an
/// interior one.
///
/// Without the zeroing this would be *false*: a dying object may hold interior
/// pointers, and sweep alone (`GC.Spec.Sweep.sweep_object`) rewrites only the
/// link word, leaving the rest of the corpse intact.
val coalesce_blue_fields_non_infix (g: heap)
  : Lemma
    (requires post_sweep_strong g)
    (ensures blue_fields_non_infix (fst (coalesce g)))

/// Every free block left by the coalescing pass is scannable: `flush_blue`
/// writes a fresh header with tag 0 for each merged run.
val coalesce_blue_blocks_scannable (g: heap)
  : Lemma
    (requires post_sweep_strong g)
    (ensures blue_blocks_scannable (fst (coalesce g)))

/// ---------------------------------------------------------------------------
/// coalesce_preserves_wf proof helpers
/// ---------------------------------------------------------------------------

/// Arithmetic: efptu field address doesn't overflow for obj_addr indices
#push-options "--z3rlimit 25"
private let efptu_field_addr_arith (h: obj_addr) (idx: U64.t{U64.v idx < pow2 54})
  : Lemma (
      U64.v (U64.mul_mod idx mword) == U64.v idx * U64.v mword /\
      U64.v (U64.add_mod h (U64.mul_mod idx mword)) == U64.v h + U64.v idx * U64.v mword)
  = FStar.Math.Lemmas.pow2_plus 54 3;
    assert ((pow2 54 * pow2 3) == pow2 57);
    assert ((U64.v idx * U64.v mword) < pow2 57);
    FStar.Math.Lemmas.pow2_lt_compat 64 57;
    FStar.Math.Lemmas.modulo_lemma ((U64.v idx * U64.v mword)) (pow2 64);
    FStar.Math.Lemmas.pow2_double_sum 57;
    FStar.Math.Lemmas.pow2_lt_compat 64 58;
    FStar.Math.Lemmas.modulo_lemma (U64.v h + U64.v idx * U64.v mword) (pow2 64)
#pop-options

/// Blue objects after coalescing satisfy the size bound (part1).
/// Admitted: proving this requires reasoning about merged block sizes.
#push-options "--z3rlimit 12"
private let coalesce_blue_size_bound (g: heap) (obj: obj_addr)
  : Lemma
    (requires
      post_sweep_strong g /\
      Seq.mem obj (objects zero_addr (fst (coalesce g))) /\
      is_blue obj (fst (coalesce g)))
    (ensures (
      let g' = fst (coalesce g) in
      let wz = wosize_of_object obj g' in
      U64.v (hd_address obj) + 8 + U64.v wz * 8 <= Seq.length g'))
  = let g' = fst (coalesce g) in
    coalesce_preserves_length g;
    objects_member_size_bound zero_addr g' obj;
    hd_address_spec obj;
    wosize_of_object_spec obj g'

#pop-options

/// ---------------------------------------------------------------------------
/// Property C: blue objects in coalesced walk have tag 0
/// ---------------------------------------------------------------------------

/// For any object in the coalesced walk that is blue, tag_of_object = 0UL.
/// Corollary of the merged walk lemma coalesce_aux_walk_all_wb_tag.
val coalesce_aux_blue_tag_zero
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr) (y: obj_addr)
  : Lemma
    (requires
      walk_pre g0 g start objs all_objs first_blue run_words /\
      (run_words > 0 ==> Seq.mem (first_blue <: obj_addr) all_objs) /\
      (forall (addr: hp_addr). U64.v addr >= U64.v start ==>
        read_word g addr == read_word g0 addr) /\
      (let sync : hp_addr =
         if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
       Seq.mem y (objects sync (coalesce_heap g0 g objs first_blue run_words fp))) /\
      is_blue y (coalesce_heap g0 g objs first_blue run_words fp))
    (ensures tag_of_object y (coalesce_heap g0 g objs first_blue run_words fp) == 0UL)

let coalesce_aux_blue_tag_zero g0 g start objs first_blue run_words fp all_objs y =
  coalesce_aux_walk_all_wb_tag g0 g start objs first_blue run_words fp all_objs y

/// Blue objects after coalescing are not infix (tag = 0, not infix_tag).
#push-options "--z3rlimit 25 --fuel 1 --ifuel 1"
private let coalesce_blue_not_infix (g: heap) (obj: obj_addr)
  : Lemma
    (requires
      post_sweep_strong g /\
      Seq.mem obj (objects zero_addr (fst (coalesce g))) /\
      is_blue obj (fst (coalesce g)))
    (ensures ~(is_infix obj (fst (coalesce g))))
  = let g' = fst (coalesce g) in
    coalesce_heap_unfold g g (objects zero_addr g) 0UL 0 0UL;
    assert (g' == coalesce_heap g g (objects zero_addr g) 0UL 0 0UL);
    coalesce_aux_blue_tag_zero g g zero_addr (objects zero_addr g) 0UL 0 0UL (objects zero_addr g) obj;
    assert (tag_of_object obj g' == 0UL);
    is_infix_spec obj g';
    infix_tag_val ()
#pop-options

/// zero_fields produces 0 when reading within the zeroed range
private let rec zero_fields_read_within (g: heap) (start: U64.t) (n: nat) (addr: hp_addr)
  : Lemma
    (requires
      U64.v start + n * U64.v mword <= heap_size /\
      U64.v start % U64.v mword == 0 /\
      U64.v addr >= U64.v start /\
      U64.v addr < U64.v start + n * U64.v mword /\
      U64.v addr % U64.v mword == 0)
    (ensures read_word (Alloc.zero_fields g start n) addr == 0UL)
    (decreases n)
  = if n = 0 then ()
    else begin
      assert (U64.v start + 8 <= heap_size);
      assert (U64.v start < heap_size);
      assert (U64.v start % 8 == 0);
      let g' = write_word g (start <: hp_addr) 0UL in
      if U64.v addr = U64.v start then begin
        // addr = start: read from g' at start gives 0UL, then zero_fields preserves it
        read_write_same g (start <: hp_addr) 0UL;
        if U64.v start + 8 >= pow2 64 then ()
        else begin
          let next = U64.uint_to_t (U64.v start + 8) in
          zero_fields_preserves_before g' next (n - 1) addr
        end
      end else begin
        // addr > start: recurse
        assert (U64.v start + 8 < pow2 64);
        let next = U64.uint_to_t (U64.v start + 8) in
        read_write_different g (start <: hp_addr) addr 0UL;
        zero_fields_read_within g' next (n - 1) addr
      end
    end

/// flush_blue produces 0 when reading fields 2..wosize of the merged block
private let flush_blue_field_zero
  (g: heap) (first_blue: obj_addr) (run_words: nat) (fp: U64.t)
  (addr: hp_addr)
  : Lemma
    (requires
      run_words >= 3 /\
      run_words - 1 < pow2 54 /\
      U64.v (hd_address first_blue) + run_words * U64.v mword <= heap_size /\
      Seq.length g == heap_size /\
      U64.v addr >= U64.v first_blue + U64.v mword /\
      U64.v addr < U64.v first_blue + (run_words - 1) * U64.v mword /\
      U64.v addr % U64.v mword == 0)
    (ensures read_word (fst (flush_blue g first_blue run_words fp)) addr == 0UL)
  = let fb = first_blue in
    let hd = hd_address fb in
    hd_address_spec fb;
    let wz = run_words - 1 in
    assert (wz >= 2);
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    let wz_u64 : wosize = U64.uint_to_t wz in
    let hdr = makeHeader wz_u64 Blue 0UL in
    let g1 = write_word g hd hdr in
    assert (wz >= 1 /\ U64.v hd + U64.v mword * 2 <= heap_size);
    assert (U64.v (hd_address fb) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
    let g2 = HeapGraph.set_field g1 fb 1UL fp in
    let zero_start_nat = U64.v fb + U64.v mword in
    assert (zero_start_nat < pow2 64);
    let zero_start = U64.uint_to_t zero_start_nat in
    // addr is in the zero_fields range [fb + mword, fb + mword + (wz-1)*mword)
    assert (U64.v addr >= U64.v zero_start);
    assert (U64.v addr < U64.v zero_start + (wz - 1) * U64.v mword);
    zero_fields_read_within g2 zero_start (wz - 1) addr

/// flush_blue field 1 value: after flush with run_words >= 2, field 1 = fp
/// Exported: `GC.Spec.Coalesce.Descending` needs the link word of a merged
/// block to establish that the rebuilt free list runs downhill.
let flush_blue_field1_spec
  (g: heap) (first_blue: obj_addr) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      run_words >= 2 /\
      run_words - 1 < pow2 54 /\
      U64.v (hd_address first_blue) + run_words * U64.v mword <= heap_size /\
      Seq.length g == heap_size)
    (ensures read_word (fst (flush_blue g first_blue run_words fp)) first_blue == fp)
  = let fb = first_blue in
    let hd = hd_address fb in
    hd_address_spec fb;
    let wz = run_words - 1 in
    assert (wz >= 1);
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    let wz_u64 : wosize = U64.uint_to_t wz in
    let hdr = makeHeader wz_u64 Blue 0UL in
    let g1 = write_word g hd hdr in
    assert (U64.v hd + U64.v mword * 2 <= heap_size);
    assert (U64.v (hd_address fb) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
    let field1_addr : hp_addr = U64.add (hd_address fb) (U64.mul mword 1UL) in
    assert (U64.v field1_addr == U64.v fb);
    read_write_different g hd field1_addr hdr;
    let g2 = HeapGraph.set_field g1 fb 1UL fp in
    read_write_same g1 field1_addr fp;
    let zero_start_nat = U64.v fb + U64.v mword in
    if wz >= 2 && zero_start_nat < pow2 64 then begin
      let zero_start = U64.uint_to_t zero_start_nat in
      assert (U64.v field1_addr + U64.v mword <= U64.v zero_start);
      zero_fields_preserves_before g2 zero_start (wz - 1) field1_addr
    end else ()

/// efptu elimination for blue objects: if fields 1..wz-1 are 0 and efptu holds,
/// then field 0 must point to dst (i.e., read_word g' src is a pointer to dst)
private let rec efptu_blue_elim
  (g': heap) (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54 /\ wz <> 0UL}) (dst: obj_addr)
  : Lemma
    (requires
      exists_field_pointing_to_unchecked g' src wz dst /\
      (forall (k: nat{k >= 1 /\ k < U64.v wz}).
        (let far = U64.add_mod src (U64.mul_mod (U64.uint_to_t k) mword) in
         U64.v far < heap_size /\ U64.v far % 8 == 0 ==>
         read_word g' (far <: hp_addr) == 0UL)))
    (ensures (
      let far0 = U64.add_mod src (U64.mul_mod 0UL mword) in
      U64.v far0 < heap_size /\ U64.v far0 % 8 == 0 /\
      is_pointer_to (read_word g' (far0 <: hp_addr)) dst))
    (decreases U64.v wz)
  = let idx = U64.sub wz 1UL in
    efptu_field_addr_arith src idx;
    let far = U64.add_mod src (U64.mul_mod idx mword) in
    if U64.v far >= heap_size || U64.v far % 8 <> 0 then ()
    else begin
      let fv = read_word g' (far <: hp_addr) in
      if is_pointer_to fv dst then begin
        // This field matched. But if idx >= 1, fv should be 0UL — contradiction
        if U64.v idx >= 1 then begin
          assert (read_word g' (far <: hp_addr) == 0UL);
          // is_pointer_to 0UL dst requires is_pointer_field 0UL
          // is_pointer_field 0UL = is_pointer 0UL = (0 >= 8 && ...) = false
          assert (is_pointer_to 0UL dst = false)
        end
        else begin
          // idx = 0: far = src + 0 = src. This is the field 0 case.
          assert (U64.v idx == 0);
          assert (U64.v far == U64.v src)
        end
      end
      else begin
        // Field at idx didn't match, recurse
        if idx = 0UL then ()  // wz was 1, didn't match, and recursion base: contradiction
        else begin
          // Show precondition for recursive call
          efptu_blue_elim g' src idx dst
        end
      end
    end

/// Walk lemma: blue merged blocks have valid field 0 and zero higher fields.
/// Proven below (after flush_blue_fb_in_walk).
val coalesce_aux_blue_field0_valid
  (g0 g: heap) (start: hp_addr) (objs all_objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t) (src: obj_addr)
  : Lemma
    (requires
      walk_pre g0 g start objs all_objs first_blue run_words /\
      (forall (addr: hp_addr). U64.v addr >= U64.v start ==>
        read_word g addr == read_word g0 addr) /\
      (let g' = coalesce_heap g0 g objs first_blue run_words fp in
       let sync : hp_addr =
         if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
       Seq.mem src (objects sync g') /\
       is_blue src g' /\
       U64.v (wosize_of_object src g') >= 1))
    (ensures (
      let g' = coalesce_heap g0 g objs first_blue run_words fp in
      let sync : hp_addr =
        if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
      let wz_src = wosize_of_object src g' in
      let fv = read_word g' src in
      (fv == 0UL \/ fv == fp \/
       (U64.v fv >= U64.v mword /\ U64.v fv < heap_size /\
        U64.v fv % U64.v mword == 0 /\
        Seq.mem (fv <: obj_addr) (objects sync g'))) /\
      (forall (k: nat). k >= 1 /\ k < U64.v wz_src ==>
        (U64.v src + k * 8 < heap_size ==>
         read_word g' (U64.uint_to_t (U64.v src + k * 8) <: hp_addr) == 0UL))))
    (decreases Seq.length objs)

/// Helper: prove field 0 of the merged block is preserved through tail walk.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let merged_block_field0_preserved
  (g0 g_flush: heap) (next: hp_addr) (tail_objs: seq obj_addr)
  (fp_flush: U64.t)
  (first_blue: obj_addr) (run_words: nat{run_words >= 2})
  (fp: U64.t)
  (g: heap)
  : Lemma
    (requires
      Seq.length g0 == heap_size /\
      Seq.length g == heap_size /\
      Seq.length g_flush == heap_size /\
      tail_objs == objects next g0 /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v (hd_address first_blue) + run_words * U64.v mword <= heap_size /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword <= U64.v next /\
      g_flush == fst (flush_blue g first_blue run_words fp) /\
      fp_flush == snd (flush_blue g first_blue run_words fp))
    (ensures
      read_word (coalesce_heap g0 g_flush tail_objs 0UL 0 fp_flush)
        (first_blue <: hp_addr) == fp)
  = hd_address_spec first_blue;
    flush_blue_field1_spec g first_blue run_words fp;
    assert (read_word g_flush (first_blue <: hp_addr) == fp);
    assert (U64.v first_blue + U64.v mword <= U64.v next);
    coalesce_heap_preserves_before_run_start g0 g_flush next tail_objs 0UL 0 fp_flush
      (first_blue <: hp_addr)
#pop-options

/// Helper: prove zero fields for the merged block are preserved through tail walk.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let merged_block_zero_field_preserved
  (g0 g_flush: heap) (next: hp_addr) (tail_objs: seq obj_addr)
  (fp_flush: U64.t)
  (first_blue: obj_addr) (run_words: nat{run_words >= 3})
  (fp: U64.t)
  (g: heap)
  (k: nat{k >= 1 /\ k < run_words - 1})
  : Lemma
    (requires
      Seq.length g0 == heap_size /\
      Seq.length g == heap_size /\
      Seq.length g_flush == heap_size /\
      tail_objs == objects next g0 /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v (hd_address first_blue) + run_words * U64.v mword <= heap_size /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword <= U64.v next /\
      g_flush == fst (flush_blue g first_blue run_words fp) /\
      fp_flush == snd (flush_blue g first_blue run_words fp) /\
      U64.v first_blue + k * U64.v mword < heap_size)
    (ensures
      read_word (coalesce_heap g0 g_flush tail_objs 0UL 0 fp_flush)
        (U64.uint_to_t (U64.v first_blue + k * U64.v mword) <: hp_addr) == 0UL)
  = let addr : hp_addr = U64.uint_to_t (U64.v first_blue + k * U64.v mword) in
    assert (U64.v addr >= U64.v first_blue + U64.v mword);
    assert (U64.v addr < U64.v first_blue + (run_words - 1) * U64.v mword);
    flush_blue_field_zero g first_blue run_words fp addr;
    assert (read_word g_flush addr == 0UL);
    assert (U64.v addr + U64.v mword <= U64.v next);
    coalesce_heap_preserves_before_run_start g0 g_flush next tail_objs 0UL 0 fp_flush addr
#pop-options

/// Helper: flush_blue's second component is either fp or first_blue (local copy)
private let flush_blue_snd_cases_local (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma (snd (flush_blue g first_blue run_words fp) == fp \/
           snd (flush_blue g first_blue run_words fp) == first_blue)
  = ()

/// Helper: when g' == flush result directly (tail empty, rest >= heap_size),
/// prove field0 validity and higher fields zero for src = first_blue.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let flush_only_blue_fields
  (g0 g g': heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: obj_addr) (run_words: pos) (fp: U64.t)
  (obj: obj_addr) (src: obj_addr)
  : Lemma
    (requires
      Seq.length g0 == heap_size /\
      Seq.length g == heap_size /\
      g' == fst (flush_blue g first_blue run_words fp) /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start /\
      run_words - 1 < pow2 54 /\
      // src = first_blue, blue, wosize >= 1
      src == first_blue /\
      Seq.length g' == heap_size /\
      is_blue src g' /\
      U64.v (wosize_of_object src g') >= 1 /\
      U64.v (wosize_of_object src g') == run_words - 1)
    (ensures
      (read_word g' src == fp) /\
      (forall (k: nat). k >= 1 /\ k < run_words - 1 ==>
        (U64.v src + k * 8 < heap_size ==>
         read_word g' (U64.uint_to_t (U64.v src + k * 8) <: hp_addr) == 0UL)))
  = hd_address_spec first_blue;
    flush_blue_field1_spec g first_blue run_words fp;
    if run_words >= 3 then begin
      let aux_zero (k: nat{k >= 1 /\ k < run_words - 1})
        : Lemma (U64.v src + k * 8 < heap_size ==>
                 read_word g' (U64.uint_to_t (U64.v src + k * 8) <: hp_addr) == 0UL)
        = if U64.v src + k * 8 < heap_size then begin
            let addr : hp_addr = U64.uint_to_t (U64.v src + k * 8) in
            assert (U64.v addr >= U64.v first_blue + U64.v mword);
            assert (U64.v addr < U64.v first_blue + (run_words - 1) * U64.v mword);
            assert (U64.v addr % U64.v mword == 0);
            flush_blue_field_zero g first_blue run_words fp addr
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_zero)
    end
#pop-options

/// Helper: white step, rest >= heap_size (tail empty) case for blue_field0_valid.
/// Factored out to keep the recursive function small for Z3.
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
private let blue_field0_white_tail_empty
  (g0 g: heap) (start: hp_addr) (objs all_objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t) (src: obj_addr)
  (obj: obj_addr) (rest_start_nat: nat)
  (g_flush: heap) (fp_flush: U64.t)
  : Lemma
    (requires
      walk_pre g0 g start objs all_objs first_blue run_words /\
      (forall (addr: hp_addr). U64.v addr >= U64.v start ==>
        read_word g addr == read_word g0 addr) /\
      Seq.length objs > 0 /\
      obj == f_address start /\
      obj == Seq.head objs /\
      is_white obj g0 /\
      rest_start_nat == U64.v start + (U64.v (getWosize (read_word g0 start)) + 1) * U64.v mword /\
      rest_start_nat >= heap_size /\
      (g_flush, fp_flush) == flush_blue g first_blue run_words fp /\
      Seq.length g_flush == heap_size /\
      (fp_flush == fp \/ fp_flush == first_blue) /\
      (let g' = coalesce_heap g0 g objs first_blue run_words fp in
       let sync : hp_addr =
         if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
       g' == g_flush /\
       Seq.mem src (objects sync g') /\
       is_blue src g' /\
       U64.v (wosize_of_object src g') >= 1))
    (ensures (
      let g' = coalesce_heap g0 g objs first_blue run_words fp in
      let sync : hp_addr =
        if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
      let wz_src = wosize_of_object src g' in
      let fv = read_word g' src in
      (fv == 0UL \/ fv == fp \/
       (U64.v fv >= U64.v mword /\ U64.v fv < heap_size /\
        U64.v fv % U64.v mword == 0 /\
        Seq.mem (fv <: obj_addr) (objects sync g'))) /\
      (forall (k: nat). k >= 1 /\ k < U64.v wz_src ==>
        (U64.v src + k * 8 < heap_size ==>
         read_word g' (U64.uint_to_t (U64.v src + k * 8) <: hp_addr) == 0UL))))
  = let g' = coalesce_heap g0 g objs first_blue run_words fp in
    if run_words > 0 then begin
      run_words_bound first_blue run_words start;
      hd_address_spec (first_blue <: obj_addr);
      flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
      let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
      merged_block_decompose g' (first_blue <: obj_addr) run_words start src;
      if src <> (first_blue <: obj_addr) then begin
        flush_blue_preserves_outside g first_blue run_words fp start;
        assert (read_word g_flush start == read_word g start);
        assert (read_word g_flush start == read_word g0 start);
        assert (g' == g_flush);
        assert (read_word g' start == read_word g0 start);
        // objects start g' is nonempty (same header as g0 at start)
        objects_nonempty_at start g' g0;
        // Tail of objects start g' is empty (rest_start_nat >= heap_size)
        // Since read_word g' start == read_word g0 start, same wosize, same next
        objects_tail_empty_when_done start g';
        // So objects start g' == [obj]
        objects_nonempty_next start g';
        f_address_spec start;
        mem_cons_lemma src (f_address start) (Seq.tail (objects start g'));
        assert (Seq.mem src (objects start g'));
        // src is in [obj] and tail is empty, so src == obj
        assert (Seq.length (Seq.tail (objects start g')) == 0);
        assert (src == obj);
        // obj is white in g0; header preserved → white in g'; but src is blue: contradiction
        hd_f_roundtrip start;
        assert (read_word g' (hd_address obj) == read_word g0 (hd_address obj));
        color_of_header_eq obj g0 g';
        // color_of_header_eq gives is_white obj g' == is_white obj g0
        // and is_blue obj g' == is_blue obj g0
        // Since obj white in g0 → obj white in g' → obj not blue in g'
        // But src == obj and src blue in g': contradiction
        is_blue_iff obj g0;
        is_white_iff obj g0;
        // color_of_object obj g0 = White, so is_blue obj g0 = false
        // By color_of_header_eq, is_blue obj g' = is_blue obj g0 = false
        // But src = obj and is_blue src g' is true: contradiction
        assert (is_blue obj g' == false)
      end;
      assert (src = (first_blue <: obj_addr));
      makeHeader_getWosize wz_u64 Blue 0UL;
      wosize_of_object_spec src g';
      flush_blue_preserves_length g first_blue run_words fp;
      flush_only_blue_fields g0 g g' start objs (first_blue <: obj_addr) run_words fp obj src
    end
    else begin
      // run_words = 0: flush_blue is no-op, g' == g
      // objects start g' == objects start g0 == [obj] (since rest >= heap_size)
      // obj is white, src is blue → contradiction (src can't be in [obj])
      objects_nonempty_at start g' g0;
      objects_tail_empty_when_done start g';
      objects_nonempty_next start g';
      f_address_spec start;
      mem_cons_lemma src (f_address start) (Seq.tail (objects start g'));
      assert (Seq.length (Seq.tail (objects start g')) == 0);
      assert (src == obj);
      hd_f_roundtrip start;
      color_of_header_eq obj g0 g';
      is_blue_iff obj g0;
      is_white_iff obj g0
    end
#pop-options

#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
let rec coalesce_aux_blue_field0_valid g0 g start objs all_objs first_blue run_words fp src =
  let g' = coalesce_heap g0 g objs first_blue run_words fp in
  let sync : hp_addr =
    if run_words > 0 then hd_address (first_blue <: obj_addr) else start in

  if Seq.length objs = 0 then begin
    assert (Seq.equal objs Seq.empty);
    coalesce_heap_empty g0 g first_blue run_words fp;
    assert (g' == fst (flush_blue g first_blue run_words fp));
    if run_words = 0 then ()
    else begin
      run_words_bound first_blue run_words start;
      hd_address_spec (first_blue <: obj_addr);
      flush_blue_preserves_length g first_blue run_words fp;
      flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
      let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
      makeHeader_getWosize wz_u64 Blue 0UL;
      f_address_spec sync;
      merged_block_decompose g' (first_blue <: obj_addr) run_words start src;
      // src must be first_blue: tail of (objects sync g') == objects start g'
      // and U64.v start may be < heap_size (where objects start g' may have things)
      // BUT: read_word g' start == read_word g start == read_word g0 start (since flush
      // preserves at start, end of merged region). And objs == empty means
      // objects start g0 == empty.
      if src <> (first_blue <: obj_addr) then begin
        if U64.v start < heap_size then begin
          flush_blue_preserves_outside g first_blue run_words fp start;
          assert (read_word g' start == read_word g start);
          assert (read_word g' start == read_word g0 start);
          // objects start g0 == objs == Seq.empty
          assert (Seq.length (objects start g0) == 0);
          // header at start in g0 has wz with rest_start_nat >= heap_size (since otherwise
          // objects start g0 would be nonempty). Actually objects start g0 is empty means
          // start position has wosize that would push past heap_size, OR... Actually at the
          // top-level we have objs == objects start g0 == Seq.empty, which is well-defined
          // when start has no valid object. The objects function at start with empty result
          // means the cell at start can't form a valid object beginning.
          // We need: objects start g' is also empty (same header).
          assert (Seq.equal (objects start g') (objects start g0));
          assert (Seq.length (objects start g') == 0);
          // But merged_block_decompose says mem src (objects start g'), contradiction
          ()
        end
      end;
      assert (src = (first_blue <: obj_addr));
      wosize_of_object_spec src g';
      assert (run_words >= 2);
      flush_blue_field1_spec g (first_blue <: obj_addr) run_words fp;
      if run_words >= 3 then begin
        let aux_zero (k: nat{k >= 1 /\ k < run_words - 1})
          : Lemma (U64.v src + k * 8 < heap_size ==>
                   read_word g' (U64.uint_to_t (U64.v src + k * 8) <: hp_addr) == 0UL)
          = if U64.v src + k * 8 < heap_size then
              flush_blue_field_zero g (first_blue <: obj_addr) run_words fp
                (U64.uint_to_t (U64.v src + k * 8) <: hp_addr)
            else ()
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_zero)
      end
    end
  end
  else begin
    objects_nonempty_next start g0;
    let header = read_word g0 start in
    let wz = getWosize header in
    let obj = f_address start in
    f_address_spec start;
    hd_address_spec obj;
    let rest_start_nat = U64.v start + (U64.v wz + 1) * U64.v mword in
    assert (obj == Seq.head objs);
    Seq.cons_head_tail objs;
    wosize_of_object_spec obj g0;
    let ws = U64.v (wosize_of_object obj g0) in

    let tail_sub (o: obj_addr)
      : Lemma (Seq.mem o (Seq.tail objs) ==> Seq.mem o all_objs)
      = mem_cons_lemma o obj (Seq.tail objs)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires tail_sub);

    if is_blue obj g0 then begin
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      let new_rw = run_words + ws + 1 in

      let tail_white_inv (o: obj_addr)
        : Lemma (Seq.mem o (Seq.tail objs) /\ is_white o g0 ==>
                 read_word g (hd_address o) == read_word g0 (hd_address o))
        = mem_cons_lemma o obj (Seq.tail objs)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires tail_white_inv);

      coalesce_heap_blue_step g0 g objs first_blue run_words fp;

      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        coalesce_aux_blue_field0_valid g0 g next (Seq.tail objs) all_objs
          new_first new_rw fp src
      end
      else begin
        // tail is empty; inline the empty-case proof with new_first/new_rw
        objects_tail_empty_when_done start g0;
        assert (Seq.equal (Seq.tail objs) Seq.empty);
        coalesce_heap_empty g0 g new_first new_rw fp;
        assert (g' == fst (flush_blue g new_first new_rw fp));
        // new_rw >= 1
        assert (new_rw >= 1);
        // Bound: new_rw - 1 < pow2 54
        hd_address_spec (new_first <: obj_addr);
        let new_sync : hp_addr =
          if run_words > 0 then hd_address (first_blue <: obj_addr)
          else hd_address (obj <: obj_addr) in
        // sync (computed at outer call) == new_sync after blue step
        if run_words > 0 then assert (new_first == first_blue)
        else assert (new_first == obj);
        let total_size_nat = U64.v (hd_address (new_first <: obj_addr)) + new_rw * U64.v mword in
        assert (total_size_nat == rest_start_nat);
        assert (rest_start_nat <= heap_size);
        assert (new_rw * U64.v mword <= heap_size);
        FStar.Math.Lemmas.lemma_div_le (new_rw * U64.v mword) (pow2 57) (U64.v mword);
        assert_norm (pow2 57 = pow2 54 * 8);
        FStar.Math.Lemmas.cancel_mul_div new_rw (U64.v mword);
        assert (new_rw - 1 < pow2 54);
        flush_blue_preserves_length g new_first new_rw fp;
        flush_blue_header_spec g (new_first <: obj_addr) new_rw fp;
        let wz_u64 : wosize = U64.uint_to_t (new_rw - 1) in
        makeHeader_getWosize wz_u64 Blue 0UL;
        f_address_spec (hd_address (new_first <: obj_addr));
        // src must be new_first
        merged_block_decompose g' (new_first <: obj_addr) new_rw
          (U64.uint_to_t rest_start_nat <: U64.t) src;
        assert (src = (new_first <: obj_addr));
        wosize_of_object_spec src g';
        assert (new_rw >= 2);
        flush_blue_field1_spec g (new_first <: obj_addr) new_rw fp;
        if new_rw >= 3 then begin
          let aux_zero (k: nat{k >= 1 /\ k < new_rw - 1})
            : Lemma (U64.v src + k * 8 < heap_size ==>
                     read_word g' (U64.uint_to_t (U64.v src + k * 8) <: hp_addr) == 0UL)
            = if U64.v src + k * 8 < heap_size then
                flush_blue_field_zero g (new_first <: obj_addr) new_rw fp
                  (U64.uint_to_t (U64.v src + k * 8) <: hp_addr)
              else ()
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires aux_zero)
        end
      end
    end
    else begin
      // White step
      mem_cons_lemma obj obj (Seq.tail objs);
      is_blue_iff obj g0; is_white_iff obj g0;
      assert (is_white obj g0);

      let (g_flush, fp_flush) = flush_blue g first_blue run_words fp in
      flush_blue_preserves_length g first_blue run_words fp;
      flush_blue_snd_cases_local g first_blue run_words fp;
      assert (fp_flush == fp \/ fp_flush == first_blue);

      coalesce_heap_white_step g0 g objs first_blue run_words fp g_flush fp_flush;
      coalesce_heap_preserves_length g0 g_flush (Seq.tail objs) 0UL 0 fp_flush;

      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);

        let flush_white_hdr_inv (o: obj_addr)
          : Lemma
            (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
            (ensures read_word g_flush (hd_address o) == read_word g0 (hd_address o))
          = mem_cons_lemma o obj (Seq.tail objs);
            objects_addresses_gt_start next g0 o;
            hd_address_spec o;
            flush_blue_preserves_outside g first_blue run_words fp (hd_address o)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires flush_white_hdr_inv);

        let flush_ge_next (addr: hp_addr)
          : Lemma (requires U64.v addr >= U64.v next)
                  (ensures read_word g_flush addr == read_word g0 addr)
          = flush_blue_preserves_outside g first_blue run_words fp addr
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires flush_ge_next);

        if run_words > 0 then begin
          run_words_bound first_blue run_words start;
          hd_address_spec (first_blue <: obj_addr);
          coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
            0UL 0 fp_flush (hd_address (first_blue <: obj_addr));
          flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
          let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in

          merged_block_decompose g' (first_blue <: obj_addr) run_words start src;

          if src = (first_blue <: obj_addr) then begin
            makeHeader_getWosize wz_u64 Blue 0UL;
            wosize_of_object_spec src g';
            assert (run_words >= 2);
            merged_block_field0_preserved g0 g_flush next (Seq.tail objs)
              fp_flush (first_blue <: obj_addr) run_words fp g;
            if run_words >= 3 then begin
              let aux_zero (k: nat{k >= 1 /\ k < run_words - 1})
                : Lemma (U64.v src + k * 8 < heap_size ==>
                         read_word g' (U64.uint_to_t (U64.v src + k * 8) <: hp_addr) == 0UL)
                = if U64.v src + k * 8 < heap_size then
                    merged_block_zero_field_preserved g0 g_flush next (Seq.tail objs)
                      fp_flush (first_blue <: obj_addr) run_words fp g k
                  else ()
              in
              FStar.Classical.forall_intro (FStar.Classical.move_requires aux_zero)
            end
          end
          else begin
            // src != first_blue, so src ∈ objects start g'
            // src can't be obj (obj is white in g0 ⇒ white in g'; but src is blue) — IH applies
            flush_blue_preserves_outside g first_blue run_words fp start;
            white_addr_outside_all_blue g0 obj start;
            coalesce_heap_preserves_outside g0 g_flush next (Seq.tail objs)
              0UL 0 fp_flush all_objs start;
            objects_nonempty_at start g' g0;
            objects_nonempty_next start g';
            f_address_spec start;
            mem_cons_lemma src (f_address start) (Seq.tail (objects start g'));
            Seq.lemma_tl obj (objects next g');

            if src = obj then begin
              coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
                0UL 0 fp_flush (hd_address obj);
              flush_blue_preserves_outside g first_blue run_words fp (hd_address obj);
              color_of_header_eq obj g0 g';
              is_blue_iff obj g'; is_white_iff obj g0
            end
            else begin
              assert (Seq.mem src (objects next g'));
              coalesce_aux_blue_field0_valid g0 g_flush next (Seq.tail objs) all_objs
                0UL 0 fp_flush src;
              let fv = read_word g' src in
              if fv = 0UL then ()
              else if fv = fp then ()
              else begin
                if fv = fp_flush then begin
                  // fp_flush <> fp, so fp_flush == first_blue, hence fv == first_blue
                  merged_block_step g' (first_blue <: obj_addr) run_words start
                    (first_blue <: obj_addr)
                end
                else begin
                  // bounds /\ mem fv (objects next g')
                  objects_later_subset start g' (fv <: obj_addr);
                  merged_block_step g' (first_blue <: obj_addr) run_words start
                    (fv <: obj_addr)
                end
              end
            end
          end
        end
        else begin
          // run_words = 0
          flush_blue_preserves_outside g first_blue run_words fp start;
          white_addr_outside_all_blue g0 obj start;
          coalesce_heap_preserves_outside g0 g_flush next (Seq.tail objs)
            0UL 0 fp_flush all_objs start;
          objects_nonempty_at start g' g0;
          objects_nonempty_next start g';
          f_address_spec start;
          mem_cons_lemma src (f_address start) (Seq.tail (objects start g'));
          Seq.lemma_tl obj (objects next g');

          if src = obj then begin
            coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
              0UL 0 fp_flush (hd_address obj);
            flush_blue_preserves_outside g first_blue run_words fp (hd_address obj);
            color_of_header_eq obj g0 g';
            is_blue_iff obj g'; is_white_iff obj g0
          end
          else begin
            assert (Seq.mem src (objects next g'));
            coalesce_aux_blue_field0_valid g0 g_flush next (Seq.tail objs) all_objs
              0UL 0 fp_flush src;
            // run_words = 0: flush_blue is a no-op, so fp_flush == fp, g_flush == g
            let fv = read_word g' src in
            if fv = 0UL then ()
            else if fv = fp_flush then ()
            else
              objects_later_subset start g' (fv <: obj_addr)
          end
        end
      end
      else begin
        // rest_start_nat >= heap_size: tail is empty
        objects_tail_empty_when_done start g0;
        assert (Seq.equal (Seq.tail objs) Seq.empty);
        Seq.lemma_eq_elim (Seq.tail objs) (Seq.empty #obj_addr);
        assert (Seq.tail objs == Seq.empty);
        coalesce_heap_empty g0 g_flush 0UL 0 fp_flush;
        assert (g' == g_flush);
        blue_field0_white_tail_empty g0 g start objs all_objs first_blue run_words fp src
          obj rest_start_nat g_flush fp_flush
      end
    end
  end
#pop-options


/// Blue source objects after coalescing: if efptu g' src wz dst, then dst in objects g'.
#push-options "--z3rlimit 25 --fuel 1 --ifuel 1"
let coalesce_blue_field_closure (g: heap) (src dst: obj_addr)
  : Lemma
    (requires
      post_sweep_strong g /\
      Seq.mem src (objects zero_addr (fst (coalesce g))) /\
      is_blue src (fst (coalesce g)) /\
      (let g' = fst (coalesce g) in
       let wz = wosize_of_object src g' in
       U64.v wz < pow2 54 /\
       exists_field_pointing_to_unchecked g' src wz dst))
    (ensures Seq.mem dst (objects zero_addr (fst (coalesce g))))
  = let g' = fst (coalesce g) in
    let wz = wosize_of_object src g' in
    coalesce_heap_unfold g g (objects zero_addr g) 0UL 0 0UL;
    assert (g' == coalesce_heap g g (objects zero_addr g) 0UL 0 0UL);
    coalesce_preserves_length g;
    // wz >= 1 since efptu requires a matching field at idx in [0, wz)
    assert (wz <> 0UL);
    assert (U64.v wz >= 1);
    coalesce_aux_blue_field0_valid g g zero_addr (objects zero_addr g) (objects zero_addr g) 0UL 0 0UL src;
    // fp = 0UL, sync = 0UL, so the disjunct simplifies
    let fv = read_word g' src in
    // Bridge zero-field hypothesis to efptu_blue_elim's expected form
    let zero_fields_hyp (k: nat{k >= 1 /\ k < U64.v wz})
      : Lemma (let far = U64.add_mod src (U64.mul_mod (U64.uint_to_t k) mword) in
               U64.v far < heap_size /\ U64.v far % 8 == 0 ==>
               read_word g' (far <: hp_addr) == 0UL)
      = efptu_field_addr_arith src (U64.uint_to_t k)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires zero_fields_hyp);
    efptu_blue_elim g' src wz dst;
    // efptu_blue_elim ensures: is_pointer_to (read_word g' (far0 <: hp_addr)) dst
    // where far0 = src + 0 == src
    efptu_field_addr_arith src 0UL;
    let far0 = U64.add_mod src (U64.mul_mod 0UL mword) in
    assert (U64.v far0 == U64.v src);
    assert (is_pointer_to (read_word g' (far0 <: hp_addr)) dst);
    assert (read_word g' (far0 <: hp_addr) == fv);
    assert (is_pointer_to fv dst);
    // is_pointer_to fv dst => is_pointer_field fv (so fv >= 8) and hd_address fv = hd_address dst
    assert (is_pointer_field fv);
    assert (U64.v fv >= U64.v mword);
    // fv != 0UL, so from the disjunction: bounds /\ mem fv (objects zero_addr g')
    assert (Seq.mem (fv <: obj_addr) (objects zero_addr g'));
    hd_address_spec (fv <: obj_addr);
    hd_address_spec dst;
    assert (hd_address fv == hd_address dst);
    assert (fv == dst)
#pop-options

/// Helper: if efptu g src wz dst and src is white and dst is blue, contradiction
/// from post_sweep_strong.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
private let rec coalesce_white_field_not_blue
  (g: heap) (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (dst: obj_addr)
  : Lemma
    (requires
      post_sweep_strong g /\
      Seq.mem src (objects zero_addr g) /\ is_white src g /\
      fields_constrained g src /\
      U64.v wz <= U64.v (wosize_of_object src g) /\
      exists_field_pointing_to_unchecked g src wz dst /\
      Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g) /\
      is_blue (GC.Spec.Object.resolve_object dst g) g)
    (ensures False)
    (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      efptu_field_addr_arith src idx;
      let far = U64.add_mod src (U64.mul_mod idx mword) in
      assert (U64.v far == U64.v src + U64.v idx * U64.v mword);
      hd_address_spec src;
      wf_object_size_bound g src;
      wosize_of_object_spec src g;
      wosize_of_object_bound src g;
      assert (U64.v far < heap_size);
      FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v src) (U64.v idx * U64.v mword) 8;
      assert (U64.v far % 8 == 0);
      let fv = read_word g (far <: hp_addr) in
      if is_pointer_to fv dst then begin
        hd_address_spec dst;
        hd_address_spec (fv <: obj_addr);
        assert (fv == dst);
        assert (U64.v fv >= U64.v mword);
        assert (U64.v fv < heap_size);
        assert (U64.v fv % U64.v mword == 0);
        // Show HeapGraph.get_field g src wz == fv
        let hd = hd_address src in
        assert (U64.v hd + U64.v mword * U64.v wz + U64.v mword <= heap_size);
        let field_addr = U64.add hd (U64.mul mword wz) in
        assert (U64.v field_addr == U64.v hd + U64.v mword * U64.v wz);
        assert (U64.v field_addr == U64.v src + U64.v idx * U64.v mword);
        assert (U64.v field_addr == U64.v far);
        assert (field_addr == far);
        assert (HeapGraph.get_field g src wz == read_word g (far <: hp_addr));
        assert (HeapGraph.get_field g src wz == fv);
        // Instantiate post_sweep_strong with i = U64.v wz
        let i : nat = U64.v wz in
        assert (i >= 1 /\ i <= U64.v (wosize_of_object src g) /\ i < pow2 64);
        assert (U64.uint_to_t i == wz);
        assert (Seq.mem (GC.Spec.Object.resolve_object (fv <: obj_addr) g) (objects zero_addr g) /\
                is_blue (GC.Spec.Object.resolve_object (fv <: obj_addr) g) g)
      end
      else begin
        coalesce_white_field_not_blue g src idx dst
      end
    end
#pop-options

/// Key recursive lemma: for white survivors, efptu on g' implies efptu on g.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
private let rec white_src_efptu_transfer
  (g: heap) (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (dst: obj_addr)
  : Lemma
    (requires
      post_sweep_strong g /\
      Seq.mem src (objects zero_addr g) /\ is_white src g /\
      U64.v wz <= U64.v (wosize_of_object src g) /\
      exists_field_pointing_to_unchecked (fst (coalesce g)) src wz dst)
    (ensures exists_field_pointing_to_unchecked g src wz dst)
    (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let g' = fst (coalesce g) in
      let idx = U64.sub wz 1UL in
      efptu_field_addr_arith src idx;
      let far = U64.add_mod src (U64.mul_mod idx mword) in
      assert (U64.v far == U64.v src + U64.v idx * U64.v mword);
      hd_address_spec src;
      wf_object_size_bound g src;
      wosize_of_object_spec src g;
      wosize_of_object_bound src g;
      assert (U64.v far < heap_size);
      FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v src) (U64.v idx * U64.v mword) 8;
      assert (U64.v far % 8 == 0);
      // far is within src's region
      assert (U64.v far >= U64.v (hd_address src));
      assert (U64.v far < U64.v (hd_address src) + (U64.v (wosize_of_object src g) + 1) * U64.v mword);
      // Read at far is preserved by coalescing
      white_addr_outside_all_blue g src (far <: hp_addr);
      coalesce_aux_preserves_outside g g zero_addr (objects zero_addr g) 0UL 0 0UL (objects zero_addr g) (far <: hp_addr);
      assert (read_word g' (far <: hp_addr) == read_word g (far <: hp_addr));
      let fv = read_word g (far <: hp_addr) in
      if is_pointer_to fv dst then
        efptu_match g src wz dst far fv
      else begin
        assert (exists_field_pointing_to_unchecked g' src idx dst);
        white_src_efptu_transfer g src idx dst;
        efptu_recurse g src wz dst far fv
      end
    end
#pop-options

/// Shared core: for a field target `dst` of a *white survivor* `src` in the
/// pre-coalesce heap, coalescing leaves the target's resolution alone and keeps
/// the resolved object enumerated.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
private let white_target_resolve_stable (g: heap) (src dst: obj_addr)
  : Lemma
    (requires
      post_sweep_strong g /\
      Seq.mem src (objects zero_addr g) /\ is_white src g /\
      fields_constrained g src /\
      (let wz = wosize_of_object src g in
       U64.v wz < pow2 54 /\
       exists_field_pointing_to_unchecked g src wz dst))
    (ensures (let g' = fst (coalesce g) in
              GC.Spec.Object.resolve_object dst g' == GC.Spec.Object.resolve_object dst g /\
              Seq.mem (GC.Spec.Object.resolve_object dst g') (objects zero_addr g') /\
              GC.Spec.Object.infix_addr_wf g' (objects zero_addr g') dst))
  = let g' = fst (coalesce g) in
    let wz = wosize_of_object src g in
    wosize_of_object_bound src g;
    // In g, well-formedness gives the resolved target in objects and part 3 at dst
    wf_field_target_in_objects g src dst;
    wf_field_target_infix_wf g src dst;
    let p : obj_addr = GC.Spec.Object.resolve_object dst g in
    assert (Seq.mem p (objects zero_addr g));
    // The enclosing object of the target cannot be a free block ...
    if is_blue p g then coalesce_white_field_not_blue g src wz dst;
    assert (~(is_blue p g));
    // ... hence it is a white survivor, whose header word coalesce leaves alone.
    assert (is_white p g);
    coalesce_survivors_in_objects g p;
    coalesce_preserves_survivor_header g p;
    GC.Spec.Object.resolve_object_locality p g g';
    // dst's own header is p's header when dst is not infix, and otherwise sits
    // at field index `wosize_of_object dst g` of the surviving closure p.
    if GC.Spec.Object.is_infix dst g then begin
      GC.Spec.Object.infix_addr_wf_elim g (objects zero_addr g) dst;
      GC.Spec.Object.resolve_infix_spec dst g;
      let w = wosize_of_object dst g in
      wosize_of_object_bound dst g;
      let pn = GC.Spec.Object.parent_closure_addr_nat dst g in
      GC.Spec.Object.parent_closure_addr_nat_spec dst g;
      assert (pn == U64.v dst - U64.v w * 8);
      assert (pn >= 8 /\ pn < heap_size);
      FStar.Math.Lemmas.pow2_lt_compat 64 61;
      assert (U64.v (U64.uint_to_t pn) == pn);
      assert (p == U64.uint_to_t pn);
      assert (U64.v p == U64.v dst - U64.v w * 8);
      assert (U64.v w < U64.v (wosize_of_object p g));
      hd_address_spec p;
      hd_address_spec dst;
      wf_object_size_bound g p;
      HeapGraph.get_field_addr_eq g p w;
      coalesce_preserves_survivor_field g p w;
      assert (HeapGraph.get_field g p w == read_word g (hd_address dst));
      assert (HeapGraph.get_field g' p w == read_word g' (hd_address dst))
    end else
      GC.Spec.Object.resolve_non_infix dst g;
    GC.Spec.Object.resolve_object_locality dst g g';
    GC.Spec.Object.infix_addr_wf_transfer g g' (objects zero_addr g) (objects zero_addr g') dst
#pop-options

/// For a white source in g', if efptu g' src wz dst, then dst's resolved target
/// is in objects zero_addr g'.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
private let white_src_field_closure (g: heap) (src dst: obj_addr)
  : Lemma
    (requires
      post_sweep_strong g /\
      Seq.mem src (objects zero_addr g) /\ is_white src g /\
      fields_constrained g src /\
      Seq.mem src (objects zero_addr (fst (coalesce g))) /\
      (let g' = fst (coalesce g) in
       let wz = wosize_of_object src g' in
       U64.v wz < pow2 54 /\
       exists_field_pointing_to_unchecked g' src wz dst))
    (ensures (let g' = fst (coalesce g) in
              Seq.mem (GC.Spec.Object.resolve_object dst g') (objects zero_addr g') /\
              GC.Spec.Object.infix_addr_wf g' (objects zero_addr g') dst))
  = let g' = fst (coalesce g) in
    coalesce_preserves_survivor_header g src;
    wosize_of_object_spec src g;
    wosize_of_object_spec src g';
    assert (wosize_of_object src g' == wosize_of_object src g);
    let wz = wosize_of_object src g in
    wosize_of_object_bound src g;
    // Transfer efptu from g' to g
    white_src_efptu_transfer g src wz dst;
    white_target_resolve_stable g src dst
#pop-options

/// Coalescing preserves how a white survivor's field resolves.
val coalesce_preserves_survivor_field_resolve
  (g: heap) (x: obj_addr) (j: U64.t{U64.v j >= 1})
  : Lemma
    (requires post_sweep_strong g /\
              Seq.mem x (objects zero_addr g) /\ is_white x g /\
              fields_constrained g x /\
              U64.v j <= U64.v (wosize_of_object x g))
    (ensures (let v = HeapGraph.get_field g x j in
              HeapGraph.resolve_field g v ==
              HeapGraph.resolve_field (fst (coalesce g)) v))

#push-options "--z3rlimit 60 --fuel 1 --ifuel 0"
let coalesce_preserves_survivor_field_resolve g x j
  = let g' = fst (coalesce g) in
    let v = HeapGraph.get_field g x j in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let vo : obj_addr = v in
      let wz = wosize_of_object x g in
      wosize_of_object_bound x g;
      hd_address_spec x;
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      HeapGraph.get_field_addr_eq g x j;
      wf_object_size_bound g x;
      field_read_implies_exists_pointing g x wz (U64.sub j 1UL) vo;
      white_target_resolve_stable g x vo
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Main proof: coalesce_preserves_wf
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let coalesce_preserves_wf g =
  let g' = fst (coalesce g) in
  coalesce_heap_unfold g g (objects zero_addr g) 0UL 0 0UL;
  coalesce_preserves_length g;

  // --- Part 4: no infix objects in g' ---
  let part4_aux (obj: obj_addr)
    : Lemma
      (requires Seq.mem obj (objects zero_addr g'))
      (ensures ~(is_infix obj g'))
    = coalesce_all_white_or_blue g;
      if is_blue obj g' then
        coalesce_blue_not_infix g obj
      else begin
        assert (g' == coalesce_heap g g (objects zero_addr g) 0UL 0 0UL);
        coalesce_aux_walk_all_wb g g zero_addr (objects zero_addr g) 0UL 0 0UL (objects zero_addr g) obj;
        is_white_iff obj g';
        is_blue_iff obj g';
        assert (Seq.mem obj (objects zero_addr g) /\ is_white obj g);
        coalesce_preserves_survivor_header g obj;
        tag_of_object_spec obj g;
        tag_of_object_spec obj g';
        is_infix_spec obj g;
        is_infix_spec obj g';
        wf_objects_non_infix g obj
      end
  in
  let part4_imp (obj: obj_addr)
    : Lemma (Seq.mem obj (objects zero_addr g') ==> ~(is_infix obj g'))
    = FStar.Classical.move_requires part4_aux obj
  in
  FStar.Classical.forall_intro part4_imp;
  assert (well_formed_heap_part4 g');

  // --- Part 1: size bounds ---
  let part1_aux (h: obj_addr)
    : Lemma
      (requires Seq.mem h (objects zero_addr g'))
      (ensures (let wz = wosize_of_object h g' in
                U64.v (hd_address h) + 8 + U64.v wz * 8 <= Seq.length g'))
    = coalesce_all_white_or_blue g;
      if is_blue h g' then
        coalesce_blue_size_bound g h
      else begin
        assert (g' == coalesce_heap g g (objects zero_addr g) 0UL 0 0UL);
        coalesce_aux_walk_all_wb g g zero_addr (objects zero_addr g) 0UL 0 0UL (objects zero_addr g) h;
        is_white_iff h g';
        is_blue_iff h g';
        assert (Seq.mem h (objects zero_addr g) /\ is_white h g);
        coalesce_preserves_survivor_header g h;
        wosize_of_object_spec h g;
        wosize_of_object_spec h g';
        assert (wosize_of_object h g' == wosize_of_object h g);
        wf_object_size_bound g h
      end
  in
  let part1_imp (h: obj_addr)
    : Lemma (Seq.mem h (objects zero_addr g') ==>
             (let wz = wosize_of_object h g' in
              U64.v (hd_address h) + 8 + U64.v wz * 8 <= Seq.length g'))
    = FStar.Classical.move_requires part1_aux h
  in
  FStar.Classical.forall_intro part1_imp;
  assert (well_formed_heap_part1 g');

  // --- Parts 2 and 3: field pointer closure (up to interior-pointer resolution) ---
  let part2_aux (src dst: obj_addr)
    : Lemma
      (requires
        Seq.mem src (objects zero_addr g') /\
        fields_constrained g' src /\
        (let wz = wosize_of_object src g' in
         U64.v wz < pow2 54 /\
         exists_field_pointing_to_unchecked g' src wz dst))
      (ensures Seq.mem (GC.Spec.Object.resolve_object dst g') (objects zero_addr g') /\
               GC.Spec.Object.infix_addr_wf g' (objects zero_addr g') dst)
    = coalesce_all_white_or_blue g;
      if is_blue src g' then begin
        coalesce_blue_field_closure g src dst;
        part4_aux dst;
        GC.Spec.Object.resolve_non_infix dst g';
        GC.Spec.Object.infix_addr_wf_intro g' (objects zero_addr g') dst
      end else begin
        assert (g' == coalesce_heap g g (objects zero_addr g) 0UL 0 0UL);
        coalesce_aux_walk_all_wb g g zero_addr (objects zero_addr g) 0UL 0 0UL (objects zero_addr g) src;
        is_white_iff src g';
        is_blue_iff src g';
        assert (Seq.mem src (objects zero_addr g) /\ is_white src g);
        coalesce_preserves_survivor_header g src;
        tag_of_object_spec src g;
        tag_of_object_spec src g';
        hd_address_spec src;
        is_no_scan_spec src g;
        is_no_scan_spec src g';
        white_src_field_closure g src dst
      end
  in
  let part2_flat (src dst: obj_addr)
    : Lemma
      (requires
        Seq.mem src (objects zero_addr g') /\
        fields_constrained g' src /\
        U64.v (wosize_of_object src g') < pow2 54 /\
        exists_field_pointing_to_unchecked g' src (wosize_of_object src g') dst)
      (ensures Seq.mem (GC.Spec.Object.resolve_object dst g') (objects zero_addr g') /\
               GC.Spec.Object.infix_addr_wf g' (objects zero_addr g') dst)
    = part2_aux src dst
  in
  well_formed_heap_part2_intro g' part2_flat;
  well_formed_heap_part3_intro g' part2_flat;

  // --- Combine all parts ---
  wf_parts ()
#pop-options

/// ---------------------------------------------------------------------------
/// Free list validity
/// ---------------------------------------------------------------------------

/// Helper: when flush returns first_blue, it's in the walk from sync
/// ---------------------------------------------------------------------------
/// coalesce_objects_subset: every object in the coalesced heap's walk was
/// also in the original heap's walk.
/// ---------------------------------------------------------------------------

val coalesce_aux_objects_subset
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr) (y: obj_addr)
  : Lemma
    (requires
      walk_pre g0 g start objs all_objs first_blue run_words /\
      (run_words > 0 ==> Seq.mem (first_blue <: obj_addr) all_objs) /\
      (forall (addr: hp_addr). U64.v addr >= U64.v start ==>
        read_word g addr == read_word g0 addr) /\
      (let sync : hp_addr =
         if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
       Seq.mem y (objects sync (coalesce_heap g0 g objs first_blue run_words fp))))
    (ensures Seq.mem y all_objs)

let coalesce_aux_objects_subset g0 g start objs first_blue run_words fp all_objs y =
  coalesce_aux_walk_all_wb_tag g0 g start objs first_blue run_words fp all_objs y

/// **The coalescer's free-list head is a heap object (or null).**
///
/// Top-level instance of `coalesce_aux_head_in_walk`.  The walk starts from a
/// null head, so the "head unchanged" disjunct degenerates to `0UL`.
val coalesce_head_in_walk (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures (let r = coalesce g in
              snd r == 0UL \/
              (U64.v (snd r) >= U64.v mword /\ U64.v (snd r) < heap_size /\
               U64.v (snd r) % U64.v mword == 0 /\
               Seq.mem (snd r <: obj_addr) (objects zero_addr (fst r)))))

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
let coalesce_head_in_walk g =
  coalesce_heap_unfold g g (objects zero_addr g) 0UL 0 0UL;
  coalesce_aux_head_in_walk g g zero_addr (objects zero_addr g) 0UL 0 0UL (objects zero_addr g)
#pop-options

val coalesce_objects_subset (g: heap) (y: obj_addr)
  : Lemma
    (requires post_sweep g /\ Seq.mem y (objects zero_addr (fst (coalesce g))))
    (ensures Seq.mem y (objects zero_addr g))

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
let coalesce_objects_subset g y =
  coalesce_heap_unfold g g (objects zero_addr g) 0UL 0 0UL;
  coalesce_aux_objects_subset g g zero_addr (objects zero_addr g) 0UL 0 0UL (objects zero_addr g) y
#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 1"
let coalesce_blue_blocks_scannable g =
  let g' = fst (coalesce g) in
  coalesce_preserves_wf g;
  let pf (obj: obj_addr) : Lemma
    (requires Seq.mem obj (objects zero_addr g') /\ is_blue obj g')
    (ensures ~(is_no_scan obj g'))
    = coalesce_heap_unfold g g (objects zero_addr g) 0UL 0 0UL;
      assert (g' == coalesce_heap g g (objects zero_addr g) 0UL 0 0UL);
      coalesce_aux_blue_tag_zero g g zero_addr (objects zero_addr g) 0UL 0 0UL
        (objects zero_addr g) obj;
      assert (tag_of_object obj g' == 0UL);
      is_no_scan_spec obj g';
      no_scan_tag_val ()
  in
  blue_blocks_scannable_intro g' pf
#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
let coalesce_blue_fields_non_infix g =
  let g' = fst (coalesce g) in
  coalesce_preserves_wf g;
  wf_parts ();
  let raw (src dst: obj_addr) : Lemma
    (requires Seq.mem src (objects zero_addr g') /\
              is_blue src g' /\
              (let wz = wosize_of_object src g' in
               U64.v wz < pow2 54 /\
               exists_field_pointing_to_unchecked g' src wz dst))
    (ensures Seq.mem dst (objects zero_addr g'))
    = coalesce_blue_field_closure g src dst
  in
  blue_fields_non_infix_from_raw g' raw
#pop-options

private let flush_blue_snd_is_fb (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      run_words >= 2 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v (hd_address (first_blue <: obj_addr)) + U64.v mword * 2 <= heap_size)
    (ensures snd (flush_blue g first_blue run_words fp) == first_blue)
  = ()

private let rec flush_walk_reaches
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (s: hp_addr) (y: obj_addr)
  : Lemma
    (requires
      run_words > 0 /\
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v s % U64.v mword == 0 /\
      Seq.length (objects s g) > 0 /\
      Seq.mem (first_blue <: obj_addr) (objects s g) /\
      (forall (t: hp_addr).
        U64.v s <= U64.v t /\
        U64.v t < U64.v (hd_address (first_blue <: obj_addr)) /\
        Seq.length (objects t g) > 0 ==>
        U64.v t + (U64.v (getWosize (read_word g t)) + 1) * U64.v mword
          <= U64.v (hd_address (first_blue <: obj_addr))) /\
      U64.v s <= U64.v (hd_address (first_blue <: obj_addr)) /\
      Seq.mem y (objects (hd_address (first_blue <: obj_addr))
                   (fst (flush_blue g first_blue run_words fp))))
     (ensures
      (let g' = fst (flush_blue g first_blue run_words fp) in
       Seq.mem y (objects s g') /\
       (Seq.mem y (objects (hd_address (first_blue <: obj_addr)) g') \/
        (Seq.mem y (objects s g) /\
         U64.v y + U64.v mword <= U64.v (hd_address (first_blue <: obj_addr))))))
    (decreases (Seq.length (objects s g)))
  = let g' = fst (flush_blue g first_blue run_words fp) in
    flush_blue_preserves_length g first_blue run_words fp;
    hd_address_spec (first_blue <: obj_addr);
    if U64.v s = U64.v (hd_address (first_blue <: obj_addr)) then ()
    else begin
      objects_nonempty_next s g;
      f_address_spec s;
      let obj = f_address s in
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * U64.v mword in
      flush_blue_preserves_outside g first_blue run_words fp s;
      assert (read_word g' s == read_word g s);
      objects_nonempty_next s g';
      if next_nat >= heap_size then
        objects_tail_empty_when_done s g
      else begin
        let next : hp_addr = U64.uint_to_t next_nat in
        Seq.lemma_tl obj (objects next g);
        assert (Seq.tail (objects s g) == objects next g);
        if Seq.length (objects next g) = 0 then assert False
        else begin
          mem_cons_lemma (first_blue <: obj_addr) obj (Seq.tail (objects s g));
          flush_walk_reaches g first_blue run_words fp next y;
          Seq.lemma_tl obj (objects next g');
          mem_cons_lemma y obj (Seq.tail (objects s g'))
        end
      end
    end

(*private let flush_merged_in_walk
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t) (run_end: nat)
  : Lemma
    (requires
      run_words >= 2 /\
      run_words - 1 < pow2 54 /\
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      Seq.mem (first_blue <: obj_addr) (objects zero_addr g) /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == run_end /\
      run_end <= heap_size /\
      run_end % U64.v mword == 0 /\
      Seq.length (objects zero_addr g) > 0 /\
      U64.v zero_addr <= U64.v (hd_address (first_blue <: obj_addr)) /\
      (forall (t: hp_addr).
        U64.v zero_addr <= U64.v t /\
        U64.v t < U64.v (hd_address (first_blue <: obj_addr)) /\
        Seq.length (objects t g) > 0 ==>
        U64.v t + (U64.v (getWosize (read_word g t)) + 1) * U64.v mword
          <= U64.v (hd_address (first_blue <: obj_addr))))
    (ensures
      Seq.mem (first_blue <: obj_addr)
        (objects zero_addr (fst (flush_blue g first_blue run_words fp))))
  = hd_address_spec (first_blue <: obj_addr);
    flush_blue_preserves_length g first_blue run_words fp;
    flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
    let g' = fst (flush_blue g first_blue run_words fp) in
    merged_block_head g' (first_blue <: obj_addr) run_words;
    flush_walk_reaches g first_blue run_words fp zero_addr (first_blue <: obj_addr)

private let rec flush_preserves_chain
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (cur: U64.t) (obj: U64.t) (n: nat)
  : Lemma
    (requires
      run_words > 0 /\
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      (forall (x: U64.t). on_fl g cur x n ==>
        U64.v x + U64.v mword <= U64.v (hd_address (first_blue <: obj_addr))))
    (ensures
      on_fl (fst (flush_blue g first_blue run_words fp)) cur obj n == on_fl g cur obj n)
    (decreases n)
  = if n = 0 then ()
    else if not (fl_node cur) then ()
    else if cur = obj then ()
    else begin
      let g' = fst (flush_blue g first_blue run_words fp) in
      hd_address_spec (first_blue <: obj_addr);
      assert (on_fl g cur cur n);
      assert (U64.v cur + U64.v mword <= U64.v (hd_address (first_blue <: obj_addr)));
      flush_blue_preserves_outside g first_blue run_words fp (cur <: hp_addr);
      assert (fl_next g' cur == fl_next g cur);
      introduce forall (x: U64.t). on_fl g (fl_next g cur) x (n - 1) ==>
        U64.v x + U64.v mword <= U64.v (hd_address (first_blue <: obj_addr))
      with introduce _ ==> _
      with on_fl_cons g cur x (n - 1);
      flush_preserves_chain g first_blue run_words fp (fl_next g cur) obj (n - 1)
    end

private let flush_preserves_reachable
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (cur: U64.t) (obj: U64.t)
  : Lemma
    (requires
      run_words > 0 /\
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      (forall (x: U64.t) (n: nat). on_fl g cur x n ==>
        U64.v x + U64.v mword <= U64.v (hd_address (first_blue <: obj_addr))))
    (ensures
      reachable_on_fl (fst (flush_blue g first_blue run_words fp)) cur obj <==>
      reachable_on_fl g cur obj)
    = introduce reachable_on_fl g cur obj ==>
              reachable_on_fl (fst (flush_blue g first_blue run_words fp)) cur obj
    with begin
      eliminate exists (n: nat). on_fl g cur obj n
      with begin
        flush_preserves_chain g first_blue run_words fp cur obj n;
        assert (on_fl (fst (flush_blue g first_blue run_words fp)) cur obj n)
      end
    end;
    introduce reachable_on_fl (fst (flush_blue g first_blue run_words fp)) cur obj ==>
              reachable_on_fl g cur obj
    with begin
      eliminate exists (n: nat).
        on_fl (fst (flush_blue g first_blue run_words fp)) cur obj n
      with begin
        flush_preserves_chain g first_blue run_words fp cur obj n;
        assert (on_fl g cur obj n)
      end
    end

private let rec flush_prefix_from
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (s: hp_addr) (y: obj_addr)
  : Lemma
    (requires
      run_words > 0 /\
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v s % U64.v mword == 0 /\
      U64.v s <= U64.v (hd_address (first_blue <: obj_addr)) /\
      U64.v y + U64.v mword <= U64.v (hd_address (first_blue <: obj_addr)) /\
      Seq.mem y (objects s g))
    (ensures
      Seq.mem y (objects s (fst (flush_blue g first_blue run_words fp))))
    (decreases (Seq.length (objects s g)))
  = let g' = fst (flush_blue g first_blue run_words fp) in
    flush_blue_preserves_length g first_blue run_words fp;
    hd_address_spec (first_blue <: obj_addr);
    if U64.v s = U64.v (hd_address (first_blue <: obj_addr)) then begin
      objects_addresses_gt_start s g y;
      assert False
    end
    else begin
      objects_nonempty_next s g;
      f_address_spec s;
      let obj = f_address s in
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * U64.v mword in
      flush_blue_preserves_outside g first_blue run_words fp s;
      assert (read_word g' s == read_word g s);
      Seq.cons_head_tail (objects s g);
      mem_cons_lemma y obj (Seq.tail (objects s g));
      objects_nonempty_next s g';
      if y = obj then
        mem_cons_lemma obj obj (Seq.tail (objects s g'))
      else begin
        if next_nat >= heap_size then
          objects_tail_empty_when_done s g
        else begin
          let next : hp_addr = U64.uint_to_t next_nat in
          Seq.lemma_tl obj (objects next g);
          assert (Seq.mem y (objects next g));
          objects_addresses_gt_start next g y;
          flush_prefix_from g first_blue run_words fp next y;
          Seq.lemma_tl obj (objects next g');
          mem_cons_lemma y obj (Seq.tail (objects s g'))
        end
      end
    end

private let flush_preserves_prefix_membership
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t) (y: obj_addr)
  : Lemma
    (requires
      run_words > 0 /\
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v y + U64.v mword <= U64.v (hd_address (first_blue <: obj_addr)) /\
      Seq.mem y (objects zero_addr g))
    (ensures
      Seq.mem y (objects zero_addr (fst (flush_blue g first_blue run_words fp))))
  = objects_addresses_gt_start zero_addr g y;
    flush_prefix_from g first_blue run_words fp zero_addr y

module SI = GC.Spec.SweepInv

private let rec flush_walk_split
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (s: hp_addr) (y: obj_addr)
  : Lemma
    (requires
      run_words >= 2 /\
      Seq.length g == heap_size /\
      linkable_heap g /\
      U64.v s + U64.v mword < heap_size /\
      Seq.mem (f_address s) (objects zero_addr g) /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v s % U64.v mword == 0 /\
      U64.v s <= U64.v (hd_address (first_blue <: obj_addr)) /\
      Seq.length (objects s g) > 0 /\
      Seq.mem (first_blue <: obj_addr) (objects s g) /\
      SI.heap_objects_dense g /\
      (forall (t: hp_addr).
        U64.v s <= U64.v t /\
        U64.v t < U64.v (hd_address (first_blue <: obj_addr)) /\
        Seq.length (objects t g) > 0 ==>
        U64.v t + (U64.v (getWosize (read_word g t)) + 1) * U64.v mword
          <= U64.v (hd_address (first_blue <: obj_addr))) /\
      Seq.mem y (objects s (fst (flush_blue g first_blue run_words fp))))
    (ensures
      (let g' = fst (flush_blue g first_blue run_words fp) in
       Seq.mem y (objects (hd_address (first_blue <: obj_addr)) g') \/
       (Seq.mem y (objects s g) /\
        U64.v y + U64.v mword <= U64.v (hd_address (first_blue <: obj_addr)))))
    (decreases (Seq.length (objects s g)))
  = let g' = fst (flush_blue g first_blue run_words fp) in
    flush_blue_preserves_length g first_blue run_words fp;
    hd_address_spec (first_blue <: obj_addr);
    if U64.v s = U64.v (hd_address (first_blue <: obj_addr)) then ()
    else begin
      objects_nonempty_next s g;
      f_address_spec s;
      let obj = f_address s in
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * U64.v mword in
      flush_blue_preserves_outside g first_blue run_words fp s;
      assert (read_word g' s == read_word g s);
      objects_nonempty_next s g';
      Seq.cons_head_tail (objects s g');
      mem_cons_lemma y obj (Seq.tail (objects s g'));
      if y = obj then begin
        Seq.cons_head_tail (objects s g);
        mem_cons_lemma obj obj (Seq.tail (objects s g));
        hd_address_spec obj;
        assert (U64.v (wosize_of_object obj g) >= 1);
        wosize_of_object_spec obj g;
        assert (U64.v (getWosize (read_word g s)) >= 1)
      end
      else begin
        if next_nat >= heap_size then assert False
        else begin
          let next : hp_addr = U64.uint_to_t next_nat in
          Seq.lemma_tl obj (objects next g);
          assert (Seq.tail (objects s g) == objects next g);
          if Seq.length (objects next g) = 0 then assert False
          else begin
            Seq.lemma_tl obj (objects next g');
            assert (Seq.tail (objects s g') == objects next g');
            mem_cons_lemma (first_blue <: obj_addr) obj (Seq.tail (objects s g));
            SI.objects_dense_obj_in s g;
            SI.obj_in_objects_elim (U64.uint_to_t (next_nat + U64.v mword)) g;
            f_address_spec next;
            flush_walk_split g first_blue run_words fp next y;
            mem_cons_lemma y obj (Seq.tail (objects s g))
          end
        end
      end
    end
    
private let flush_objects_cases
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t) (y: obj_addr) (run_end: nat)
  : Lemma
    (requires
      run_words >= 2 /\
      run_words - 1 < pow2 54 /\
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == run_end /\
      run_end <= heap_size /\
      Seq.mem y (objects zero_addr (fst (flush_blue g first_blue run_words fp))))
    (ensures
      y == (first_blue <: obj_addr) \/
      (Seq.mem y (objects zero_addr g) /\
       (U64.v y + U64.v (wosize_of_object y g) * U64.v mword
          <= U64.v (hd_address (first_blue <: obj_addr)) \/
        U64.v (hd_address y) >= run_end)))
  = admit()

private let flush_objects_reflect
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t) (y: obj_addr)
  : Lemma
    (requires
      run_words >= 2 /\
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v (hd_address (first_blue <: obj_addr)) + run_words * U64.v mword <= heap_size /\
      Seq.mem y (objects zero_addr (fst (flush_blue g first_blue run_words fp))) /\
      y <> (first_blue <: obj_addr))
    (ensures Seq.mem y (objects zero_addr g) /\
             (U64.v y + U64.v (wosize_of_object y g) * U64.v mword <= U64.v (hd_address (first_blue <: obj_addr)) \/
              U64.v (hd_address y) >= U64.v (hd_address (first_blue <: obj_addr)) + run_words * U64.v mword))
  = hd_address_spec (first_blue <: obj_addr);
    flush_objects_cases g first_blue run_words fp y
      (U64.v (hd_address (first_blue <: obj_addr)) + run_words * U64.v mword)



private let rec run_walk_reaches_end
  (g: heap) (s: hp_addr) (run_end: nat) (y: obj_addr)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v s % U64.v mword == 0 /\
      U64.v s <= run_end /\
      run_end + U64.v mword < heap_size /\
      run_end % U64.v mword == 0 /\
      SI.heap_objects_dense g /\
      U64.v s + U64.v mword < heap_size /\
      Seq.mem (f_address s) (objects zero_addr g) /\
      Seq.length (objects s g) > 0 /\
      (forall (t: hp_addr).
        U64.v s <= U64.v t /\ U64.v t < run_end /\
        Seq.length (objects t g) > 0 ==>
        U64.v t + (U64.v (getWosize (read_word g t)) + 1) * U64.v mword <= run_end) /\
      U64.v (hd_address y) >= run_end)
    (ensures (Seq.mem y (objects s g) <==>
              Seq.mem y (objects (U64.uint_to_t run_end) g)))
    (decreases (Seq.length (objects s g)))
  = if U64.v s = run_end then ()
    else begin
      objects_nonempty_next s g;
      f_address_spec s;
      let obj = f_address s in
      hd_address_spec obj;
      assert (U64.v (hd_address obj) == U64.v s);
      assert (U64.v s < run_end);
      assert (y <> obj);
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * U64.v mword in
      if next_nat >= heap_size then assert False
      else begin
        let next : hp_addr = U64.uint_to_t next_nat in
        Seq.lemma_tl obj (objects next g);
        assert (Seq.tail (objects s g) == objects next g);
        if Seq.length (objects next g) = 0 then begin
          SI.objects_dense_step s g;
          assert False
        end
        else begin
          SI.objects_dense_step s g;
          SI.objects_dense_obj_in s g;
          SI.obj_in_objects_elim (U64.uint_to_t (next_nat + U64.v mword)) g;
          f_address_spec next;
          run_walk_reaches_end g next run_end y;
          mem_cons_lemma y obj (Seq.tail (objects s g))
        end
      end
    end

private let rec walk_agree_above_run
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (s: hp_addr) (y: obj_addr) (run_end: nat)
  : Lemma
    (requires
      run_words >= 2 /\
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == run_end /\
      run_end <= heap_size /\
      U64.v s >= run_end /\
      Seq.mem y (objects s g))
    (ensures
      Seq.mem y (objects s (fst (flush_blue g first_blue run_words fp))))
    (decreases (Seq.length (objects s g)))
  = let g' = fst (flush_blue g first_blue run_words fp) in
    flush_blue_preserves_length g first_blue run_words fp;
    hd_address_spec (first_blue <: obj_addr);
    objects_nonempty_next s g;
    f_address_spec s;
    let obj = f_address s in
    let wz = getWosize (read_word g s) in
    let next_nat = U64.v s + (U64.v wz + 1) * U64.v mword in
    flush_blue_preserves_outside g first_blue run_words fp s;
    assert (read_word g' s == read_word g s);
    objects_nonempty_next s g';
    Seq.cons_head_tail (objects s g);
    mem_cons_lemma y obj (Seq.tail (objects s g));
    if y = obj then mem_cons_lemma obj obj (Seq.tail (objects s g'))
    else begin
      if next_nat >= heap_size then objects_tail_empty_when_done s g
      else begin
        let next : hp_addr = U64.uint_to_t next_nat in
        Seq.lemma_tl obj (objects next g);
        walk_agree_above_run g first_blue run_words fp next y run_end;
        Seq.lemma_tl obj (objects next g');
        mem_cons_lemma y obj (Seq.tail (objects s g'))
      end
    end

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

private let rec flush_above_from
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (s: hp_addr) (y: obj_addr) (run_end: nat)
  : Lemma
    (requires
      run_words >= 2 /\
      run_words - 1 < pow2 54 /\
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == run_end /\
      run_end + U64.v mword < heap_size /\
      run_end % U64.v mword == 0 /\
      U64.v s % U64.v mword == 0 /\
      U64.v s <= U64.v (hd_address (first_blue <: obj_addr)) /\
      (forall (t: hp_addr).
        U64.v s <= U64.v t /\
        U64.v t < U64.v (hd_address (first_blue <: obj_addr)) /\
        Seq.length (objects t g) > 0 ==>
        U64.v t + (U64.v (getWosize (read_word g t)) + 1) * U64.v mword
          <= U64.v (hd_address (first_blue <: obj_addr))) /\
      U64.v (hd_address y) >= run_end /\
      SI.heap_objects_dense g /\
      U64.v s + U64.v mword < heap_size /\
      Seq.mem (f_address s) (objects zero_addr g) /\
      (forall (t: hp_addr).
        U64.v s <= U64.v t /\ U64.v t < run_end /\
        Seq.length (objects t g) > 0 ==>
        U64.v t + (U64.v (getWosize (read_word g t)) + 1) * U64.v mword <= run_end) /\
      Seq.mem y (objects s g))
    (ensures
      Seq.mem y (objects s (fst (flush_blue g first_blue run_words fp))))
    (decreases (Seq.length (objects s g)))
  = let g' = fst (flush_blue g first_blue run_words fp) in
    flush_blue_preserves_length g first_blue run_words fp;
    hd_address_spec (first_blue <: obj_addr);
    if U64.v s = U64.v (hd_address (first_blue <: obj_addr)) then
    begin
      assert (U64.v s <= run_end);
      assert (Seq.length (objects s g) > 0);
      run_walk_reaches_end g s run_end y;
      assert (Seq.mem y (objects (U64.uint_to_t run_end) g));
      walk_agree_above_run g first_blue run_words fp (U64.uint_to_t run_end) y run_end;
      assert (Seq.mem y (objects (U64.uint_to_t run_end) g'));
      flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
      merged_block_recompose g' (first_blue <: obj_addr) run_words
        (U64.uint_to_t run_end) y
    end
    else begin
      objects_nonempty_next s g;
      f_address_spec s;
      let obj = f_address s in
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * U64.v mword in
      flush_blue_preserves_outside g first_blue run_words fp s;
      assert (read_word g' s == read_word g s);
      objects_nonempty_next s g';
      if next_nat >= heap_size then assert False
      else begin
        let next : hp_addr = U64.uint_to_t next_nat in
        Seq.lemma_tl obj (objects next g);
        assert (Seq.tail (objects s g) == objects next g);
        mem_cons_lemma y obj (Seq.tail (objects s g));
        if y = obj then mem_cons_lemma obj obj (Seq.tail (objects s g'))
        else begin
          SI.objects_dense_obj_in s g;
          SI.obj_in_objects_elim (U64.uint_to_t (next_nat + U64.v mword)) g;
          f_address_spec next;
          flush_above_from g first_blue run_words fp next y run_end;
          Seq.lemma_tl obj (objects next g');
          mem_cons_lemma y obj (Seq.tail (objects s g'))
        end
      end
    end

#pop-options

private let flush_objects_above
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t) (y: obj_addr) (run_end: nat)
  : Lemma
    (requires
      run_words >= 2 /\
      run_words - 1 < pow2 54 /\
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == run_end /\
      run_end + U64.v mword < heap_size /\
      run_end % U64.v mword == 0 /\
      SI.heap_objects_dense g /\
      Seq.length (objects zero_addr g) > 0 /\
      Seq.mem (f_address zero_addr) (objects zero_addr g) /\
      U64.v zero_addr <= U64.v (hd_address (first_blue <: obj_addr)) /\
      (forall (t: hp_addr).
        U64.v zero_addr <= U64.v t /\
        U64.v t < U64.v (hd_address (first_blue <: obj_addr)) /\
        Seq.length (objects t g) > 0 ==>
        U64.v t + (U64.v (getWosize (read_word g t)) + 1) * U64.v mword
          <= U64.v (hd_address (first_blue <: obj_addr))) /\
      (forall (t: hp_addr).
        U64.v zero_addr <= U64.v t /\ U64.v t < run_end /\
        Seq.length (objects t g) > 0 ==>
        U64.v t + (U64.v (getWosize (read_word g t)) + 1) * U64.v mword <= run_end) /\
      Seq.mem y (objects zero_addr g) /\
      U64.v (hd_address y) >= run_end)
    (ensures
      Seq.mem y (objects zero_addr (fst (flush_blue g first_blue run_words fp))))
  = flush_above_from g first_blue run_words fp zero_addr y run_end

#push-options "--z3rlimit 800 --fuel 1 --ifuel 1"
private let flush_step_fl_exact
  (g: heap) (run_end: nat) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      run_words >= 2 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == run_end /\
      run_end <= heap_size /\
      run_end % U64.v mword == 0 /\
      linkable_heap g /\
      fl_sound g fp /\
      (forall (t: hp_addr).
        U64.v zero_addr <= U64.v t /\
        U64.v t < U64.v (hd_address (first_blue <: obj_addr)) /\
        Seq.length (objects t g) > 0 ==>
        U64.v t + (U64.v (getWosize (read_word g t)) + 1) * U64.v mword
          <= U64.v (hd_address (first_blue <: obj_addr))) /\
      Seq.mem (first_blue <: obj_addr) (objects zero_addr g) /\
      (forall (x: U64.t) (n: nat). on_fl g fp x n ==>
        U64.v x + U64.v mword <= U64.v (hd_address (first_blue <: obj_addr))) /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ is_blue y g /\
        U64.v y < U64.v (hd_address (first_blue <: obj_addr)) ==>
        reachable_on_fl g fp y))
    (ensures (let (g', fp') = flush_blue g first_blue run_words fp in
              fl_sound g' fp' /\
              (forall (y: obj_addr).
                Seq.mem y (objects zero_addr g') /\ is_blue y g' /\
                U64.v y < run_end ==>
                reachable_on_fl g' fp' y) /\
              (forall (x: U64.t) (n: nat). on_fl g' fp' x n ==>
                U64.v x + U64.v mword <= run_end)))
  = hd_address_spec (first_blue <: obj_addr);
    flush_blue_preserves_length g first_blue run_words fp;
    flush_blue_snd_is_fb g first_blue run_words fp;
    flush_blue_field1_spec g (first_blue <: obj_addr) run_words fp;
    let g' = fst (flush_blue g first_blue run_words fp) in
    assert (fl_next g' (first_blue <: obj_addr) == fp);
    flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
    let wz : wosize = U64.uint_to_t (run_words - 1) in
    merged_block_is_blue g' (first_blue <: obj_addr) wz;
    assert (is_blue (first_blue <: obj_addr) g');
    linkable_is_fl_node g (first_blue <: obj_addr);

    introduce forall (y: U64.t). reachable_on_fl g' (first_blue <: obj_addr) y ==>
      (fl_node y /\
       (U64.v y >= U64.v mword /\ U64.v y < heap_size /\ U64.v y % U64.v mword == 0) /\
       Seq.mem (y <: obj_addr) (objects zero_addr g') /\
       is_blue (y <: obj_addr) g')
    with introduce _ ==> _
    with begin
      reachable_is_node g' (first_blue <: obj_addr) y;
      if y = (first_blue <: obj_addr) then begin
        objects_addresses_gt_start zero_addr g (first_blue <: obj_addr);
        flush_merged_in_walk g first_blue run_words fp run_end;
        assert (Seq.mem (first_blue <: obj_addr) (objects zero_addr g'))
      end
      else begin
        reachable_uncons g' (first_blue <: obj_addr) y;
        assert (reachable_on_fl g' fp y);
        flush_preserves_reachable g first_blue run_words fp fp y;
        assert (reachable_on_fl g fp y);
        assert (Seq.mem (y <: obj_addr) (objects zero_addr g));
        assert (is_blue (y <: obj_addr) g);
        hd_address_spec (y <: obj_addr);
        flush_blue_preserves_outside g first_blue run_words fp (hd_address (y <: obj_addr));
        is_blue_iff (y <: obj_addr) g;
        is_blue_iff (y <: obj_addr) g';
        color_of_object_spec (y <: obj_addr) g;
        color_of_object_spec (y <: obj_addr) g';
        assert (is_blue (y <: obj_addr) g');
        flush_preserves_prefix_membership g first_blue run_words fp (y <: obj_addr);
        assert (Seq.mem (y <: obj_addr) (objects zero_addr g'))
      end
    end;

    introduce forall (y: obj_addr).
      (Seq.mem y (objects zero_addr g') /\ is_blue y g' /\ U64.v y < run_end) ==>
      reachable_on_fl g' (first_blue <: obj_addr) y
    with introduce _ ==> _
    with begin
      if y = (first_blue <: obj_addr) then
        reachable_head g' (first_blue <: obj_addr)
      else begin
        assert (g' == fst (flush_blue g first_blue run_words fp));
        flush_objects_reflect g first_blue run_words fp y;
        assert (Seq.mem y (objects zero_addr g));
        hd_address_spec y;
        flush_blue_preserves_outside g first_blue run_words fp (hd_address y);
        is_blue_iff y g;
        is_blue_iff y g';
        color_of_object_spec y g;
        color_of_object_spec y g';
        assert (is_blue y g);
        if U64.v y + U64.v (wosize_of_object y g) * U64.v mword <= U64.v (hd_address (first_blue <: obj_addr))
        then begin
          assert (U64.v y < U64.v (hd_address (first_blue <: obj_addr)));
          assert (reachable_on_fl g fp y);
          flush_preserves_reachable g first_blue run_words fp fp y;
          assert (reachable_on_fl g' fp y);
          assert (fl_next g' (first_blue <: obj_addr) == fp);
          assert (reachable_on_fl g' (fl_next g' (first_blue <: obj_addr)) y);
          reachable_cons g' (first_blue <: obj_addr) y
        end
      else assert False
      end
    end;
    introduce forall (x: U64.t) (n: nat). on_fl g' (first_blue <: obj_addr) x n ==>
      U64.v x + U64.v mword <= run_end
    with introduce _ ==> _
    with begin
      on_fl_is_node g' (first_blue <: obj_addr) x n;
      if x = (first_blue <: obj_addr) then ()
      else begin
        on_fl_uncons g' (first_blue <: obj_addr) x n;
        assert (on_fl g' fp x (n - 1));
        flush_preserves_chain g first_blue run_words fp fp x (n - 1)
      end
    end

#pop-options
*)
let coalesce_aux_empty (g0 g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma (coalesce_aux g0 g Seq.empty first_blue run_words fp ==
           flush_blue g first_blue run_words fp)
  = ()
let coalesce_aux_blue_step
  (g0 g: heap) (objs: seq obj_addr) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires Seq.length objs > 0 /\ is_blue (Seq.head objs) g0)
    (ensures
      coalesce_aux g0 g objs first_blue run_words fp ==
      coalesce_aux g0 g (Seq.tail objs)
        (if run_words = 0 then Seq.head objs else first_blue)
        (run_words + U64.v (wosize_of_object (Seq.head objs) g0) + 1) fp)
  = ()

let coalesce_aux_white_step
  (g0 g: heap) (objs: seq obj_addr) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires Seq.length objs > 0 /\ ~(is_blue (Seq.head objs) g0))
    (ensures
      (let (g', fp') = flush_blue g first_blue run_words fp in
       coalesce_aux g0 g objs first_blue run_words fp ==
       coalesce_aux g0 g' (Seq.tail objs) 0UL 0 fp'))
  = ()


(*#push-options "--z3rlimit 800 --fuel 1 --ifuel 1"

private let pow2_57_div_8 () : Lemma (pow2 57 / 8 == pow2 54)
  = assert_norm (pow2 57 / 8 == pow2 54)

private let flush_preserves_linkable
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      run_words >= 2 /\
      run_words - 1 < pow2 54 /\
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v (hd_address (first_blue <: obj_addr)) + run_words * U64.v mword <= heap_size /\
      linkable_heap g)
    (ensures linkable_heap (fst (flush_blue g first_blue run_words fp)))
  = hd_address_spec (first_blue <: obj_addr);
    flush_blue_preserves_length g first_blue run_words fp;
    flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
    let g' = fst (flush_blue g first_blue run_words fp) in
    let run_end = U64.v (hd_address (first_blue <: obj_addr)) + run_words * U64.v mword in
    introduce forall (obj: obj_addr).
      Seq.mem obj (objects zero_addr g') ==>
      (U64.v (wosize_of_object obj g') >= 1 /\
       U64.v (hd_address obj) + U64.v mword * 2 <= heap_size)
    with introduce _ ==> _
    with begin
      flush_objects_cases g first_blue run_words fp obj run_end;
      if obj = (first_blue <: obj_addr) then begin
        let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
        makeHeader_getWosize wz_u64 Blue 0UL;
        wosize_of_object_spec obj g';
        assert (U64.v (wosize_of_object obj g') >= 1);
        assert (U64.v (hd_address obj) + U64.v mword * 2 <= heap_size)
      end
      else begin
        hd_address_spec obj;
        flush_blue_preserves_outside g first_blue run_words fp (hd_address obj);
        wosize_of_object_spec obj g;
        wosize_of_object_spec obj g';
        assert (U64.v (wosize_of_object obj g') >= 1);
        assert (U64.v (hd_address obj) + U64.v mword * 2 <= heap_size)
      end
    end

private let coalesce_empty_case
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr)
  : Lemma
    (requires
      Seq.length objs = 0 /\
      walk_pre g0 g start objs all_objs first_blue run_words /\
      linkable_heap g /\
      linkable_heap g0 /\
      SI.heap_objects_dense g /\
      Seq.length (objects zero_addr g) > 0 /\
      fl_sound g fp /\
      (run_words > 0 ==> run_words >= 2) /\
      (run_words > 0 ==>
        (forall (t: hp_addr).
          U64.v zero_addr <= U64.v t /\
          U64.v t < U64.v (hd_address (first_blue <: obj_addr)) /\
          Seq.length (objects t g) > 0 ==>
          U64.v t + (U64.v (getWosize (read_word g t)) + 1) * U64.v mword
            <= U64.v (hd_address (first_blue <: obj_addr)))) /\
      (run_words > 0 ==> Seq.mem (first_blue <: obj_addr) (objects zero_addr g)) /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g0) /\ U64.v y >= U64.v start ==>
        Seq.mem y (objects zero_addr g)) /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ ~(Seq.mem y objs) ==>
        U64.v y < U64.v start) /\
      (forall (x: U64.t) (n: nat). on_fl g fp x n ==>
        U64.v x + U64.v mword <= U64.v (if run_words > 0
                                        then hd_address (first_blue <: obj_addr)
                                        else start)) /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ is_blue y g /\
        U64.v y < U64.v (if run_words > 0
                         then hd_address (first_blue <: obj_addr)
                         else start) ==>
        reachable_on_fl g fp y))
    (ensures (let (g', fp') = coalesce_aux g0 g objs first_blue run_words fp in
              fl_exact g' fp'))
  = Seq.lemma_eq_elim objs Seq.empty;
    coalesce_aux_empty g0 g first_blue run_words fp;
    assert (forall (y: obj_addr).
      Seq.mem y (objects zero_addr g) ==> U64.v y < U64.v start);
    if run_words = 0 then
      assert (flush_blue g first_blue run_words fp == (g, fp))
    else begin
      hd_address_spec (first_blue <: obj_addr);
      run_words_bound first_blue run_words start;
      flush_blue_preserves_length g first_blue run_words fp;
      if run_words = 1 then assert False
      else begin
        flush_step_fl_exact g (U64.v start) first_blue run_words fp;
        let g' = fst (flush_blue g first_blue run_words fp) in
        introduce forall (y: obj_addr).
          (Seq.mem y (objects zero_addr g') /\ is_blue y g') ==>
          reachable_on_fl g' (snd (flush_blue g first_blue run_words fp)) y
        with introduce _ ==> _
        with begin
          if y = (first_blue <: obj_addr) then ()
          else begin
            flush_objects_reflect g first_blue run_words fp y;
            hd_address_spec y
          end
        end
      end
    end

val coalesce_blue_case
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      is_blue (Seq.head objs) g0 /\
      walk_pre g0 g start objs all_objs first_blue run_words /\
      linkable_heap g /\
      linkable_heap g0 /\
      SI.heap_objects_dense g /\
      Seq.length (objects zero_addr g) > 0 /\
      fl_sound g fp /\
      (run_words > 0 ==> run_words >= 2) /\
      (forall (t: hp_addr).
        U64.v zero_addr <= U64.v t /\
        U64.v t < U64.v (if run_words > 0
                         then hd_address (first_blue <: obj_addr)
                         else start) /\
        Seq.length (objects t g) > 0 ==>
        U64.v t + (U64.v (getWosize (read_word g t)) + 1) * U64.v mword
          <= U64.v (if run_words > 0
                    then hd_address (first_blue <: obj_addr)
                    else start)) /\
      (run_words > 0 ==> Seq.mem (first_blue <: obj_addr) (objects zero_addr g)) /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g0) /\ U64.v y >= U64.v start ==>
        Seq.mem y (objects zero_addr g)) /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ ~(Seq.mem y objs) ==>
        U64.v y < U64.v start) /\
      (forall (x: U64.t) (n: nat). on_fl g fp x n ==>
        U64.v x + U64.v mword <= U64.v (if run_words > 0
                                        then hd_address (first_blue <: obj_addr)
                                        else start)) /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ is_blue y g /\
        U64.v y < U64.v (if run_words > 0
                         then hd_address (first_blue <: obj_addr)
                         else start) ==>
        reachable_on_fl g fp y))
    (ensures (let (g', fp') = coalesce_aux g0 g objs first_blue run_words fp in
              fl_exact g' fp'))
    (decreases %[Seq.length objs; 0])

val coalesce_white_case
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      ~(is_blue (Seq.head objs) g0) /\
      walk_pre g0 g start objs all_objs first_blue run_words /\
      linkable_heap g /\
      linkable_heap g0 /\
      SI.heap_objects_dense g /\
      fl_sound g fp /\
      (run_words > 0 ==> run_words >= 2) /\
      (forall (t: hp_addr).
        U64.v zero_addr <= U64.v t /\
        U64.v t < U64.v (if run_words > 0
                         then hd_address (first_blue <: obj_addr)
                         else start) /\
        Seq.length (objects t g) > 0 ==>
        U64.v t + (U64.v (getWosize (read_word g t)) + 1) * U64.v mword
          <= U64.v (if run_words > 0
                    then hd_address (first_blue <: obj_addr)
                    else start)) /\
      (run_words > 0 ==> Seq.mem (first_blue <: obj_addr) (objects zero_addr g)) /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g0) /\ U64.v y >= U64.v start ==>
        Seq.mem y (objects zero_addr g)) /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ ~(Seq.mem y objs) ==>
        U64.v y < U64.v start) /\
      (forall (x: U64.t) (n: nat). on_fl g fp x n ==>
        U64.v x + U64.v mword <= U64.v (if run_words > 0
                                        then hd_address (first_blue <: obj_addr)
                                        else start)) /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ is_blue y g /\
        U64.v y < U64.v (if run_words > 0
                         then hd_address (first_blue <: obj_addr)
                         else start) ==>
        reachable_on_fl g fp y))
    (ensures (let (g', fp') = coalesce_aux g0 g objs first_blue run_words fp in
              fl_exact g' fp'))
    (decreases %[Seq.length objs; 0])

val coalesce_aux_fl_exact
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr)
  : Lemma
    (requires
      walk_pre g0 g start objs all_objs first_blue run_words /\
      linkable_heap g /\
      linkable_heap g0 /\
      SI.heap_objects_dense g /\
      Seq.length (objects zero_addr g) > 0 /\
      fl_sound g fp /\
      (run_words > 0 ==> run_words >= 2) /\
      (forall (t: hp_addr).
        U64.v zero_addr <= U64.v t /\
        U64.v t < U64.v (if run_words > 0
                         then hd_address (first_blue <: obj_addr)
                         else start) /\
        Seq.length (objects t g) > 0 ==>
        U64.v t + (U64.v (getWosize (read_word g t)) + 1) * U64.v mword
          <= U64.v (if run_words > 0
                    then hd_address (first_blue <: obj_addr)
                    else start)) /\
      (run_words > 0 ==> Seq.mem (first_blue <: obj_addr) (objects zero_addr g)) /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g0) /\ U64.v y >= U64.v start ==>
        Seq.mem y (objects zero_addr g)) /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ ~(Seq.mem y objs) ==>
        U64.v y < U64.v start) /\
      (forall (x: U64.t) (n: nat). on_fl g fp x n ==>
        U64.v x + U64.v mword <= U64.v (if run_words > 0
                                        then hd_address (first_blue <: obj_addr)
                                        else start)) /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ is_blue y g /\
        U64.v y < U64.v (if run_words > 0
                         then hd_address (first_blue <: obj_addr)
                         else start) ==>
        reachable_on_fl g fp y))
    (ensures (let (g', fp') = coalesce_aux g0 g objs first_blue run_words fp in
              fl_exact g' fp'))
    (decreases %[Seq.length objs; 1])

let coalesce_aux_white_step
  (g0 g: heap) (objs: seq obj_addr) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires Seq.length objs > 0 /\ ~(is_blue (Seq.head objs) g0))
    (ensures
      (let (g', fp') = flush_blue g first_blue run_words fp in
       coalesce_aux g0 g objs first_blue run_words fp ==
       coalesce_aux g0 g' (Seq.tail objs) 0UL 0 fp'))
  = ()

let rec coalesce_aux_fl_exact g0 g start objs first_blue run_words fp all_objs =
  if Seq.length objs = 0 then
    coalesce_empty_case g0 g start objs first_blue run_words fp all_objs
  else if is_blue (Seq.head objs) g0 then
    coalesce_blue_case g0 g start objs first_blue run_words fp all_objs
  else
    coalesce_white_case g0 g start objs first_blue run_words fp all_objs

and coalesce_blue_case g0 g start objs first_blue run_words fp all_objs =
  let obj = Seq.head objs in
  objects_nonempty_next start g0;
  f_address_spec start;
  assert (obj == f_address start);
  hd_address_spec obj;
  assert (U64.v (hd_address obj) == U64.v start);
  wosize_of_object_spec obj g0;
  let ws = U64.v (wosize_of_object obj g0) in
  assert (U64.v (getWosize (read_word g0 start)) == ws);
  assert (ws >= 1);
  let rest_start_nat = U64.v start + (ws + 1) * U64.v mword in

  let tail_sub (o: obj_addr)
    : Lemma (Seq.mem o (Seq.tail objs) ==> Seq.mem o all_objs)
    = mem_cons_lemma o obj (Seq.tail objs)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires tail_sub);
  let tail_white (o: obj_addr)
    : Lemma (Seq.mem o (Seq.tail objs) /\ is_white o g0 ==>
             read_word g (hd_address o) == read_word g0 (hd_address o))
    = mem_cons_lemma o obj (Seq.tail objs)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires tail_white);

  coalesce_aux_blue_step g0 g objs first_blue run_words fp;

  if run_words = 0 then begin
    let new_rw = ws + 1 in
    assert (Seq.mem obj (objects zero_addr g0));
    assert (U64.v obj >= U64.v start);
    assert (Seq.mem (obj <: obj_addr) (objects zero_addr g));
    assert (new_rw >= 2);
    assert (U64.v obj - U64.v mword + new_rw * U64.v mword == rest_start_nat);
    if rest_start_nat < heap_size then begin
      let next : hp_addr = U64.uint_to_t rest_start_nat in
      Seq.lemma_tl obj (objects next g0);
      assert (Seq.tail objs == objects next g0);
      coalesce_aux_fl_exact g0 g next (Seq.tail objs) obj new_rw fp all_objs
    end
    else begin
      objects_tail_empty_when_done start g0;
      Seq.lemma_eq_elim (Seq.tail objs) Seq.empty;
      coalesce_aux_empty g0 g obj new_rw fp;
      flush_blue_preserves_length g obj new_rw fp;
      assert (new_rw * U64.v mword <= heap_size);
      assert (heap_size < pow2 57);
      FStar.Math.Lemmas.lemma_div_le (new_rw * 8) (pow2 57) 8;
      FStar.Math.Lemmas.cancel_mul_div new_rw 8;
      pow2_57_div_8 ();
      assert (new_rw - 1 < pow2 54);
      flush_step_fl_exact g rest_start_nat obj new_rw fp
    end
  end
  else begin
    let new_rw = run_words + ws + 1 in
    assert (Seq.mem (first_blue <: obj_addr) (objects zero_addr g));
    assert (new_rw >= 2);
    assert (U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start);
    FStar.Math.Lemmas.distributivity_add_left run_words (ws + 1) (U64.v mword);
    assert (new_rw * U64.v mword == run_words * U64.v mword + (ws + 1) * U64.v mword);
    assert (U64.v first_blue - U64.v mword + new_rw * U64.v mword == rest_start_nat);
    if rest_start_nat < heap_size then begin
      let next : hp_addr = U64.uint_to_t rest_start_nat in
      Seq.lemma_tl obj (objects next g0);
      assert (Seq.tail objs == objects next g0);
      coalesce_aux_fl_exact g0 g next (Seq.tail objs) first_blue new_rw fp all_objs
    end
    else begin
      objects_tail_empty_when_done start g0;
      Seq.lemma_eq_elim (Seq.tail objs) Seq.empty;
      coalesce_aux_empty g0 g first_blue new_rw fp;
      flush_blue_preserves_length g first_blue new_rw fp;
      assert (new_rw * U64.v mword <= heap_size);
      assert (heap_size < pow2 57);
      FStar.Math.Lemmas.lemma_div_le (new_rw * 8) (pow2 57) 8;
      FStar.Math.Lemmas.cancel_mul_div new_rw 8;
      pow2_57_div_8 ();
      assert (new_rw - 1 < pow2 54);
      flush_step_fl_exact g rest_start_nat first_blue new_rw fp
    end
  end

and coalesce_white_case g0 g start objs first_blue run_words fp all_objs =
  let obj = Seq.head objs in
  objects_nonempty_next start g0;
  f_address_spec start;
  assert (obj == f_address start);
  hd_address_spec obj;
  assert (U64.v (hd_address obj) == U64.v start);
  wosize_of_object_spec obj g0;
  let ws = U64.v (wosize_of_object obj g0) in
  assert (U64.v (getWosize (read_word g0 start)) == ws);
  let rest_start_nat = U64.v start + (ws + 1) * U64.v mword in
  let (g_flush, fp_flush) = flush_blue g first_blue run_words fp in
  flush_blue_preserves_length g first_blue run_words fp;
  coalesce_aux_white_step g0 g objs first_blue run_words fp;

  let tail_sub (o: obj_addr)
    : Lemma (Seq.mem o (Seq.tail objs) ==> Seq.mem o all_objs)
    = mem_cons_lemma o obj (Seq.tail objs)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires tail_sub);

  if run_words = 0 then begin
    assert (g_flush == g);
    assert (fp_flush == fp);
    assert (read_word g (hd_address obj) == read_word g0 (hd_address obj));
    is_white_iff obj g0;
    is_blue_iff obj g;
    color_of_object_spec obj g0;
    color_of_object_spec obj g;
    assert (~(is_blue obj g));

    let tail_white (o: obj_addr)
      : Lemma (Seq.mem o (Seq.tail objs) /\ is_white o g0 ==>
               read_word g_flush (hd_address o) == read_word g0 (hd_address o))
      = mem_cons_lemma o obj (Seq.tail objs)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires tail_white);

    if rest_start_nat < heap_size then begin
      let next : hp_addr = U64.uint_to_t rest_start_nat in
      Seq.lemma_tl obj (objects next g0);
      assert (Seq.tail objs == objects next g0);
      let span (y: obj_addr)
        : Lemma
          (requires Seq.mem y (objects zero_addr g_flush) /\ U64.v y < U64.v next)
          (ensures U64.v y < U64.v start \/ y == obj)
        = if y = obj then ()
          else if Seq.mem y objs then begin
            Seq.cons_head_tail objs;
            mem_cons_lemma y obj (Seq.tail objs);
            objects_addresses_gt_start next g0 y
          end
          else ()
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires span);
      let straddle_flush (t: hp_addr)
          : Lemma
            (requires U64.v t < U64.v next /\ Seq.length (objects t g_flush) > 0)
            (ensures U64.v t + (U64.v (getWosize (read_word g_flush t)) + 1) * U64.v mword
                       <= U64.v next)
          = admit ()
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires straddle_flush);
      coalesce_aux_fl_exact g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs
    end
    else begin
      objects_tail_empty_when_done start g0;
      Seq.lemma_eq_elim (Seq.tail objs) Seq.empty;
      coalesce_aux_empty g0 g_flush 0UL 0 fp_flush;
      assert (fst (flush_blue g_flush 0UL 0 fp_flush) == g_flush);
      assert (snd (flush_blue g_flush 0UL 0 fp_flush) == fp_flush);
      assert (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ is_blue y g ==> U64.v y < U64.v start)
    end
  end
  else begin
    hd_address_spec (first_blue <: obj_addr);
    run_words_bound first_blue run_words start;
    if run_words = 1 then assert False
    else begin
      flush_step_fl_exact g (U64.v start) first_blue run_words fp;
      assert (fl_sound g_flush fp_flush);
      hd_address_spec obj;
      flush_blue_preserves_outside g first_blue run_words fp (hd_address obj);
      assert (read_word g_flush (hd_address obj) == read_word g0 (hd_address obj));
      is_white_iff obj g0;
      is_blue_iff obj g_flush;
      color_of_object_spec obj g0;
      color_of_object_spec obj g_flush;
      assert (~(is_blue obj g_flush));
      assert (U64.v first_blue < U64.v start);

      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        assert (Seq.tail objs == objects next g0);

        let tail_white (o: obj_addr)
          : Lemma
            (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
            (ensures read_word g_flush (hd_address o) == read_word g0 (hd_address o))
          = mem_cons_lemma o obj (Seq.tail objs);
            objects_addresses_gt_start next g0 o;
            hd_address_spec o;
            flush_blue_preserves_outside g first_blue run_words fp (hd_address o)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires tail_white);
        assert (U64.v obj == U64.v start + U64.v mword);
        assert (U64.v start < U64.v next);
        let span (y: obj_addr)
          : Lemma
            (requires Seq.mem y (objects zero_addr g_flush) /\
                      ~(Seq.mem y (Seq.tail objs)))
            (ensures U64.v y < U64.v next /\
                     (U64.v y < U64.v start \/ y == obj))
          = if y = obj then ()
            else if y = (first_blue <: obj_addr) then ()
            else begin
              flush_objects_reflect g first_blue run_words fp y;
              if Seq.mem y objs then begin
                Seq.cons_head_tail objs;
                mem_cons_lemma y obj (Seq.tail objs)
              end
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires span);
        let comp (y: obj_addr)
          : Lemma
            (requires Seq.mem y (objects zero_addr g_flush) /\ is_blue y g_flush /\
                      U64.v y < U64.v next)
            (ensures reachable_on_fl g_flush fp_flush y)
          = if Seq.mem y (Seq.tail objs) then
              objects_addresses_gt_start next g0 y
            else span y
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires comp);
        assert (U64.v obj == U64.v start + U64.v mword);
        assert (U64.v start < U64.v next);
        let above (y: obj_addr)
          : Lemma
            (requires Seq.mem y (objects zero_addr g0) /\ U64.v y >= U64.v next)
            (ensures Seq.mem y (objects zero_addr g_flush))
          = hd_address_spec y;
            SI.obj_in_objects_head g;
            SI.obj_in_objects_elim (f_address zero_addr) g;
            flush_objects_above g first_blue run_words fp y (U64.v start)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires above);
        flush_preserves_linkable g first_blue run_words fp;
        flush_blue_preserves_outside g first_blue run_words fp start;
        assert (read_word g_flush start == read_word g0 start);
        let straddle_flush (t: hp_addr)
          : Lemma
            (requires U64.v t < U64.v next /\ Seq.length (objects t g_flush) > 0)
            (ensures U64.v t + (U64.v (getWosize (read_word g_flush t)) + 1) * U64.v mword
                       <= U64.v next)
          = admit ()
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires straddle_flush);
        coalesce_aux_fl_exact g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs
      end
      else begin
        objects_tail_empty_when_done start g0;
        Seq.lemma_eq_elim (Seq.tail objs) Seq.empty;
        coalesce_aux_empty g0 g_flush 0UL 0 fp_flush;
        assert (fst (flush_blue g_flush 0UL 0 fp_flush) == g_flush);
        assert (snd (flush_blue g_flush 0UL 0 fp_flush) == fp_flush);
        let span2 (y: obj_addr)
          : Lemma
            (requires Seq.mem y (objects zero_addr g_flush) /\ is_blue y g_flush)
            (ensures reachable_on_fl g_flush fp_flush y)
          = if y = obj then ()
            else if y = (first_blue <: obj_addr) then ()
            else begin
              flush_objects_reflect g first_blue run_words fp y;
              if Seq.mem y objs then begin
                Seq.cons_head_tail objs;
                mem_cons_lemma y obj (Seq.tail objs)
              end
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires span2)
      end
    end
  end
 
#pop-options

val coalesce_establishes_fl_exact (g: heap) (fp: U64.t)
  : Lemma (requires post_sweep_strong g /\ linkable_heap g /\ fl_exact g fp)
          (ensures (let (g', fp') = coalesce g in fl_exact g' fp'))

let coalesce_establishes_fl_exact g fp =
  let aux (y: obj_addr)
    : Lemma (requires Seq.mem y (objects zero_addr g))
            (ensures ~(U64.v y < U64.v zero_addr))
    = objects_addresses_gt_start zero_addr g y
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  coalesce_aux_fl_exact g g zero_addr (objects zero_addr g) 0UL 0 0UL
    (objects zero_addr g)

*)
module SI = GC.Spec.SweepInv

module WE = GC.Spec.WalkEnd

#set-options "--z3rlimit 50 --fuel 2 --ifuel 1"

/// ---------------------------------------------------------------------------
/// Free-space accounting
/// ---------------------------------------------------------------------------
///
/// The conserved quantity is the whole size of a block: header plus fields.
/// Coalescing reclaims the absorbed blocks' headers into the merged block's
/// field area, so wosize is not conserved but whole size is.
///
/// Before: B1(wz 2) B2(wz 2) B3(wz 3) B4(wz 1) -- whole 3 + 3 + 4 + 2 = 12
/// After:  B2, B3 merged, B2 has wosize 6      -- whole 3 + 7 + 2 = 12

/// Machine words occupied by an object: its fields plus its header.
let whsize (g: heap) (x: obj_addr) : GTot nat =
  1 + U64.v (wosize_of_object x g)

/// Total whole size of the blue objects of a walk.
let rec blue_whsize (g: heap) (objs: seq obj_addr)
  : GTot nat (decreases Seq.length objs) =
  if Seq.length objs = 0 then 0
  else
    let x = Seq.head objs in
    (if is_blue x g then whsize g x else 0)
    + blue_whsize g (Seq.tail objs)

let total_blue_whsize (g: heap) : GTot nat =
  blue_whsize g (objects zero_addr g)

/// The walk position immediately above x.
let next_pos (g: heap) (x: obj_addr) : GTot nat =
  U64.v (hd_address x) + whsize g x * U64.v mword

/// y sits directly above x, with no gap.
let adjacent (g: heap) (x y: obj_addr) : prop =
  next_pos g x == U64.v (hd_address y)

/// p lies within x's header-and-fields extent.
let in_extent (g: heap) (x: obj_addr) (p: nat) : prop =
  U64.v (hd_address x) <= p /\ p < next_pos g x

/// p is covered by some blue object.
let blue_covered (g: heap) (p: nat) : prop =
  exists (x: obj_addr).
    Seq.mem x (objects zero_addr g) /\ is_blue x g /\ in_extent g x p

/// ---------------------------------------------------------------------------
/// Splitting the object walk at a position
/// ---------------------------------------------------------------------------

/// `a` is a position the walk from `s` lands on.
let rec walk_visits (g: heap) (s a: hp_addr)
  : GTot bool (decreases (heap_size - U64.v s)) =
  if U64.v s = U64.v a then true
  else if U64.v s + 8 >= heap_size then false
  else
    let wz = getWosize (read_word g s) in
    let next = U64.v s + (U64.v wz + 1) * 8 in
    if next > heap_size || next >= pow2 64 || next >= heap_size then false
    else begin
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      walk_visits g (mk_hp_addr next) a
    end

val objects_split_from (g: heap) (s a: hp_addr)
  : Lemma
    (requires Seq.length g == heap_size /\ walk_visits g s a)
    (ensures
      (exists (pre: seq obj_addr).
         objects s g == Seq.append pre (objects a g) /\
         (forall (y: obj_addr). Seq.mem y pre ==> U64.v (hd_address y) < U64.v a) /\
         (forall (y: obj_addr). Seq.mem y (objects a g) ==> U64.v (hd_address y) >= U64.v a)))
    (decreases (heap_size - U64.v s))

/// A visited position is at or above the walk start.
val walk_visits_above (g: heap) (s a: hp_addr)
  : Lemma (requires walk_visits g s a)
          (ensures U64.v s <= U64.v a)
          (decreases (heap_size - U64.v s))

let rec walk_visits_above g s a =
  if U64.v s = U64.v a then ()
  else begin
    let wz = getWosize (read_word g s) in
    let next = U64.v s + (U64.v wz + 1) * 8 in
    aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
    walk_visits_above g (mk_hp_addr next) a
  end

let rec objects_split_from g s a =
  let pred (pre: seq obj_addr) : prop =
    objects s g == Seq.append pre (objects a g) /\
    (forall (y: obj_addr). Seq.mem y pre ==> U64.v (hd_address y) < U64.v a) /\
    (forall (y: obj_addr). Seq.mem y (objects a g) ==> U64.v (hd_address y) >= U64.v a)
  in
  /// The suffix bound, in both cases, from the upstream walk lemma.
  let above (y: obj_addr)
    : Lemma (Seq.mem y (objects a g) ==> U64.v (hd_address y) >= U64.v a)
    = objects_addresses_gt_start a g y;
      hd_address_spec y
  in
  FStar.Classical.forall_intro above;

  if U64.v s = U64.v a then begin
    Seq.lemma_eq_elim (objects s g) (Seq.append Seq.empty (objects a g));
    FStar.Classical.exists_intro pred Seq.empty
  end
  else begin
    /// `walk_visits` took its recursive branch, so the walk at `s` is
    /// non-empty and steps to `next < heap_size`.
    let wz = getWosize (read_word g s) in
    let next = U64.v s + (U64.v wz + 1) * 8 in
    aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
    let nxt = mk_hp_addr next in
    walk_visits_above g nxt a;
    assert (U64.v s < U64.v a);
    WE.walk_end_step g s;
    WE.walk_head g s;
    f_address_spec s;
    let x : obj_addr = f_address s in
    hd_address_spec x;

    objects_split_from g nxt a;
    eliminate exists (pre: seq obj_addr).
        objects nxt g == Seq.append pre (objects a g) /\
        (forall (y: obj_addr). Seq.mem y pre ==> U64.v (hd_address y) < U64.v a) /\
        (forall (y: obj_addr). Seq.mem y (objects a g) ==> U64.v (hd_address y) >= U64.v a)
    with begin
      let pre' = Seq.cons x pre in
      Seq.lemma_tl x pre;
      Seq.lemma_eq_elim (objects s g) (Seq.cons x (objects nxt g));
      Seq.lemma_eq_elim (objects s g) (Seq.append pre' (objects a g));
      let below (y: obj_addr)
        : Lemma (Seq.mem y pre' ==> U64.v (hd_address y) < U64.v a)
        = mem_cons_lemma y x pre
      in
      FStar.Classical.forall_intro below;
      FStar.Classical.exists_intro pred pre'
    end
  end

val objects_split_at (g: heap) (a: hp_addr)
  : Lemma
    (requires Seq.length g == heap_size /\ walk_visits g zero_addr a)
    (ensures
      (exists (pre: seq obj_addr).
         objects zero_addr g == Seq.append pre (objects a g) /\
         (forall (y: obj_addr). Seq.mem y pre ==> U64.v (hd_address y) < U64.v a) /\
         (forall (y: obj_addr). Seq.mem y (objects a g) ==> U64.v (hd_address y) >= U64.v a)))

let objects_split_at g a = objects_split_from g zero_addr a

/// ---------------------------------------------------------------------------
/// The four obligations of `coalesce_correct`
/// ---------------------------------------------------------------------------

val coalesce_conserves_whsize (g: heap)
  : Lemma
    (requires post_sweep_strong g /\ SI.heap_objects_dense g /\
              Seq.length g == heap_size /\
              Seq.length (objects zero_addr g) > 0)
    (ensures total_blue_whsize (fst (coalesce g)) == total_blue_whsize g)

val coalesce_preserves_blue_coverage (g: heap)
  : Lemma
    (requires post_sweep_strong g /\ SI.heap_objects_dense g /\
              Seq.length g == heap_size /\
              Seq.length (objects zero_addr g) > 0)
    (ensures
      (let g' = fst (coalesce g) in
       forall (p: nat). p < heap_size ==> (blue_covered g' p <==> blue_covered g p)))

val coalesce_no_adjacent_blue (g: heap)
  : Lemma
    (requires post_sweep_strong g /\ SI.heap_objects_dense g /\
              Seq.length g == heap_size /\
              Seq.length (objects zero_addr g) > 0)
    (ensures
      (let g' = fst (coalesce g) in
       forall (x y: obj_addr).
         Seq.mem x (objects zero_addr g') /\ Seq.mem y (objects zero_addr g') /\
         is_blue x g' /\ is_blue y g' /\ adjacent g' x y ==> False))

val coalesce_preserves_white (g: heap)
  : Lemma
    (requires post_sweep_strong g /\ SI.heap_objects_dense g /\
              Seq.length g == heap_size /\
              Seq.length (objects zero_addr g) > 0)
    (ensures
      (let g' = fst (coalesce g) in
       forall (x: obj_addr).
         Seq.mem x (objects zero_addr g) /\ is_white x g ==>
         Seq.mem x (objects zero_addr g') /\ is_white x g' /\
         wosize_of_object x g' == wosize_of_object x g))

/// ---------------------------------------------------------------------------
/// White preservation: the walk invariant
/// ---------------------------------------------------------------------------
///
/// `g0` is the frozen heap the walk reads colours from; `g` is the heap being
/// built.

let white_inv
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (all_objs: seq obj_addr)
  : prop =
  walk_pre g0 g start objs all_objs first_blue run_words /\
  Seq.length g == heap_size /\
  Seq.length g0 == heap_size /\
  SI.heap_objects_dense g /\
  post_sweep_strong g0 /\
  /// 1. Above the cursor, the two heaps agree word for word.
  (forall (p: hp_addr). U64.v p >= U64.v start /\
                        U64.v p + U64.v mword <= heap_size ==>
     read_word g p == read_word g0 p) /\
  /// 2. The cursor is a walk position of both heaps.
  walk_visits g zero_addr start /\
  walk_visits g0 zero_addr start /\
  /// 3. The remaining walk is the same in both heaps.
  objects start g == objs /\
  /// 4. Every white object of `g0` already passed is still a white object of
  ///    `g`, with the same size.
  (forall (x: obj_addr).
     Seq.mem x (objects zero_addr g0) /\ is_white x g0 /\
     U64.v (hd_address x) < U64.v start ==>
     Seq.mem x (objects zero_addr g) /\ is_white x g /\
     wosize_of_object x g == wosize_of_object x g0) /\
  /// 5. The pending run contains no white object of `g`.  Runs are built from
  ///    blue objects only, so this is true; it is not derivable from the
  ///    clauses above, and `flush_preserves_white` needs it.
  (run_words > 0 ==>
    (forall (y: obj_addr).
       Seq.mem y (objects zero_addr g) /\ is_white y g /\
       U64.v (hd_address y) >= U64.v first_blue - U64.v mword /\
       U64.v (hd_address y) < U64.v start ==> False)) /\
  /// 6. "H-reachability": the pending run's floor is itself a walk position
  ///    of `g`.  When a run starts, `first_blue` is the object at `start`,
  ///    whose floor *is* `start`, and clause 2 already gives `walk_visits g
  ///    zero_addr start`; when a run extends, the floor doesn't move and the
  ///    blue case writes nothing to `g`.  Needed by `flush_white_transfer`/
  ///    `flush_density_transfer` (and hence the induction itself) to route
  ///    around the gap documented for `flush_preserves_white`/`density`.
  (run_words > 0 ==>
    walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)))

/// ---------------------------------------------------------------------------
/// What the flush does
/// ---------------------------------------------------------------------------
///
/// `run_end` is a `nat`, not an `hp_addr`: a run can end exactly at
/// `heap_size`, which is not a valid address.  In all three the run occupies
/// `[first_blue - mword, run_end)`, so every write lands strictly below
/// `run_end`.

/// The run's geometry, shared by the three statements below.
let run_at (first_blue: U64.t) (run_words: nat) (run_end: nat) : prop =
  run_words > 0 ==>
    (U64.v first_blue >= U64.v mword /\
     U64.v first_blue < heap_size /\
     U64.v first_blue % U64.v mword == 0 /\
     U64.v first_blue - U64.v mword + run_words * U64.v mword == run_end)

/// Two heaps that agree word-for-word at every position at or above `bound`
/// produce identical object walks from any starting point at or above
/// `bound`.  Pure write-locality: `objects` only ever reads the header at its
/// current cursor, and the cursor only moves forward.
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec objects_agree_above (g g1: heap) (s: hp_addr) (bound: nat)
  : Lemma
    (requires
      U64.v s >= bound /\
      (forall (q: hp_addr). U64.v q >= bound /\ U64.v q + U64.v mword <= heap_size ==>
         read_word g1 q == read_word g q))
    (ensures objects s g1 == objects s g)
    (decreases (heap_size - U64.v s))
  = if U64.v s + 8 >= heap_size then ()
    else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      if next_nat > heap_size || next_nat >= pow2 64 then ()
      else if next_nat >= heap_size then ()
      else begin
        aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
        objects_agree_above g g1 (mk_hp_addr next_nat) bound
      end
    end
#pop-options

/// The flush leaves the heap at and above `run_end` unchanged, word for word,
/// and hence leaves the walk there unchanged too.
///
/// Carries clauses 1 and 3 of the invariant across the white case.
val flush_preserves_walk
  (g: heap) (run_end: nat) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\ run_end <= heap_size /\
      run_at first_blue run_words run_end)
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       Seq.length g1 == heap_size /\
       (forall (p: hp_addr). U64.v p >= run_end /\
                             U64.v p + U64.v mword <= heap_size ==>
          read_word g1 p == read_word g p) /\
       (forall (s: hp_addr). U64.v s >= run_end ==>
          objects s g1 == objects s g)))

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let flush_preserves_walk g run_end first_blue run_words fp =
  let g1 = fst (flush_blue g first_blue run_words fp) in
  let outside (p: hp_addr)
    : Lemma
      (requires U64.v p >= run_end /\ U64.v p + U64.v mword <= heap_size)
      (ensures read_word g1 p == read_word g p)
    = flush_blue_preserves_outside g first_blue run_words fp p
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires outside);
  let walks (s: hp_addr)
    : Lemma
      (requires U64.v s >= run_end)
      (ensures objects s g1 == objects s g)
    = objects_agree_above g g1 s run_end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires walks)
#pop-options

/// Membership in a walk started at `s` implies the walk from `s` actually
/// visits the member's header position.  Purely structural: `objects` and
/// `walk_visits` share the same recursion, so this is the membership analogue
/// of `objects_addresses_gt_start`.
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec objects_mem_implies_walk_visits (g: heap) (s: hp_addr) (y: obj_addr)
  : Lemma
    (requires Seq.mem y (objects s g))
    (ensures walk_visits g s (hd_address y))
    (decreases (heap_size - U64.v s))
  = objects_nonempty_next s g;
    f_address_spec s;
    let obj = f_address s in
    if y = obj then begin
      hd_address_bounds y;
      hd_f_roundtrip s
    end else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      if next_nat >= heap_size then
        mem_cons_lemma y obj Seq.empty
      else begin
        let next = mk_hp_addr next_nat in
        mem_cons_lemma y obj (objects next g);
        objects_mem_implies_walk_visits g next y
      end
    end
#pop-options

/// Membership below the run transfers across the flush: if `y`'s header lies
/// strictly below `first_blue - mword`, and the walk from `s <= hd_address y`
/// reaches `y`, then the flushed heap's walk from `s` reaches `y` too.  The
/// entire path from `s` to `y` lies below the write range, so reads agree at
/// every step (`flush_blue_preserves_outside`) and the two walks step in
/// lockstep all the way to `y`.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec flush_membership_below
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  (s: hp_addr) (y: obj_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v s <= U64.v (hd_address y) /\
      U64.v (hd_address y) < U64.v first_blue - U64.v mword /\
      Seq.mem y (objects s g))
    (ensures Seq.mem y (objects s (fst (flush_blue g first_blue run_words fp))))
    (decreases (Seq.length (objects s g)))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    objects_nonempty_next s g;
    f_address_spec s;
    hd_address_spec y;
    let obj = f_address s in
    flush_blue_preserves_outside g first_blue run_words fp s;
    objects_nonempty_next s g1;
    if U64.v s = U64.v (hd_address y) then begin
      hd_address_bounds y;
      hd_f_roundtrip s;
      mem_cons_lemma y obj Seq.empty
    end else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      if next_nat >= heap_size then
        mem_cons_lemma y obj Seq.empty
      else begin
        let next = mk_hp_addr next_nat in
        mem_cons_lemma y obj (objects next g);
        objects_addresses_gt_start next g y;
        flush_membership_below g first_blue run_words fp next y;
        mem_cons_lemma y obj (objects next g1)
      end
    end
#pop-options

/// Mirror of `flush_membership_below`: membership below the run transfers
/// the other way, from the flushed heap back to the original.  Same proof,
/// `g` and `g1` exchanged (`flush_blue_preserves_outside`'s conclusion is a
/// plain equality, symmetric in use).
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec flush_membership_below_rev
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  (s: hp_addr) (y: obj_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v s <= U64.v (hd_address y) /\
      U64.v (hd_address y) < U64.v first_blue - U64.v mword /\
      Seq.mem y (objects s (fst (flush_blue g first_blue run_words fp))))
    (ensures Seq.mem y (objects s g))
    (decreases (Seq.length (objects s (fst (flush_blue g first_blue run_words fp)))))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    objects_nonempty_next s g1;
    f_address_spec s;
    hd_address_spec y;
    let obj = f_address s in
    flush_blue_preserves_outside g first_blue run_words fp s;
    objects_nonempty_next s g;
    if U64.v s = U64.v (hd_address y) then begin
      hd_address_bounds y;
      hd_f_roundtrip s;
      mem_cons_lemma y obj Seq.empty
    end else begin
      let wz = getWosize (read_word g1 s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      if next_nat >= heap_size then
        mem_cons_lemma y obj Seq.empty
      else begin
        let next = mk_hp_addr next_nat in
        mem_cons_lemma y obj (objects next g1);
        objects_addresses_gt_start next g1 y;
        flush_membership_below_rev g first_blue run_words fp next y;
        mem_cons_lemma y obj (objects next g)
      end
    end
#pop-options

/// No white object's header is written by the flush.
///
/// Carries clause 4 across the white case.  The last hypothesis is clause 5
/// of the invariant: the run holds no white object, so the writes cannot land
/// on one.
val flush_preserves_white
  (g: heap) (run_end: nat) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\ run_end <= heap_size /\
      SI.heap_objects_dense g /\
      run_at first_blue run_words run_end /\
      (run_words > 0 ==>
        (forall (y: obj_addr).
           Seq.mem y (objects zero_addr g) /\ is_white y g /\
           U64.v (hd_address y) >= U64.v first_blue - U64.v mword /\
           U64.v (hd_address y) < run_end ==> False)))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (y: obj_addr).
         Seq.mem y (objects zero_addr g) /\ is_white y g ==>
         Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
         wosize_of_object y g1 == wosize_of_object y g))

// NOT PROVABLE AS STATED -- see NOTES.md ("flush_preserves_white").  The
// `hd_address y < first_blue - mword` case (below the run) is a genuine,
// complete proof (`flush_membership_below` above does exactly this, and is
// used from `coalesce_aux_preserves_white`'s own corrected internal argument).
// The `hd_address y >= run_end` case (above the run) needs, in addition to
// this lemma's stated hypotheses, that the *original* heap's own walk from
// `zero_addr` actually reaches `first_blue - mword` (equivalently, that the
// run genuinely corresponds to a real run of objects in `g`, not merely to
// arithmetic satisfying `run_at`).  Without that, `g`'s real walk can enter
// the flushed range at a non-edge position under cover of an unconstrained
// blue object, in which case the flushed heap's reconstruction from that
// point does not match anything about `g`'s real structure past there, and
// the target white object need not be found again.  That extra fact is not
// among this lemma's hypotheses (nor derivable from
// `SI.heap_objects_dense g`, which only speaks about positions *already*
// known reachable from `zero_addr`), so the lemma is not provable in this
// generality.  Confirmed empirically: the natural proof (below-case complete,
// above-case via `flush_preserves_walk` + `objects_mem_implies_walk_visits`)
// leaves exactly one un-discharged goal, `Seq.mem y (objects zero_addr g1)`,
// which Z3 cannot close from the available hypotheses.
let flush_preserves_white g run_end first_blue run_words fp = admit ()

/// Density survives the flush: the merged block ends exactly where the run
/// ended, so the walk still tiles the heap.
val flush_preserves_density
  (g: heap) (run_end: nat) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\ run_end <= heap_size /\
      SI.heap_objects_dense g /\
      run_at first_blue run_words run_end)
    (ensures SI.heap_objects_dense (fst (flush_blue g first_blue run_words fp)))

// NOT PROVABLE AS STATED -- see NOTES.md ("flush_preserves_density").  Same
// root cause as `flush_preserves_white`: `heap_objects_dense_intro`'s
// obligation, for a position `start` that is a genuine member of `g1`'s own
// walk from `zero_addr`, needs `f_address next` to *also* be a member of
// `objects zero_addr g1` once `next` has room.  When `start`'s real object
// (below the run, hence identical in `g` and `g1`) has `next` landing
// strictly inside `(first_blue - mword, run_end)` -- not exactly at
// `first_blue - mword`, the one position `g1` gives a well-formed fresh
// header -- `g1` reads back either a zeroed field or the untyped `fp` value
// there.  `fp` is a completely unconstrained `U64.t` in this lemma's
// hypotheses, so for `run_words >= 2` its bits, misread as a header at
// `first_blue`, can be chosen to send `next` to an address with no relation
// to `g`'s real structure at all, breaking the density obligation outright.
// `SI.heap_objects_dense g` does not rule this out: it is conditioned on
// positions *already known* reachable from `zero_addr`, and gives no control
// over where an object below the run happens to end.
let flush_preserves_density g run_end first_blue run_words fp = admit ()

/// The cursor advances to the next walk position.
val walk_visits_step (g: heap) (s p q: hp_addr)
  : Lemma (requires walk_visits g s p /\ Seq.length (objects p g) > 0 /\
                    U64.v q == U64.v p +
                      (U64.v (getWosize (read_word g p)) + 1) * U64.v mword /\
                    U64.v q < heap_size)
          (ensures walk_visits g s q)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec walk_visits_step g s p q
  : Lemma (requires walk_visits g s p /\ Seq.length (objects p g) > 0 /\
                    U64.v q == U64.v p +
                      (U64.v (getWosize (read_word g p)) + 1) * U64.v mword /\
                    U64.v q < heap_size)
          (ensures walk_visits g s q)
          (decreases (heap_size - U64.v s))
  = let wz_p = getWosize (read_word g p) in
    aligned_plus_mul8 (U64.v p) (U64.v wz_p + 1);
    if U64.v s = U64.v p then ()
    else begin
      walk_visits_above g s p;
      let wz = getWosize (read_word g s) in
      let next = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      walk_visits_step g (mk_hp_addr next) p q
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Corrected white/density transfer, for internal use only
/// ---------------------------------------------------------------------------
///
/// `flush_preserves_white` and `flush_preserves_density` above are not
/// provable as stated (see NOTES.md).  What *is* true, and is what
/// `coalesce_aux_preserves_white`'s own induction actually has on hand, is
/// the same statement plus one extra fact that only the induction (not a
/// standalone lemma about an arbitrary heap) can supply: that the walk from
/// `zero_addr` reaches `first_blue - mword` -- i.e. that the run is not just
/// arithmetic, but genuinely starts where a real object of `g` begins.  The
/// lemmas below take that fact as an explicit extra hypothesis and are
/// completely proved.

/// Append membership, the general form of `mem_cons_lemma`.
let mem_append_lemma (#a: eqtype) (x: a) (lo hi: Seq.seq a)
  : Lemma (Seq.mem x (Seq.append lo hi) <==> Seq.mem x lo \/ Seq.mem x hi)
  = Seq.Properties.lemma_append_count lo hi

/// Two heaps that agree at every position below `bound` have the same walk
/// reachability below `bound`: if the walk from `s <= bound` reaches `bound`
/// in one heap, it reaches `bound` in the other.  Mirrors `objects_agree_above`
/// (which handles positions *above* a bound) for the below-a-bound case.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec walk_visits_agree_below (g g1: heap) (s bound: hp_addr)
  : Lemma
    (requires
      U64.v s <= U64.v bound /\
      (forall (q: hp_addr). U64.v q + U64.v mword <= U64.v bound ==>
         read_word g1 q == read_word g q) /\
      walk_visits g s bound)
    (ensures walk_visits g1 s bound)
    (decreases (heap_size - U64.v s))
  = if U64.v s = U64.v bound then ()
    else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      let next = mk_hp_addr next_nat in
      walk_visits_above g next bound;
      walk_visits_agree_below g g1 next bound
    end
#pop-options

/// `objects p g`'s nonemptiness (as opposed to its full structure) depends
/// only on the single header word at `p`: whether there is room for it, and
/// whether its wosize overflows past the end of the heap.  So agreement at
/// `p` alone -- not agreement everywhere `objects` subsequently reads --
/// already transfers nonemptiness.
let objects_nonempty_transfers (g g1: heap) (p: hp_addr)
  : Lemma
    (requires read_word g1 p == read_word g p /\ Seq.length (objects p g) > 0)
    (ensures Seq.length (objects p g1) > 0)
  = ()

/// Given that `g`'s own walk from `zero_addr` reaches exactly
/// `first_blue - mword` (the run's start), the flushed heap's walk reaches
/// `re` (`run_end`) too: below the run start the two heaps agree, so the walk
/// gets there the same way; from there, the flushed heap's own header -- the
/// fresh merged one -- takes it straight to `re` in one step.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let flush_reaches_run_end
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t) (re: hp_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)))
    (ensures walk_visits (fst (flush_blue g first_blue run_words fp)) zero_addr re)
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    walk_visits_above g zero_addr h;
    walk_visits_agree_below g g1 zero_addr h;
    flush_blue_header_spec g fb run_words fp;
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    walk_visits_step g1 zero_addr h re
#pop-options

/// The flushed heap's `zero_addr`-membership above the run agrees exactly
/// with the original heap's, given that both `first_blue - mword` and `re`
/// (`run_end`) are genuinely reached by `g`'s own walk from `zero_addr`.
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let flush_membership_above_run_iff
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t) (re: hp_addr) (y: obj_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)) /\
      walk_visits g zero_addr re /\
      U64.v (hd_address y) >= U64.v re)
    (ensures
      (Seq.mem y (objects zero_addr (fst (flush_blue g first_blue run_words fp))) <==>
       Seq.mem y (objects zero_addr g)))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    flush_reaches_run_end g first_blue run_words fp re;
    flush_preserves_walk g (U64.v re) first_blue run_words fp;
    objects_split_from g zero_addr re;
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g == Seq.append pre (objects re g) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v re) /\
        (forall (z: obj_addr). Seq.mem z (objects re g) ==> U64.v (hd_address z) >= U64.v re)
    with begin
      objects_split_from g1 zero_addr re;
      eliminate exists (pre1: seq obj_addr).
          objects zero_addr g1 == Seq.append pre1 (objects re g1) /\
          (forall (z: obj_addr). Seq.mem z pre1 ==> U64.v (hd_address z) < U64.v re) /\
          (forall (z: obj_addr). Seq.mem z (objects re g1) ==> U64.v (hd_address z) >= U64.v re)
      with begin
        mem_append_lemma y pre (objects re g);
        mem_append_lemma y pre1 (objects re g1)
      end
    end
#pop-options

/// The corrected `flush_preserves_white`: same conclusion, with the one
/// extra hypothesis that makes it true (see the section comment above).
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let flush_white_transfer
  (g: heap) (re: hp_addr) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)) /\
      walk_visits g zero_addr re /\
      (forall (y: obj_addr).
         Seq.mem y (objects zero_addr g) /\ is_white y g /\
         U64.v (hd_address y) >= U64.v first_blue - U64.v mword /\
         U64.v (hd_address y) < U64.v re ==> False))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (y: obj_addr).
         Seq.mem y (objects zero_addr g) /\ is_white y g ==>
         Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
         wosize_of_object y g1 == wosize_of_object y g))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let aux (y: obj_addr)
      : Lemma
        (requires Seq.mem y (objects zero_addr g) /\ is_white y g)
        (ensures
          Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
          wosize_of_object y g1 == wosize_of_object y g)
      = (if U64.v (hd_address y) < U64.v first_blue - U64.v mword then begin
           objects_addresses_gt_start zero_addr g y;
           hd_address_spec y;
           flush_membership_below g first_blue run_words fp zero_addr y
         end
         else if U64.v (hd_address y) < U64.v re then ()
         else
           flush_membership_above_run_iff g first_blue run_words fp re y);
        flush_blue_preserves_outside g first_blue run_words fp (hd_address y);
        is_white_iff y g; is_white_iff y g1;
        color_of_object_spec y g; color_of_object_spec y g1;
        wosize_of_object_spec y g; wosize_of_object_spec y g1
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// The flushed heap's walk from the run start unfolds to exactly one cons:
/// `first_blue` itself, then straight on to `re`.  Isolated as its own fact
/// (rather than inlined) so later proofs can use it without re-deriving the
/// header/wosize arithmetic each time.
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let flush_h_decompose
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t) (re: hp_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       walk_visits g1 zero_addr (hd_address (first_blue <: obj_addr)) /\
       objects (hd_address (first_blue <: obj_addr)) g1 ==
       Seq.cons (first_blue <: obj_addr) (objects re g1)))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    walk_visits_above g zero_addr h;
    walk_visits_agree_below g g1 zero_addr h;
    flush_blue_header_spec g fb run_words fp;
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    f_hd_roundtrip fb;
    objects_nonempty_next h g1
#pop-options

/// `first_blue` itself is a member of the flushed heap's walk, given
/// H-reachability.  Shared by `flush_no_interior_member`'s edge case and
/// `flush_density_transfer`'s "lands exactly on H" case.
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let flush_h_is_member
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t) (re: hp_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)))
    (ensures
      Seq.mem (first_blue <: obj_addr) (objects zero_addr (fst (flush_blue g first_blue run_words fp))))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    flush_h_decompose g first_blue run_words fp re;
    mem_cons_lemma fb fb (objects re g1);
    objects_split_from g1 zero_addr h;
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g1 == Seq.append pre (objects h g1) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h) /\
        (forall (z: obj_addr). Seq.mem z (objects h g1) ==> U64.v (hd_address z) >= U64.v h)
    with begin
      mem_append_lemma fb pre (objects h g1)
    end
#pop-options

/// No position strictly between `first_blue - mword` and `re` is ever a
/// member of the flushed heap's walk: the merged header takes the walk
/// straight from `H` to `re` in one step.
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let flush_no_interior_member
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t) (re: hp_addr) (y: obj_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)) /\
      U64.v (hd_address y) > U64.v (hd_address (first_blue <: obj_addr)) /\
      U64.v (hd_address y) < U64.v re)
    (ensures ~(Seq.mem y (objects zero_addr (fst (flush_blue g first_blue run_words fp)))))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    flush_h_decompose g first_blue run_words fp re;
    if Seq.mem y (objects zero_addr g1) then begin
      objects_split_from g1 zero_addr h;
      eliminate exists (pre: seq obj_addr).
          objects zero_addr g1 == Seq.append pre (objects h g1) /\
          (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h) /\
          (forall (z: obj_addr). Seq.mem z (objects h g1) ==> U64.v (hd_address z) >= U64.v h)
      with begin
        mem_append_lemma y pre (objects h g1);
        mem_cons_lemma y fb (objects re g1);
        hd_address_spec y;
        if y = fb then ()
        else if Seq.mem y (objects re g1) then objects_addresses_gt_start re g1 y
      end
    end
#pop-options

/// If the walk from `zero_addr` reaches both `start` and `bound`, with
/// `start <= bound`, it reaches `bound` starting from `start` too: the walk
/// is a single deterministic sequence, so reaching both means reaching one
/// from the other.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec walk_visits_prefix_gen (g: heap) (s start bound: hp_addr)
  : Lemma
    (requires
      U64.v s <= U64.v start /\ U64.v start <= U64.v bound /\
      walk_visits g s start /\ walk_visits g s bound)
    (ensures walk_visits g start bound)
    (decreases (heap_size - U64.v s))
  = if U64.v s = U64.v start then ()
    else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      let next = mk_hp_addr next_nat in
      walk_visits_above g next start;
      walk_visits_prefix_gen g next start bound
    end
#pop-options

let walk_visits_prefix (g: heap) (start bound: hp_addr)
  : Lemma
    (requires
      walk_visits g zero_addr start /\ walk_visits g zero_addr bound /\
      U64.v start <= U64.v bound)
    (ensures walk_visits g start bound)
  = walk_visits_above g zero_addr start;
    walk_visits_prefix_gen g zero_addr start bound

/// A walk position's next position never overshoots a target the walk
/// (from that position) is known to reach.
let walk_visits_next_bound (g: heap) (start bound: hp_addr)
  : Lemma
    (requires U64.v start < U64.v bound /\ walk_visits g start bound)
    (ensures
      (let wz = getWosize (read_word g start) in
       U64.v start + (U64.v wz + 1) * 8 <= U64.v bound))
  = let wz = getWosize (read_word g start) in
    let next_nat = U64.v start + (U64.v wz + 1) * 8 in
    aligned_plus_mul8 (U64.v start) (U64.v wz + 1);
    let next = mk_hp_addr next_nat in
    walk_visits_above g next bound

/// A position the walk from `zero_addr` reaches, with room for a header, is
/// never a dead end: density (plus the heap being nonempty to begin with)
/// carries the walk's own "doesn't stop early" property all the way from
/// `zero_addr` to any such position.  Needed because `walk_visits` only
/// records that the walk *reaches* a position, not that it *continues*
/// there -- that extra step is exactly what `SI.heap_objects_dense` supplies,
/// one hop at a time.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec walk_visits_dense_continues (g: heap) (s p: hp_addr)
  : Lemma
    (requires
      SI.heap_objects_dense g /\ walk_visits g s p /\
      Seq.length (objects s g) > 0 /\
      Seq.mem (f_address s) (objects zero_addr g) /\
      U64.v p + 8 < heap_size)
    (ensures Seq.length (objects p g) > 0)
    (decreases (heap_size - U64.v s))
  = if U64.v s = U64.v p then ()
    else begin
      SI.objects_dense_step s g;
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      let next = mk_hp_addr next_nat in
      if U64.v next + 8 < heap_size then begin
        SI.objects_dense_obj_in s g;
        SI.obj_in_objects_elim (U64.uint_to_t (next_nat + 8)) g;
        f_address_spec next;
        walk_visits_dense_continues g next p
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Density via `walk_end`: the scalar route
/// ---------------------------------------------------------------------------
///
/// The earlier attempt at `flush_density_transfer` went straight at
/// `SI.heap_objects_dense`'s quantified form -- for every walk position with
/// room, show the walk continues -- and got stuck exactly where `flush_preserves_white`
/// did: transferring a single position's own nonemptiness across the flush.
/// `GC.Spec.WalkEnd` gives a scalar restatement of density (`walk_end g
/// zero_addr` is *the* address where the whole-heap walk stops) and a pair of
/// bridging lemmas (`walk_end_of_dense_top`, `dense_from_walk_end`), so the
/// job reduces to showing the flush doesn't move that one number.  That's
/// what's done below: `flush_preserves_walk_end` is the only real content;
/// `flush_density_transfer` is three lines around it.

/// Membership in a walk between two points already visited: if the walk
/// visits `a` starting from `s`, its ultimate stopping point from `s` is the
/// same as from `a` -- `a` is just an intermediate checkpoint. Unconditional,
/// no heap-agreement hypotheses needed: `walk_visits` and `walk_end` share
/// the same recursive step, so visiting `a` en route doesn't change where
/// the walk eventually halts.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec walk_end_agree_on_visit (g: heap) (s a: hp_addr)
  : Lemma
    (requires walk_visits g s a)
    (ensures WE.walk_end g s == WE.walk_end g a)
    (decreases (heap_size - U64.v s))
  = if U64.v s = U64.v a then ()
    else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      let next = mk_hp_addr next_nat in
      walk_end_agree_on_visit g next a
    end
#pop-options

/// Two heaps that agree at every position at or above `bound` have the same
/// `walk_end` from any starting point at or above `bound`.  Mirrors
/// `objects_agree_above`.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec walk_end_agree_above (g g1: heap) (s: hp_addr) (bound: nat)
  : Lemma
    (requires
      U64.v s >= bound /\
      (forall (q: hp_addr). U64.v q >= bound /\ U64.v q + U64.v mword <= heap_size ==>
         read_word g1 q == read_word g q))
    (ensures WE.walk_end g1 s == WE.walk_end g s)
    (decreases (heap_size - U64.v s))
  = if U64.v s + 8 >= heap_size then ()
    else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      if next_nat > heap_size || next_nat >= pow2 64 then ()
      else if next_nat >= heap_size then ()
      else begin
        aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
        walk_end_agree_above g g1 (mk_hp_addr next_nat) bound
      end
    end
#pop-options

/// The flush leaves `walk_end` from `zero_addr` exactly where it was.  Below
/// the run, the two heaps agree, so the walk gets to `H` the same way in
/// both; from `H`, the flushed heap's one merged block covers exactly the
/// same ground -- `run_words` words -- as however many blocks the run held
/// in the original, so both heaps' walks resume at the same place, `re`;
/// above `re` the heaps agree again.  `H`- and `re`-reachability (from
/// `zero_addr`, in the original heap) are the same two extra facts
/// `flush_white_transfer` needed and for the same reason: they are what ties
/// `first_blue`/`run_words` to the heap's real layout, which
/// `SI.heap_objects_dense` alone does not supply.
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let flush_preserves_walk_end
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t) (re: hp_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)) /\
      walk_visits g zero_addr re)
    (ensures WE.walk_end (fst (flush_blue g first_blue run_words fp)) zero_addr == WE.walk_end g zero_addr)
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    walk_visits_above g zero_addr h;
    walk_visits_agree_below g g1 zero_addr h;
    walk_end_agree_on_visit g zero_addr h;
    walk_end_agree_on_visit g1 zero_addr h;
    walk_visits_prefix g h re;
    walk_end_agree_on_visit g h re;
    flush_blue_header_spec g fb run_words fp;
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    let above (q: hp_addr)
      : Lemma
        (requires U64.v q >= U64.v re)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires above);
    walk_end_agree_above g g1 re (U64.v re)
#pop-options

/// The corrected `flush_preserves_density`: same extra hypotheses as
/// `flush_white_transfer`, plus the heap being nonempty to begin with (needed
/// by `dense_from_walk_end`).  `walk_end_of_dense_top` turns density(`g`)
/// into a scalar fact, `flush_preserves_walk_end` carries that scalar fact
/// across the flush unchanged, and `dense_from_walk_end` turns it back into
/// density(`g1`).
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let flush_density_transfer
  (g: heap) (re: hp_addr) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      SI.heap_objects_dense g /\
      Seq.length (objects zero_addr g) > 0 /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)) /\
      walk_visits g zero_addr re)
    (ensures SI.heap_objects_dense (fst (flush_blue g first_blue run_words fp)))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let h = hd_address (first_blue <: obj_addr) in
    hd_address_spec (first_blue <: obj_addr);
    WE.walk_end_of_dense_top g;
    flush_preserves_walk_end g first_blue run_words fp re;
    (if U64.v zero_addr < U64.v h then begin
       flush_blue_preserves_outside g first_blue run_words fp zero_addr;
       objects_nonempty_transfers g g1 zero_addr
     end else
       flush_h_decompose g first_blue run_words fp re);
    WE.dense_from_walk_end g1
#pop-options

/// `flush_white_transfer`'s edge case: the run runs all the way to the end of
/// the heap.  No H-reachability needed at all -- there is nothing above the
/// run to worry about, so every white object is simply below it, and
/// `flush_membership_below` (which never needed the extra hypothesis) does
/// the whole job.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let flush_white_transfer_at_end
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == heap_size /\
      (forall (y: obj_addr).
         Seq.mem y (objects zero_addr g) /\ is_white y g /\
         U64.v (hd_address y) >= U64.v first_blue - U64.v mword ==> False))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (y: obj_addr).
         Seq.mem y (objects zero_addr g) /\ is_white y g ==>
         Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
         wosize_of_object y g1 == wosize_of_object y g))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let aux (y: obj_addr)
      : Lemma
        (requires Seq.mem y (objects zero_addr g) /\ is_white y g)
        (ensures
          Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
          wosize_of_object y g1 == wosize_of_object y g)
      = objects_addresses_gt_start zero_addr g y;
        hd_address_spec y;
        flush_membership_below g first_blue run_words fp zero_addr y;
        flush_blue_preserves_outside g first_blue run_words fp (hd_address y);
        is_white_iff y g; is_white_iff y g1;
        color_of_object_spec y g; color_of_object_spec y g1;
        wosize_of_object_spec y g; wosize_of_object_spec y g1
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// White preservation: the induction
/// ---------------------------------------------------------------------------

val coalesce_aux_preserves_white
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires white_inv g0 g start objs first_blue run_words all_objs)
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (x: obj_addr).
         Seq.mem x (objects zero_addr g0) /\ is_white x g0 ==>
         Seq.mem x (objects zero_addr g') /\ is_white x g' /\
         wosize_of_object x g' == wosize_of_object x g0))
    (decreases Seq.length objs)

/// If two heaps agree at `y`'s header word, `y`'s color and wosize agree
/// between them too -- both are read straight from that word.  Written once
/// because this exact conversion (word equality -> color/size equality, via
/// `is_white_iff`/`is_blue_iff`/`color_of_object_spec`/`wosize_of_object_spec`)
/// was being hand-written at every call site that needed it below, and was
/// missing at least one of its pieces at more than one of them.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let header_agree_transfers (g g': heap) (y: obj_addr)
  : Lemma
    (requires
      Seq.length g == heap_size /\ Seq.length g' == heap_size /\
      read_word g (hd_address y) == read_word g' (hd_address y))
    (ensures
      (is_white y g <==> is_white y g') /\
      (is_blue y g <==> is_blue y g') /\
      wosize_of_object y g == wosize_of_object y g')
  = color_of_object_spec y g;
    color_of_object_spec y g';
    is_white_iff y g;
    is_white_iff y g';
    is_blue_iff y g;
    is_blue_iff y g';
    wosize_of_object_spec y g;
    wosize_of_object_spec y g'
#pop-options

/// If `y` is on the walk from `lo`, then `lo <= hd_address y`: two
/// `mword`-aligned addresses that differ at all differ by a whole word.
/// General and independent of `white_inv` -- usable with `lo = zero_addr` or
/// `lo = nxt` alike.  Pulled out as its own lemma because the same
/// three-line arithmetic argument was being re-derived by hand at several
/// call sites below and got the wrong lemma (`hd_address_bounds`, an upper
/// bound, instead of `hd_address_spec`, the exact equation) more than once.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let mem_from_le_hd_address (lo: hp_addr) (g: heap) (y: obj_addr)
  : Lemma
    (requires Seq.mem y (objects lo g))
    (ensures U64.v lo <= U64.v (hd_address y))
  = objects_addresses_gt_start lo g y;
    hd_address_spec y;
    assert (U64.v y % U64.v mword == 0);
    assert (U64.v lo % U64.v mword == 0);
    FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v y) (U64.v lo) (U64.v mword);
    assert ((U64.v y - U64.v lo) % U64.v mword == 0);
    assert (U64.v y - U64.v lo >= U64.v mword)
#pop-options

/// The consequences of `white_inv` that every one of the four blue/white x
/// top/continuing case lemmas below needs.  Extracted into one place after
/// each kept re-deriving these independently and kept independently
/// forgetting one: `caw_top_white` lacked a conjunct `caw_top_blue` had,
/// `caw_top`'s blue branch lacked a case split its white branch had, and
/// `first_blue % mword == 0` went missing from three call sites at once.
let caw_shared_facts (g0 g: heap) (start: hp_addr) (first_blue: U64.t) (run_words: nat) : prop =
  (run_words > 0 ==>
     U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
     U64.v first_blue % U64.v mword == 0 /\
     U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start /\
     walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword))) /\
  (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==>
     U64.v zero_addr <= U64.v (hd_address y)) /\
  (forall (w: obj_addr).
     Seq.mem w (objects zero_addr g0) /\ is_white w g0 /\
     U64.v (hd_address w) < U64.v start ==>
     Seq.mem w (objects zero_addr g) /\ is_white w g /\
     wosize_of_object w g == wosize_of_object w g0) /\
  (run_words > 0 ==>
     (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ is_white y g /\
        U64.v (hd_address y) >= U64.v first_blue - U64.v mword /\
        U64.v (hd_address y) < U64.v start ==> False))

/// Establishes `caw_shared_facts` from `white_inv`, in the one place
/// (`white_inv`'s own clauses, directly available where this is called)
/// where each piece is genuinely primitive.  Called as the first line of
/// `caw_empty`, `caw_top`, `caw_blue_head` and `caw_white_head` -- the only
/// four places that actually have `white_inv` in scope.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let caw_unpack_white_inv
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (all_objs: seq obj_addr)
  : Lemma
    (requires white_inv g0 g start objs first_blue run_words all_objs)
    (ensures caw_shared_facts g0 g start first_blue run_words)
  = let alignment (y: obj_addr)
      : Lemma
        (requires Seq.mem y (objects zero_addr g))
        (ensures U64.v zero_addr <= U64.v (hd_address y))
      = mem_from_le_hd_address zero_addr g y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires alignment)
#pop-options

/// Empty case (`objs` empty): every `g0`-global white object has `hd < start`
/// (`objs == objects start g0 == Seq.empty`, so `objects_split_from` puts the
/// whole global list below `start`), so clause 4 already carries it to `g`;
/// `flush_white_transfer` carries it on to the flushed heap (vacuously, if
/// `run_words = 0`, since the flush is then the identity).
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let caw_empty
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      white_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs = 0)
    (ensures
      (let g' = fst (flush_blue g first_blue run_words fp) in
       forall (x: obj_addr).
         Seq.mem x (objects zero_addr g0) /\ is_white x g0 ==>
         Seq.mem x (objects zero_addr g') /\ is_white x g' /\
         wosize_of_object x g' == wosize_of_object x g0))
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    Seq.lemma_eq_elim objs Seq.empty;
    objects_split_from g0 zero_addr start;
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g0 == Seq.append pre (objects start g0) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v start) /\
        (forall (z: obj_addr). Seq.mem z (objects start g0) ==> U64.v (hd_address z) >= U64.v start)
    with begin
      (if run_words > 0 then begin
         run_words_bound first_blue run_words start;
         h_addr_agree first_blue;
         flush_white_transfer g start first_blue run_words fp
       end);
      let final (x: obj_addr)
        : Lemma
          (requires Seq.mem x (objects zero_addr g0) /\ is_white x g0)
          (ensures
            Seq.mem x (objects zero_addr (fst (flush_blue g first_blue run_words fp))) /\
            is_white x (fst (flush_blue g first_blue run_words fp)) /\
            wosize_of_object x (fst (flush_blue g first_blue run_words fp)) ==
              wosize_of_object x g0)
        = mem_append_lemma x pre (objects start g0)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires final)
    end
#pop-options

/// The shared "clause 5" step: extending a pending run by one more blue
/// object `x` (header at `start`) keeps it white-free, up to any bound `hi`
/// for which `x` is known to be the only `g`-object with header in
/// `[start, hi)`.  Used by both places a run gets extended and then
/// immediately flushed: the heap-top case (`hi = heap_size`) and the
/// ordinary continuing-run case (`hi = nxt`, the next cursor).
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let caw_extend_run_white_free
  (g0 g: heap) (start: hp_addr) (x: obj_addr) (hi: nat)
  (first_blue fb': U64.t) (run_words: nat)
  : Lemma
    (requires
      Seq.length g0 == heap_size /\ Seq.length g == heap_size /\
      hd_address x == start /\ is_blue x g0 /\
      (forall (p: hp_addr). U64.v p >= U64.v start /\ U64.v p + U64.v mword <= heap_size ==>
         read_word g p == read_word g0 p) /\
      (forall (y: obj_addr).
         Seq.mem y (objects zero_addr g) /\
         U64.v (hd_address y) >= U64.v start /\ U64.v (hd_address y) < hi ==> y == x) /\
      (run_words > 0 ==> U64.v first_blue >= U64.v mword) /\
      (run_words > 0 ==>
        (forall (y: obj_addr).
           Seq.mem y (objects zero_addr g) /\ is_white y g /\
           U64.v (hd_address y) >= U64.v first_blue - U64.v mword /\
           U64.v (hd_address y) < U64.v start ==> False)) /\
      fb' == (if run_words = 0 then x else first_blue))
    (ensures
      forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ is_white y g /\
        U64.v (hd_address y) >= U64.v fb' - U64.v mword /\
        U64.v (hd_address y) < hi ==> False)
  = let no_white (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g) /\ is_white y g /\
          U64.v (hd_address y) >= U64.v fb' - U64.v mword /\
          U64.v (hd_address y) < hi)
        (ensures False)
      = if U64.v (hd_address y) < U64.v start then begin
          if run_words = 0 then begin
            assert (fb' == x);
            hd_address_spec x
            // fb' - mword == start here, contradicting hd_address y < start
            // together with hd_address y >= fb' - mword.
          end else ()
          // fb' == first_blue here; hd_address y >= first_blue - mword and
          // < start is exactly the old clause 5, giving False directly.
        end
        else begin
          // start <= hd_address y < hi: `x` is the only such object, so
          // y = x, which is blue in g0 hence blue in g (read agreement at
          // `start`), contradicting is_white y g.
          assert (y == x);
          hd_address_bounds x;
          assert (read_word g start == read_word g0 start);
          header_agree_transfers g0 g x;
          assert (is_blue x g);
          is_blue_iff x g;
          is_white_iff x g
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires no_white)
#pop-options

/// Top-of-heap, `x` blue: the run absorbs `x` and ends exactly at the top of
/// the heap.  `x` is the only object at or above `start` (the walk is a
/// singleton there), so `caw_extend_run_white_free` with `hi = heap_size`
/// gives the "no white in the extended run" fact `flush_white_transfer_at_end`
/// needs.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let caw_top_blue
  (g0 g: heap) (start: hp_addr) (x: obj_addr)
  (first_blue fb': U64.t) (run_words rw': nat) (fp: U64.t)
  : Lemma
    (requires
      rw' > 0 /\
      Seq.length g0 == heap_size /\ Seq.length g == heap_size /\
      hd_address x == start /\ is_blue x g0 /\
      objects start g == Seq.cons x Seq.empty /\
      (forall (p: hp_addr). U64.v p >= U64.v start /\ U64.v p + U64.v mword <= heap_size ==>
         read_word g p == read_word g0 p) /\
      walk_visits g0 zero_addr start /\ walk_visits g zero_addr start /\
      (run_words > 0 ==> U64.v first_blue >= U64.v mword) /\
      (run_words > 0 ==> U64.v first_blue < heap_size) /\
      (run_words > 0 ==>
        (forall (y: obj_addr).
           Seq.mem y (objects zero_addr g) /\ is_white y g /\
           U64.v (hd_address y) >= U64.v first_blue - U64.v mword /\
           U64.v (hd_address y) < U64.v start ==> False)) /\
      fb' == (if run_words = 0 then x else first_blue) /\
      U64.v fb' - U64.v mword + rw' * U64.v mword == heap_size)
    (ensures
      (let g1 = fst (flush_blue g fb' rw' fp) in
       forall (y: obj_addr).
         Seq.mem y (objects zero_addr g) /\ is_white y g ==>
         Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
         wosize_of_object y g1 == wosize_of_object y g))
  = run_words_bound_top fb' rw';
    let only_x (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g) /\ U64.v (hd_address y) >= U64.v start)
        (ensures y == x)
      = objects_agree_above g0 g start (U64.v start);
        objects_split_from g zero_addr start;
        eliminate exists (pre: seq obj_addr).
            objects zero_addr g == Seq.append pre (objects start g) /\
            (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v start) /\
            (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
        with begin
          mem_append_lemma y pre (objects start g);
          mem_cons_lemma y x Seq.empty
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires only_x);
    caw_extend_run_white_free g0 g start x heap_size first_blue fb' run_words;
    flush_white_transfer_at_end g fb' rw' fp
#pop-options

/// Top-of-heap, `x` white: flush whatever run was pending (ending exactly at
/// `start`, unaffecting `x` itself, whose header is untouched throughout),
/// then handle `x` -- unaffected by the flush -- and everything below
/// `start` -- carried by clause 4 then `flush_white_transfer` -- separately.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
private let caw_top_white
  (g0 g g1: heap) (start: hp_addr) (x: obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      (g1, ()) == (fst (flush_blue g first_blue run_words fp), ()) /\
      Seq.length g0 == heap_size /\ Seq.length g == heap_size /\
      hd_address x == start /\ ~(is_blue x g0) /\
      objects start g0 == Seq.cons x Seq.empty /\
      (forall (p: hp_addr). U64.v p >= U64.v start /\ U64.v p + U64.v mword <= heap_size ==>
         read_word g p == read_word g0 p) /\
      walk_visits g0 zero_addr start /\ walk_visits g zero_addr start /\
      run_at first_blue run_words (U64.v start) /\
      (run_words > 0 ==> walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword))) /\
      (run_words > 0 ==>
        (forall (y: obj_addr).
           Seq.mem y (objects zero_addr g) /\ is_white y g /\
           U64.v (hd_address y) >= U64.v first_blue - U64.v mword /\
           U64.v (hd_address y) < U64.v start ==> False)) /\
      (forall (z: obj_addr).
         Seq.mem z (objects zero_addr g0) /\ is_white z g0 /\
         U64.v (hd_address z) < U64.v start ==>
         Seq.mem z (objects zero_addr g) /\ is_white z g /\
         wosize_of_object z g == wosize_of_object z g0))
    (ensures
      forall (z: obj_addr).
        Seq.mem z (objects zero_addr g0) /\ is_white z g0 ==>
        Seq.mem z (objects zero_addr g1) /\ is_white z g1 /\
        wosize_of_object z g1 == wosize_of_object z g0)
  = flush_preserves_walk g (U64.v start) first_blue run_words fp;
    (if run_words > 0 then begin
       run_words_bound first_blue run_words start;
       h_addr_agree first_blue;
       flush_white_transfer g start first_blue run_words fp;
       flush_reaches_run_end g first_blue run_words fp start
     end);
    objects_agree_above g0 g start (U64.v start);
    objects_split_from g1 zero_addr start;
    eliminate exists (pre1: seq obj_addr).
        objects zero_addr g1 == Seq.append pre1 (objects start g1) /\
        (forall (z: obj_addr). Seq.mem z pre1 ==> U64.v (hd_address z) < U64.v start) /\
        (forall (z: obj_addr). Seq.mem z (objects start g1) ==> U64.v (hd_address z) >= U64.v start)
    with begin
      objects_split_from g0 zero_addr start;
      eliminate exists (pre0: seq obj_addr).
          objects zero_addr g0 == Seq.append pre0 (objects start g0) /\
          (forall (z: obj_addr). Seq.mem z pre0 ==> U64.v (hd_address z) < U64.v start) /\
          (forall (z: obj_addr). Seq.mem z (objects start g0) ==> U64.v (hd_address z) >= U64.v start)
      with begin
        let final (z: obj_addr)
          : Lemma
            (requires Seq.mem z (objects zero_addr g0) /\ is_white z g0)
            (ensures
              Seq.mem z (objects zero_addr g1) /\ is_white z g1 /\
              wosize_of_object z g1 == wosize_of_object z g0)
          = mem_append_lemma z pre0 (objects start g0);
            if U64.v (hd_address z) < U64.v start then begin
              // Clause 4 carries z into g.  If a run is pending, clause 5
              // rules out z's header falling inside it (z is white), so z
              // sits strictly below the run's floor and
              // `flush_membership_below` carries it on into g1 untouched.
              if run_words = 0 then ()
              else begin
                assert (U64.v (hd_address z) < U64.v first_blue - U64.v mword);
                objects_addresses_gt_start zero_addr g z;
                hd_address_bounds z;
                hd_address_spec z;
                // z and zero_addr are both mword-aligned and z > zero_addr,
                // so their difference is a positive multiple of mword, hence
                // at least one whole word: zero_addr <= z - mword = hd_address z.
                assert (U64.v z % U64.v mword == 0);
                assert (U64.v zero_addr % U64.v mword == 0);
                FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v z) (U64.v zero_addr) (U64.v mword);
                assert ((U64.v z - U64.v zero_addr) % U64.v mword == 0);
                assert (U64.v z - U64.v zero_addr >= U64.v mword);
                assert (U64.v zero_addr <= U64.v (hd_address z));
                objects_mem_implies_walk_visits g zero_addr z;
                flush_membership_below g first_blue run_words fp zero_addr z;
                flush_blue_preserves_outside g first_blue run_words fp (hd_address z);
                header_agree_transfers g g1 z;
                assert (Seq.mem z (objects zero_addr g1));
                assert (is_white z g1);
                assert (wosize_of_object z g1 == wosize_of_object z g0)
              end
            end
            else begin
              // z = x: not part of any run, its header is untouched all the
              // way from g0 through g to g1.
              mem_cons_lemma z x Seq.empty;
              flush_blue_preserves_outside g first_blue run_words fp start;
              mem_append_lemma x pre1 (objects start g1);
              Seq.cons_head_tail (objects start g1);
              mem_cons_lemma x x (Seq.tail (objects start g1));
              assert (read_word g0 (hd_address z) == read_word g1 (hd_address z));
              header_agree_transfers g0 g1 z;
              assert (Seq.mem z (objects zero_addr g1));
              assert (is_white z g1);
              assert (wosize_of_object z g1 == wosize_of_object z g0)
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires final)
      end
    end
#pop-options

/// Clause 4, extended from `start` to `nxt` for the blue-continuing step:
/// below `start` it's the old clause 4 (a direct hypothesis here, not
/// buried in an ambient `white_inv`); at/above `start` and below `nxt`, `x`
/// is the only such object (`objects_cons_step_to`'s cons-shape), and it's
/// blue, so `is_white y g0` can't hold there.  A standalone top-level lemma
/// -- not a closure nested inside the much larger `caw_blue_head` proof --
/// so this gets its own small, focused proof context.  Below `start`, the
/// old clause 4 is extracted from its hypothesis via an explicit `eliminate
/// forall ... with y` rather than a bare `assert`, since automatic
/// E-matching was not firing the pattern reliably here.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let caw_clause4_ext_blue
  (g0 g: heap) (start nxt: hp_addr) (x: obj_addr)
  : Lemma
    (requires
      Seq.length g0 == heap_size /\ Seq.length g == heap_size /\
      walk_visits g0 zero_addr start /\
      is_blue x g0 /\
      objects start g0 == Seq.cons x (objects nxt g0) /\
      (forall (w: obj_addr).
         Seq.mem w (objects zero_addr g0) /\ is_white w g0 /\
         U64.v (hd_address w) < U64.v start ==>
         Seq.mem w (objects zero_addr g) /\ is_white w g /\
         wosize_of_object w g == wosize_of_object w g0))
    (ensures
      forall (y: obj_addr).
        Seq.mem y (objects zero_addr g0) /\ is_white y g0 /\
        U64.v (hd_address y) < U64.v nxt ==>
        Seq.mem y (objects zero_addr g) /\ is_white y g /\
        wosize_of_object y g == wosize_of_object y g0)
  = let step (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g0) /\ is_white y g0 /\
          U64.v (hd_address y) < U64.v nxt)
        (ensures
          Seq.mem y (objects zero_addr g) /\ is_white y g /\
          wosize_of_object y g == wosize_of_object y g0)
      = if U64.v (hd_address y) < U64.v start then begin
          is_white_iff y g0; color_of_object_spec y g0;
          eliminate forall (w: obj_addr).
              Seq.mem w (objects zero_addr g0) /\ is_white w g0 /\
              U64.v (hd_address w) < U64.v start ==>
              Seq.mem w (objects zero_addr g) /\ is_white w g /\
              wosize_of_object w g == wosize_of_object w g0
          with y;
          is_white_iff y g; color_of_object_spec y g
        end
        else begin
          objects_split_from g0 zero_addr start;
          eliminate exists (pre: seq obj_addr).
              objects zero_addr g0 == Seq.append pre (objects start g0) /\
              (forall (w: obj_addr). Seq.mem w pre ==> U64.v (hd_address w) < U64.v start) /\
              (forall (w: obj_addr). Seq.mem w (objects start g0) ==> U64.v (hd_address w) >= U64.v start)
          with begin
            mem_append_lemma y pre (objects start g0);
            mem_cons_lemma y x (objects nxt g0);
            // Rule out y in objects_nxt_g0: that would give hd_address y
            // >= nxt (mem_cons_lemma's second disjunct plus the shared
            // alignment-gap argument), contradicting hd_address y < nxt.
            // So y = x.
            (if not (y = x) then mem_from_le_hd_address nxt g0 y);
            is_white_iff y g0; is_blue_iff x g0;
            color_of_object_spec y g0; color_of_object_spec x g0
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires step)
#pop-options

/// The white-continuing-step analogue of `caw_clause4_ext_blue`: `x` here is
/// white, not blue, so at/above `start` (forced to equal `x`) the object
/// itself must be shown to survive the flush (its header sits below the
/// write range, untouched), rather than being ruled out by contradiction.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let caw_clause4_ext_white
  (g0 g g1: heap) (start nxt: hp_addr) (x: obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g0 == heap_size /\ Seq.length g == heap_size /\
      walk_visits g0 zero_addr start /\ walk_visits g1 zero_addr start /\
      caw_shared_facts g0 g start first_blue run_words /\
      read_word g start == read_word g0 start /\
      (g1, ()) == (fst (flush_blue g first_blue run_words fp), ()) /\
      hd_address x == start /\ ~(is_blue x g0) /\
      objects start g0 == Seq.cons x (objects nxt g0) /\
      objects start g1 == Seq.cons x (objects nxt g1))
    (ensures
      forall (y: obj_addr).
        Seq.mem y (objects zero_addr g0) /\ is_white y g0 /\
        U64.v (hd_address y) < U64.v nxt ==>
        Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
        wosize_of_object y g1 == wosize_of_object y g0)
  = // Unpack caw_shared_facts into raw, local facts once: the raw forall
    // form is what `eliminate forall` below needs (it looks for a literal
    // hypothesis of that shape in context, not an opaque named `prop` --
    // that was tried and does not work reliably).
    assert (run_words > 0 ==>
              U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
              U64.v first_blue % U64.v mword == 0 /\
              U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start);
    assert (forall (w: obj_addr).
              Seq.mem w (objects zero_addr g0) /\ is_white w g0 /\
              U64.v (hd_address w) < U64.v start ==>
              Seq.mem w (objects zero_addr g) /\ is_white w g /\
              wosize_of_object w g == wosize_of_object w g0);
    assert (run_words > 0 ==>
              (forall (w: obj_addr).
                 Seq.mem w (objects zero_addr g) /\ is_white w g /\
                 U64.v (hd_address w) >= U64.v first_blue - U64.v mword /\
                 U64.v (hd_address w) < U64.v start ==> False));
    let step (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g0) /\ is_white y g0 /\
          U64.v (hd_address y) < U64.v nxt)
        (ensures
          Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
          wosize_of_object y g1 == wosize_of_object y g0)
      = if U64.v (hd_address y) < U64.v start then begin
          // The old clause 4 (a raw, local hypothesis, just unpacked above)
          // transfers y from g0 into g.
          is_white_iff y g0; color_of_object_spec y g0;
          eliminate forall (w: obj_addr).
              Seq.mem w (objects zero_addr g0) /\ is_white w g0 /\
              U64.v (hd_address w) < U64.v start ==>
              Seq.mem w (objects zero_addr g) /\ is_white w g /\
              wosize_of_object w g == wosize_of_object w g0
          with y;
          is_white_iff y g; color_of_object_spec y g;
          if run_words = 0 then begin
            assert (g1 == g);
            assert (Seq.mem y (objects zero_addr g1));
            assert (is_white y g1);
            assert (wosize_of_object y g1 == wosize_of_object y g0)
          end
          else begin
            assert (Seq.mem y (objects zero_addr g));
            mem_from_le_hd_address zero_addr g y;
            objects_mem_implies_walk_visits g zero_addr y;
            flush_membership_below g first_blue run_words fp zero_addr y;
            flush_blue_preserves_outside g first_blue run_words fp (hd_address y);
            header_agree_transfers g g1 y;
            assert (Seq.mem y (objects zero_addr g1));
            assert (is_white y g1);
            assert (wosize_of_object y g1 == wosize_of_object y g0)
          end
        end else begin
          objects_split_from g0 zero_addr start;
          eliminate exists (pre: seq obj_addr).
              objects zero_addr g0 == Seq.append pre (objects start g0) /\
              (forall (w: obj_addr). Seq.mem w pre ==> U64.v (hd_address w) < U64.v start) /\
              (forall (w: obj_addr). Seq.mem w (objects start g0) ==> U64.v (hd_address w) >= U64.v start)
          with begin
            mem_append_lemma y pre (objects start g0);
            mem_cons_lemma y x (objects nxt g0);
            // Rule out y in objects_nxt_g0: that would give hd_address y
            // >= nxt (mem_cons_lemma's second disjunct plus the shared
            // alignment-gap argument), contradicting hd_address y < nxt.
            // So y = x.
            (if not (y = x) then mem_from_le_hd_address nxt g0 y);
            // y == x: its header (at `start`) is untouched, g0 through g to
            // g1 (clause 1 above start, then the flush leaves start alone).
            assert (read_word g start == read_word g0 start);
            flush_blue_preserves_outside g first_blue run_words fp start;
            header_agree_transfers g0 g y;
            header_agree_transfers g g1 y;
            mem_cons_lemma y x (objects nxt g1);
            // y = x is in objects start g1, a suffix of the walk from
            // zero_addr in g1; bridge it back to global membership.
            objects_split_from g1 zero_addr start;
            eliminate exists (pre1: seq obj_addr).
                objects zero_addr g1 == Seq.append pre1 (objects start g1) /\
                (forall (w: obj_addr). Seq.mem w pre1 ==> U64.v (hd_address w) < U64.v start) /\
                (forall (w: obj_addr). Seq.mem w (objects start g1) ==> U64.v (hd_address w) >= U64.v start)
            with begin
              mem_append_lemma y pre1 (objects start g1)
            end
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires step)
#pop-options

/// Heap-top boundary case: `objs` is non-empty but its head `x` reaches (or
/// overruns) the top of the heap.  Re-derives `x`, its wosize, and the
/// top-of-heap fact from `objs`, then dispatches to the blue/white lemmas
/// above.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
private let caw_top
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      white_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (z: obj_addr).
         Seq.mem z (objects zero_addr g0) /\ is_white z g0 ==>
         Seq.mem z (objects zero_addr g') /\ is_white z g' /\
         wosize_of_object z g' == wosize_of_object z g0))
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    let wz = U64.v (wosize_of_object x g0) in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    Seq.lemma_eq_elim (objects start g0) (Seq.cons x Seq.empty);
    Seq.lemma_eq_elim (Seq.tail objs) Seq.empty;
    if is_blue x g0 then begin
      let fb' = if run_words = 0 then x else first_blue in
      let rw' = run_words + wz + 1 in
      coalesce_aux_blue_step g0 g objs first_blue run_words fp;
      coalesce_aux_empty g0 g fb' rw' fp;
      hd_address_spec fb';
      caw_top_blue g0 g start x first_blue fb' run_words rw' fp;
      let gb = fst (flush_blue g fb' rw' fp) in
      assert (fst (coalesce_aux g0 g objs first_blue run_words fp) == gb);
      let final (z: obj_addr)
        : Lemma
          (requires Seq.mem z (objects zero_addr g0) /\ is_white z g0)
          (ensures
            Seq.mem z (objects zero_addr (fst (coalesce_aux g0 g objs first_blue run_words fp))) /\
            is_white z (fst (coalesce_aux g0 g objs first_blue run_words fp)) /\
            wosize_of_object z (fst (coalesce_aux g0 g objs first_blue run_words fp)) ==
              wosize_of_object z g0)
        = if U64.v (hd_address z) < U64.v start then begin
            // Clause 4 carries z from g0 into g; caw_top_blue's own
            // conclusion then carries it on from g into gb.
            assert (Seq.mem z (objects zero_addr g));
            assert (is_white z g);
            assert (wosize_of_object z g == wosize_of_object z g0);
            assert (Seq.mem z (objects zero_addr gb));
            assert (is_white z gb);
            assert (wosize_of_object z gb == wosize_of_object z g0)
          end else begin
            // z would have to be x (the only object of g0 at or above
            // start), but x is blue here, contradicting is_white z g0.
            objects_split_from g0 zero_addr start;
            eliminate exists (pre: seq obj_addr).
                objects zero_addr g0 == Seq.append pre (objects start g0) /\
                (forall (w: obj_addr). Seq.mem w pre ==> U64.v (hd_address w) < U64.v start) /\
                (forall (w: obj_addr). Seq.mem w (objects start g0) ==> U64.v (hd_address w) >= U64.v start)
            with begin
              mem_append_lemma z pre (objects start g0);
              mem_cons_lemma z x Seq.empty;
              is_white_iff z g0; is_blue_iff x g0;
              color_of_object_spec z g0; color_of_object_spec x g0
            end
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires final)
    end else begin
      coalesce_aux_white_step g0 g objs first_blue run_words fp;
      let (g1, fp1) = flush_blue g first_blue run_words fp in
      coalesce_aux_empty g0 g1 0UL 0 fp1;
      assert (fst (coalesce_aux g0 g objs first_blue run_words fp) == g1);
      caw_top_white g0 g g1 start x first_blue run_words fp;
      let final (z: obj_addr)
        : Lemma
          (requires Seq.mem z (objects zero_addr g0) /\ is_white z g0)
          (ensures
            Seq.mem z (objects zero_addr (fst (coalesce_aux g0 g objs first_blue run_words fp))) /\
            is_white z (fst (coalesce_aux g0 g objs first_blue run_words fp)) /\
            wosize_of_object z (fst (coalesce_aux g0 g objs first_blue run_words fp)) ==
              wosize_of_object z g0)
        = assert (Seq.mem z (objects zero_addr g1));
          assert (is_white z g1);
          assert (wosize_of_object z g1 == wosize_of_object z g0)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires final)
    end
#pop-options

/// The real induction.  A four-way dispatcher (empty / heap-top / blue head /
/// white head), each case a separately-verified lemma with its own small
/// proof context, rather than one huge recursive body.  The blue/white "head"
/// cases recurse, so they and the dispatcher form one mutual-recursion group
/// with a lexicographic `decreases`: the dispatcher is at phase 1 (so it can
/// call the phase-0 cases at the *same* `objs` length), and the cases
/// recurse back into the dispatcher only at a strictly smaller length.
///
/// "H-reachability" -- `white_inv`'s clause 6 -- is re-established at each
/// step: it's exactly `white_inv`'s own clause 2, evaluated at the moment a
/// run begins (`first_blue` is then `Seq.head objs`, whose header address is
/// `start`, and clause 2 already gives `walk_visits g zero_addr start`) --
/// and carries over unchanged while a run keeps accumulating (`first_blue`
/// doesn't change, and clause 1 gives `g` itself doesn't change in the blue
/// case either); see `caw_blue_head`. It's vacuous once a run flushes and
/// resets to `run_words = 0`; see `caw_white_head`.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec coalesce_aux_preserves_white_aux
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires white_inv g0 g start objs first_blue run_words all_objs)
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (x: obj_addr).
         Seq.mem x (objects zero_addr g0) /\ is_white x g0 ==>
         Seq.mem x (objects zero_addr g') /\ is_white x g' /\
         wosize_of_object x g' == wosize_of_object x g0))
    (decreases %[Seq.length objs; 1])
  = if Seq.length objs = 0 then
      caw_empty g0 g start objs first_blue run_words fp all_objs
    else begin
      let x = Seq.head objs in
      if U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size then
        caw_top g0 g start objs first_blue run_words fp all_objs
      else if is_blue x g0 then
        caw_blue_head g0 g start objs first_blue run_words fp all_objs
      else
        caw_white_head g0 g start objs first_blue run_words fp all_objs
    end

/// Ordinary step, `x` blue, not at the heap top: extend the pending run by
/// one object and recurse.  `objects_cons_step_to` gives the exact structural
/// fact `objects start g == x :: objects nxt g`; `caw_extend_run_white_free`
/// (with `hi = nxt`) carries clause 5 forward to the new cursor for the
/// recursive call's own precondition.
and caw_blue_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      white_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ is_blue (Seq.head objs) g0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (z: obj_addr).
         Seq.mem z (objects zero_addr g0) /\ is_white z g0 ==>
         Seq.mem z (objects zero_addr g') /\ is_white z g' /\
         wosize_of_object z g' == wosize_of_object z g0))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    let fb' = if run_words = 0 then x else first_blue in
    let rw' = run_words + wz + 1 in
    coalesce_aux_blue_step g0 g objs first_blue run_words fp;
    assert (read_word g start == read_word g0 start);
    header_agree_transfers g0 g x;
    walk_visits_step g zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    hd_address_spec fb';
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    let only_x (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g) /\
          U64.v (hd_address y) >= U64.v start /\ U64.v (hd_address y) < U64.v nxt)
        (ensures y == x)
      = objects_agree_above g0 g start (U64.v start);
        objects_split_from g zero_addr start;
        eliminate exists (pre: seq obj_addr).
            objects zero_addr g == Seq.append pre (objects start g) /\
            (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v start) /\
            (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
        with begin
          mem_append_lemma y pre (objects start g);
          mem_cons_lemma y x (objects nxt g);
          if y = x then ()
          else begin
            objects_addresses_gt_start nxt g y;
            hd_address_spec y
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires only_x);
    caw_extend_run_white_free g0 g start x (U64.v nxt) first_blue fb' run_words;
    // H-reachability for the new state `(g, nxt, fb', rw')`: if the run is
    // starting now, `fb' = x` and `hd_address x == start`, and clause 2
    // already gives `walk_visits g zero_addr start`; if it was already
    // accumulating, `fb' = first_blue` and `g` is unchanged, so white_inv's
    // own clause 6 at the *current* state carries over unchanged.
    (if run_words = 0 then h_addr_agree fb');
    // Establish white_inv's clauses at the new state one at a time, rather
    // than leaving the recursive call's whole precondition to be discharged
    // as one bundled query.
    assert (walk_pre g0 g nxt (Seq.tail objs) all_objs fb' rw');
    assert (Seq.length g == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g);
    assert (post_sweep_strong g0);
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g p == read_word g0 p);
    assert (walk_visits g zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g == Seq.tail objs);
    caw_clause4_ext_blue g0 g start nxt x;
    assert (rw' > 0 ==>
              (forall (y: obj_addr).
                 Seq.mem y (objects zero_addr g) /\ is_white y g /\
                 U64.v (hd_address y) >= U64.v fb' - U64.v mword /\
                 U64.v (hd_address y) < U64.v nxt ==> False));
    assert (rw' > 0 ==> walk_visits g zero_addr (mk_hp_addr (U64.v fb' - U64.v mword)));
    assert (white_inv g0 g nxt (Seq.tail objs) fb' rw' all_objs);
    coalesce_aux_preserves_white_aux g0 g nxt (Seq.tail objs) fb' rw' fp all_objs

/// Ordinary step, `x` white, not at the heap top: flush whatever run was
/// pending (via `flush_white_transfer`/`flush_density_transfer`, unchanged
/// from before), then recurse from `nxt` with a fresh, empty run.
/// `objects_cons_step_to` plus `flush_preserves_walk`'s `objects` agreement
/// (unconditional, at or above `start` in the flushed heap) gives the
/// recursive call's `objects nxt g1 == Seq.tail objs` obligation.
and caw_white_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      white_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ ~(is_blue (Seq.head objs) g0) /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (z: obj_addr).
         Seq.mem z (objects zero_addr g0) /\ is_white z g0 ==>
         Seq.mem z (objects zero_addr g') /\ is_white z g' /\
         wosize_of_object z g' == wosize_of_object z g0))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    coalesce_aux_white_step g0 g objs first_blue run_words fp;
    let (g1, fp1) = flush_blue g first_blue run_words fp in
    flush_preserves_walk g (U64.v start) first_blue run_words fp;
    (if run_words > 0 then begin
       run_words_bound first_blue run_words start;
       h_addr_agree first_blue;
       flush_white_transfer g start first_blue run_words fp;
       flush_density_transfer g start first_blue run_words fp;
       flush_reaches_run_end g first_blue run_words fp start
     end);
    assert (walk_visits g1 zero_addr start);
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    assert (objects nxt g0 == Seq.tail objs);
    assert (objects nxt g1 == Seq.tail objs);
    walk_visits_step g1 zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    // Establish white_inv's clauses at the new (reset) state one at a time,
    // rather than leaving the recursive call's whole precondition to be
    // discharged as one bundled query. Clauses 5/6 are vacuous at run_words
    // = 0.
    // Decompose walk_pre's own conjunction, rather than proving it whole.
    assert (Seq.tail objs == objects nxt g0);
    assert (all_objs == objects zero_addr g0);
    assert (Seq.length g0 == heap_size);
    assert (Seq.length g1 == heap_size);
    assert (post_sweep_strong g0);
    assert (post_sweep g0);
    (let subset (o: obj_addr)
       : Lemma (requires Seq.mem o (Seq.tail objs)) (ensures Seq.mem o all_objs)
       = mem_cons_lemma o x (Seq.tail objs)
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires subset));
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g1 p == read_word g0 p);
    (let word_agree (o: obj_addr)
       : Lemma
         (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
         (ensures read_word g1 (hd_address o) == read_word g0 (hd_address o))
       = assert (Seq.mem o (objects nxt g0));
         mem_from_le_hd_address nxt g0 o;
         hd_address_bounds o
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires word_agree));
    assert (walk_pre g0 g1 nxt (Seq.tail objs) all_objs 0UL 0);
    assert (Seq.length g1 == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g1);
    assert (post_sweep_strong g0);
    assert (walk_visits g1 zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g1 == Seq.tail objs);
    // Clause 4, extended from `start` to `nxt`: below `start` it's the old
    // clause 4 (ambient, at `start`) carried across the flush (clause 5 at
    // `start` rules out the "inside the run" case); at/above `start` and
    // below `nxt`, `objects_cons_step_to` forces y = x, whose header is
    // untouched by the flush (the write range ends strictly below `start`).
    objects_agree_above g g1 start (U64.v start);
    objects_agree_above g g1 nxt (U64.v start);
    assert (objects start g1 == Seq.cons x (objects nxt g1));
    assert (read_word g start == read_word g0 start);
    caw_clause4_ext_white g0 g g1 start nxt x first_blue run_words fp;
    assert (white_inv g0 g1 nxt (Seq.tail objs) 0UL 0 all_objs);
    coalesce_aux_preserves_white_aux
      g0 g1 nxt (Seq.tail objs) 0UL 0 fp1 all_objs
#pop-options

/// `white_inv`'s clause 6 ("H-reachability") closes the gap that otherwise
/// blocks this for `run_words > 0`, so the wrapper is now just the induction
/// directly, for every `run_words`.
let coalesce_aux_preserves_white
      g0 g start objs first_blue run_words fp all_objs =
  coalesce_aux_preserves_white_aux g0 g start objs first_blue run_words fp all_objs

let coalesce_preserves_white g =
  coalesce_aux_preserves_white g g zero_addr (objects zero_addr g) 0UL 0 0UL
                               (objects zero_addr g)

/// ---------------------------------------------------------------------------
/// Whole-size conservation: general helpers
/// ---------------------------------------------------------------------------
///
/// `blue_whsize` is additive over `Seq.append`, and agrees between two heaps
/// that agree at every header of every object in the sequence -- the two
/// facts the flush-conserves-whsize argument below is built from.

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec blue_whsize_append (g: heap) (s1 s2: seq obj_addr)
  : Lemma
    (ensures blue_whsize g (Seq.append s1 s2) == blue_whsize g s1 + blue_whsize g s2)
    (decreases (Seq.length s1))
  = if Seq.length s1 = 0 then
      Seq.lemma_eq_elim (Seq.append s1 s2) s2
    else begin
      let hd = Seq.head s1 in
      let tl = Seq.tail s1 in
      Seq.lemma_append_cons s1 s2;
      Seq.head_cons hd (Seq.append tl s2);
      Seq.lemma_tl hd (Seq.append tl s2);
      blue_whsize_append g tl s2
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec blue_whsize_agree (g g': heap) (s: seq obj_addr)
  : Lemma
    (requires
      Seq.length g == heap_size /\ Seq.length g' == heap_size /\
      (forall (y: obj_addr). Seq.mem y s ==>
         read_word g (hd_address y) == read_word g' (hd_address y)))
    (ensures blue_whsize g s == blue_whsize g' s)
    (decreases (Seq.length s))
  = if Seq.length s = 0 then ()
    else begin
      let x = Seq.head s in
      let t = Seq.tail s in
      Seq.cons_head_tail s;
      mem_cons_lemma x x t;
      header_agree_transfers g g' x;
      let mem_t (y: obj_addr)
        : Lemma (requires Seq.mem y t) (ensures Seq.mem y s)
        = mem_cons_lemma y x t
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires mem_t);
      blue_whsize_agree g g' t
    end
#pop-options

/// Prefix version of `objects_split_from`: if two heaps agree at every
/// header strictly below `bound` starting from `s`, and `g`'s walk from `s`
/// reaches `bound`, the segment of objects strictly below `bound` is built
/// identically in both heaps.  Proved by an induction that runs in lockstep
/// with `objects_split_from`'s own, tracking `g` and `g1` simultaneously.
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let rec objects_prefix_agree (g g1: heap) (s bound: hp_addr)
  : Lemma
    (requires
      Seq.length g == heap_size /\ Seq.length g1 == heap_size /\
      walk_visits g s bound /\
      (forall (q: hp_addr). U64.v q >= U64.v s /\ U64.v q + U64.v mword <= U64.v bound ==>
         read_word g1 q == read_word g q))
    (ensures
      (exists (pre: seq obj_addr).
         objects s g == Seq.append pre (objects bound g) /\
         objects s g1 == Seq.append pre (objects bound g1) /\
         (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v bound)))
    (decreases (heap_size - U64.v s))
  = if U64.v s = U64.v bound then begin
      Seq.lemma_eq_elim (objects s g) (Seq.append Seq.empty (objects bound g));
      Seq.lemma_eq_elim (objects s g1) (Seq.append Seq.empty (objects bound g1));
      FStar.Classical.exists_intro
        (fun (pre: seq obj_addr) ->
           objects s g == Seq.append pre (objects bound g) /\
           objects s g1 == Seq.append pre (objects bound g1) /\
           (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v bound))
        Seq.empty
    end
    else begin
      walk_visits_above g s bound;
      WE.walk_end_step g s;
      WE.walk_head g s;
      WE.walk_end_step g1 s;
      WE.walk_head g1 s;
      f_address_spec s;
      let x : obj_addr = f_address s in
      hd_address_spec x;
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      let nxt = mk_hp_addr next_nat in
      assert (read_word g1 s == read_word g s);
      objects_prefix_agree g g1 nxt bound;
      eliminate exists (pre: seq obj_addr).
          objects nxt g == Seq.append pre (objects bound g) /\
          objects nxt g1 == Seq.append pre (objects bound g1) /\
          (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v bound)
      with begin
        let pre' = Seq.cons x pre in
        Seq.lemma_tl x pre;
        Seq.lemma_eq_elim (objects s g) (Seq.cons x (objects nxt g));
        Seq.lemma_eq_elim (objects s g) (Seq.append pre' (objects bound g));
        Seq.lemma_eq_elim (objects s g1) (Seq.cons x (objects nxt g1));
        Seq.lemma_eq_elim (objects s g1) (Seq.append pre' (objects bound g1));
        let below (z: obj_addr)
          : Lemma (Seq.mem z pre' ==> U64.v (hd_address z) < U64.v bound)
          = mem_cons_lemma z x pre
        in
        FStar.Classical.forall_intro below;
        FStar.Classical.exists_intro
          (fun (pre2: seq obj_addr) ->
             objects s g == Seq.append pre2 (objects bound g) /\
             objects s g1 == Seq.append pre2 (objects bound g1) /\
             (forall (z: obj_addr). Seq.mem z pre2 ==> U64.v (hd_address z) < U64.v bound))
          pre'
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Whole-size conservation: the walk invariant
/// ---------------------------------------------------------------------------
///
/// Built on `white_inv` (reusing its H-reachability/density/walk-agreement
/// bookkeeping wholesale) plus exactly the two facts specific to whsize: the
/// running total is unchanged, and the pending run's own blue whsize equals
/// `run_words` (no separate "list of run objects" needed -- just the sum).
let whsize_inv
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (all_objs: seq obj_addr)
  : prop =
  white_inv g0 g start objs first_blue run_words all_objs /\
  total_blue_whsize g0 == total_blue_whsize g /\
  (run_words > 0 ==>
    blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
      run_words + blue_whsize g objs)

/// A flush conserves the heap's total blue whsize: the run's own objects
/// (summing to `run_words`, by `whsize_inv`'s clause) become one merged
/// object of whsize `run_words`; everything else -- below the run, and from
/// `start` on -- is untouched, so its own contribution is unaffected.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let flush_conserves_whsize
  (g: heap) (start: hp_addr) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start /\
      walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)) /\
      blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
        run_words + blue_whsize g (objects start g))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       blue_whsize g1 (objects zero_addr g1) == blue_whsize g (objects zero_addr g)))
  = let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let g1 = fst (flush_blue g first_blue run_words fp) in
    // Below `h`: unaffected by the flush -- exactly `flush_blue_preserves_outside`'s
    // own "below" condition, so the same fact both feeds `objects_prefix_agree`
    // (to carry the split witness across to `g1`) and `blue_whsize_agree`.
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    objects_prefix_agree g g1 zero_addr h;
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g == Seq.append pre (objects h g) /\
        objects zero_addr g1 == Seq.append pre (objects h g1) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h)
    with begin
      blue_whsize_append g pre (objects h g);
      flush_h_decompose g first_blue run_words fp start;
      flush_preserves_walk g (U64.v start) first_blue run_words fp;
      flush_blue_header_spec g fb run_words fp;
      let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
      makeHeader_getWosize wz_u64 Blue 0UL;
      makeHeader_getColor wz_u64 Blue 0UL;
      wosize_of_object_spec fb g1;
      color_of_object_spec fb g1;
      is_blue_iff fb g1;
      assert (is_blue fb g1);
      assert (wosize_of_object fb g1 == wz_u64);
      assert (whsize g1 fb == run_words);
      // `pre`'s own header words agree between `g` and `g1` (each element's
      // hd_address is < h, hence its whole word is below h).
      let pre_agree (z: obj_addr)
        : Lemma
          (requires Seq.mem z pre)
          (ensures read_word g (hd_address z) == read_word g1 (hd_address z))
        = hd_address_spec z;
          FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v h) (U64.v (hd_address z)) (U64.v mword);
          assert (U64.v h - U64.v (hd_address z) >= U64.v mword);
          flush_blue_preserves_outside g first_blue run_words fp (hd_address z)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires pre_agree);
      blue_whsize_agree g g1 pre;
      // At or above `start`: unaffected by the flush.
      let above (z: obj_addr)
        : Lemma
          (requires Seq.mem z (objects start g))
          (ensures read_word g (hd_address z) == read_word g1 (hd_address z))
        = mem_from_le_hd_address start g z;
          flush_blue_preserves_outside g first_blue run_words fp (hd_address z)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires above);
      blue_whsize_agree g g1 (objects start g);
      Seq.head_cons fb (objects start g1);
      Seq.lemma_tl fb (objects start g1);
      blue_whsize_append g1 pre (Seq.cons fb (objects start g1));
      Seq.lemma_eq_elim (objects h g1) (Seq.cons fb (objects start g1))
    end
#pop-options

/// The top-of-heap analogue of `flush_conserves_whsize`: the run ends
/// exactly at `heap_size`, which is not itself a valid `hp_addr`, so there is
/// no "tail" beyond the run at all -- mirrors `flush_white_transfer_at_end`.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let flush_conserves_whsize_at_end
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == heap_size /\
      walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)) /\
      blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) == run_words)
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       blue_whsize g1 (objects zero_addr g1) == blue_whsize g (objects zero_addr g)))
  = let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let g1 = fst (flush_blue g first_blue run_words fp) in
    // `h + mword == first_blue < heap_size`, so both `objects h g` and
    // `objects h g1` are nonempty -- nonemptiness of `objects s _` depends
    // only on `s` versus `heap_size`, never on heap content.
    assert (U64.v h + U64.v mword == U64.v first_blue);
    assert (Seq.length (objects h g) > 0);
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    objects_prefix_agree g g1 zero_addr h;
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g == Seq.append pre (objects h g) /\
        objects zero_addr g1 == Seq.append pre (objects h g1) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h)
    with begin
      blue_whsize_append g pre (objects h g);
      // `pre`'s own header words agree between `g` and `g1`.
      let pre_agree (z: obj_addr)
        : Lemma
          (requires Seq.mem z pre)
          (ensures read_word g (hd_address z) == read_word g1 (hd_address z))
        = hd_address_spec z;
          FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v h) (U64.v (hd_address z)) (U64.v mword);
          assert (U64.v h - U64.v (hd_address z) >= U64.v mword);
          flush_blue_preserves_outside g first_blue run_words fp (hd_address z)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires pre_agree);
      blue_whsize_agree g g1 pre;
      // `objects h g1` is the merged block alone: its header gives wosize
      // `run_words - 1`, so its own extent reaches exactly `heap_size`.
      flush_blue_header_spec g fb run_words fp;
      let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
      makeHeader_getWosize wz_u64 Blue 0UL;
      makeHeader_getColor wz_u64 Blue 0UL;
      wosize_of_object_spec fb g1;
      color_of_object_spec fb g1;
      is_blue_iff fb g1;
      assert (is_blue fb g1);
      assert (wosize_of_object fb g1 == wz_u64);
      f_hd_roundtrip fb;
      assert (Seq.length (objects h g1) > 0);
      WE.walk_end_step g1 h;
      Seq.lemma_eq_elim (objects h g1) (Seq.cons fb Seq.empty);
      blue_whsize_append g1 pre (Seq.cons fb Seq.empty)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Whole-size conservation: the induction
/// ---------------------------------------------------------------------------

/// The shared "extend the run by one blue object" whsize step: consuming
/// `x` (blue in `g0`, header at `start`) contributes exactly `wz + 1` to
/// `blue_whsize g objs`, since `objs == Seq.cons x (Seq.tail objs)` and `x`'s
/// header agrees between `g0` and `g`.  Used by both `caw_ws_top` (where
/// `Seq.tail objs` is empty) and `caw_ws_blue_head` (where it isn't) --
/// factored out once it was needed a second time.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let caw_ws_head_whsize
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  : Lemma
    (requires
      Seq.length g0 == heap_size /\ Seq.length g == heap_size /\
      Seq.length objs > 0 /\ hd_address (Seq.head objs) == start /\
      is_blue (Seq.head objs) g0 /\
      read_word g start == read_word g0 start)
    (ensures
      blue_whsize g objs ==
        (U64.v (wosize_of_object (Seq.head objs) g0) + 1) + blue_whsize g (Seq.tail objs))
  = let x = Seq.head objs in
    Seq.cons_head_tail objs;
    header_agree_transfers g0 g x;
    Seq.head_cons x (Seq.tail objs);
    Seq.lemma_tl x (Seq.tail objs)
#pop-options

/// Empty case: flush whatever run is pending, using `flush_conserves_whsize`
/// (vacuous if `run_words = 0`, since the flush is then the identity).
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let caw_ws_empty
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      whsize_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs = 0)
    (ensures
      total_blue_whsize g0 == total_blue_whsize (fst (flush_blue g first_blue run_words fp)))
  = if run_words = 0 then ()
    else begin
      run_words_bound first_blue run_words start;
      assert (objects start g == objs);
      assert (blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
                run_words + blue_whsize g objs);
      flush_conserves_whsize g start first_blue run_words fp
    end
#pop-options

/// Top-of-heap case: `x` is the last object.  Blue: extend the run and flush
/// it against the top of the heap (`flush_conserves_whsize_at_end`).  White:
/// the pending run (if any) ends exactly at `start` -- an ordinary flush,
/// `x` itself untouched.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
private let caw_ws_top
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      whsize_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size))
    (ensures
      total_blue_whsize g0 ==
        total_blue_whsize (fst (coalesce_aux g0 g objs first_blue run_words fp)))
  = let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    let wz = U64.v (wosize_of_object x g0) in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    Seq.lemma_eq_elim (objects start g0) (Seq.cons x Seq.empty);
    Seq.lemma_eq_elim (Seq.tail objs) Seq.empty;
    assert (objects start g == objs);
    if is_blue x g0 then begin
      let fb' = if run_words = 0 then x else first_blue in
      let rw' = run_words + wz + 1 in
      coalesce_aux_blue_step g0 g objs first_blue run_words fp;
      coalesce_aux_empty g0 g fb' rw' fp;
      hd_address_spec fb';
      h_addr_agree fb';
      assert (U64.v fb' - U64.v mword + rw' * U64.v mword == heap_size);
      caw_ws_head_whsize g0 g start objs;
      assert (blue_whsize g objs == (wz + 1) + blue_whsize g (Seq.tail objs));
      assert (blue_whsize g (Seq.tail objs) == 0);
      assert (blue_whsize g objs == wz + 1);
      (if run_words = 0 then begin
         assert (hd_address fb' == start);
         assert (blue_whsize g (objects (mk_hp_addr (U64.v fb' - U64.v mword)) g) == rw')
       end else begin
         assert (blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
                   run_words + blue_whsize g objs);
         assert (blue_whsize g (objects (mk_hp_addr (U64.v fb' - U64.v mword)) g) == rw')
       end);
      run_words_bound_top fb' rw';
      assert (walk_visits g zero_addr (mk_hp_addr (U64.v fb' - U64.v mword)));
      flush_conserves_whsize_at_end g fb' rw' fp;
      assert (total_blue_whsize g0 == total_blue_whsize (fst (flush_blue g fb' rw' fp)))
    end else begin
      coalesce_aux_white_step g0 g objs first_blue run_words fp;
      let (g1, fp1) = flush_blue g first_blue run_words fp in
      coalesce_aux_empty g0 g1 0UL 0 fp1;
      if run_words = 0 then ()
      else begin
        run_words_bound first_blue run_words start;
        assert (blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
                  run_words + blue_whsize g objs);
        Seq.head_cons x (Seq.tail objs);
        Seq.lemma_tl x (Seq.tail objs);
        is_blue_iff x g0;
        header_agree_transfers g0 g x;
        assert (~(is_blue x g));
        assert (blue_whsize g objs == 0 + blue_whsize g (Seq.tail objs));
        assert (blue_whsize g (Seq.tail objs) == 0);
        assert (blue_whsize g objs == 0);
        assert (blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) == run_words);
        flush_conserves_whsize g start first_blue run_words fp
      end
    end
#pop-options

/// The real induction.  Four-way dispatcher (empty / heap-top / blue head /
/// white head), mirroring `coalesce_aux_preserves_white_aux`'s own structure
/// and reusing its leaf lemmas (`caw_extend_run_white_free`,
/// `caw_clause4_ext_blue`, `caw_clause4_ext_white`) wherever the bookkeeping
/// is identical -- only the whsize-specific facts are new here.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec coalesce_aux_conserves_whsize_aux
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires whsize_inv g0 g start objs first_blue run_words all_objs)
    (ensures
      total_blue_whsize g0 ==
        total_blue_whsize (fst (coalesce_aux g0 g objs first_blue run_words fp)))
    (decreases %[Seq.length objs; 1])
  = if Seq.length objs = 0 then
      caw_ws_empty g0 g start objs first_blue run_words fp all_objs
    else begin
      let x = Seq.head objs in
      if U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size then
        caw_ws_top g0 g start objs first_blue run_words fp all_objs
      else if is_blue x g0 then
        caw_ws_blue_head g0 g start objs first_blue run_words fp all_objs
      else
        caw_ws_white_head g0 g start objs first_blue run_words fp all_objs
    end

and caw_ws_blue_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      whsize_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ is_blue (Seq.head objs) g0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      total_blue_whsize g0 ==
        total_blue_whsize (fst (coalesce_aux g0 g objs first_blue run_words fp)))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    let fb' = if run_words = 0 then x else first_blue in
    let rw' = run_words + wz + 1 in
    coalesce_aux_blue_step g0 g objs first_blue run_words fp;
    assert (read_word g start == read_word g0 start);
    header_agree_transfers g0 g x;
    walk_visits_step g zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    hd_address_spec fb';
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    let only_x (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g) /\
          U64.v (hd_address y) >= U64.v start /\ U64.v (hd_address y) < U64.v nxt)
        (ensures y == x)
      = objects_agree_above g0 g start (U64.v start);
        objects_split_from g zero_addr start;
        eliminate exists (pre: seq obj_addr).
            objects zero_addr g == Seq.append pre (objects start g) /\
            (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v start) /\
            (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
        with begin
          mem_append_lemma y pre (objects start g);
          mem_cons_lemma y x (objects nxt g);
          if y = x then ()
          else begin
            objects_addresses_gt_start nxt g y;
            hd_address_spec y
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires only_x);
    caw_extend_run_white_free g0 g start x (U64.v nxt) first_blue fb' run_words;
    (if run_words = 0 then h_addr_agree fb');
    assert (walk_pre g0 g nxt (Seq.tail objs) all_objs fb' rw');
    assert (Seq.length g == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g);
    assert (post_sweep_strong g0);
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g p == read_word g0 p);
    assert (walk_visits g zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g == Seq.tail objs);
    caw_clause4_ext_blue g0 g start nxt x;
    assert (rw' > 0 ==>
              (forall (y: obj_addr).
                 Seq.mem y (objects zero_addr g) /\ is_white y g /\
                 U64.v (hd_address y) >= U64.v fb' - U64.v mword /\
                 U64.v (hd_address y) < U64.v nxt ==> False));
    assert (rw' > 0 ==> walk_visits g zero_addr (mk_hp_addr (U64.v fb' - U64.v mword)));
    assert (white_inv g0 g nxt (Seq.tail objs) fb' rw' all_objs);
    // whsize_inv's own two extra clauses at the new state.
    caw_ws_head_whsize g0 g start objs;
    assert (blue_whsize g objs == (wz + 1) + blue_whsize g (Seq.tail objs));
    (if run_words = 0 then begin
       assert (hd_address fb' == start);
       assert (blue_whsize g (objects (mk_hp_addr (U64.v fb' - U64.v mword)) g) ==
                 rw' + blue_whsize g (Seq.tail objs))
     end else begin
       assert (blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
                 run_words + blue_whsize g objs);
       assert (blue_whsize g (objects (mk_hp_addr (U64.v fb' - U64.v mword)) g) ==
                 rw' + blue_whsize g (Seq.tail objs))
     end);
    assert (total_blue_whsize g0 == total_blue_whsize g);
    assert (whsize_inv g0 g nxt (Seq.tail objs) fb' rw' all_objs);
    coalesce_aux_conserves_whsize_aux g0 g nxt (Seq.tail objs) fb' rw' fp all_objs

and caw_ws_white_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      whsize_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ ~(is_blue (Seq.head objs) g0) /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      total_blue_whsize g0 ==
        total_blue_whsize (fst (coalesce_aux g0 g objs first_blue run_words fp)))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    coalesce_aux_white_step g0 g objs first_blue run_words fp;
    let (g1, fp1) = flush_blue g first_blue run_words fp in
    flush_preserves_walk g (U64.v start) first_blue run_words fp;
    (if run_words > 0 then begin
       run_words_bound first_blue run_words start;
       h_addr_agree first_blue;
       flush_white_transfer g start first_blue run_words fp;
       flush_density_transfer g start first_blue run_words fp;
       flush_reaches_run_end g first_blue run_words fp start;
       assert (blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
                 run_words + blue_whsize g objs);
       flush_conserves_whsize g start first_blue run_words fp
     end);
    assert (total_blue_whsize g0 == total_blue_whsize g1);
    assert (walk_visits g1 zero_addr start);
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    assert (objects nxt g0 == Seq.tail objs);
    assert (objects nxt g1 == Seq.tail objs);
    walk_visits_step g1 zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    assert (Seq.tail objs == objects nxt g0);
    assert (all_objs == objects zero_addr g0);
    assert (Seq.length g0 == heap_size);
    assert (Seq.length g1 == heap_size);
    assert (post_sweep_strong g0);
    assert (post_sweep g0);
    (let subset (o: obj_addr)
       : Lemma (requires Seq.mem o (Seq.tail objs)) (ensures Seq.mem o all_objs)
       = mem_cons_lemma o x (Seq.tail objs)
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires subset));
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g1 p == read_word g0 p);
    (let word_agree (o: obj_addr)
       : Lemma
         (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
         (ensures read_word g1 (hd_address o) == read_word g0 (hd_address o))
       = assert (Seq.mem o (objects nxt g0));
         mem_from_le_hd_address nxt g0 o;
         hd_address_bounds o
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires word_agree));
    assert (walk_pre g0 g1 nxt (Seq.tail objs) all_objs 0UL 0);
    assert (Seq.length g1 == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g1);
    assert (post_sweep_strong g0);
    assert (walk_visits g1 zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g1 == Seq.tail objs);
    objects_agree_above g g1 start (U64.v start);
    objects_agree_above g g1 nxt (U64.v start);
    assert (objects start g1 == Seq.cons x (objects nxt g1));
    assert (read_word g start == read_word g0 start);
    caw_clause4_ext_white g0 g g1 start nxt x first_blue run_words fp;
    assert (white_inv g0 g1 nxt (Seq.tail objs) 0UL 0 all_objs);
    assert (whsize_inv g0 g1 nxt (Seq.tail objs) 0UL 0 all_objs);
    coalesce_aux_conserves_whsize_aux g0 g1 nxt (Seq.tail objs) 0UL 0 fp1 all_objs
#pop-options

let coalesce_conserves_whsize g =
  coalesce_aux_conserves_whsize_aux g g zero_addr (objects zero_addr g) 0UL 0 0UL
                                    (objects zero_addr g)

/// ---------------------------------------------------------------------------
/// Blue coverage: general helpers
/// ---------------------------------------------------------------------------
///
/// `blue_covered g p` is existential over `objects zero_addr g`; the two
/// facts the flush-preserves-coverage argument needs are: a header-agreeing
/// witness transfers (the `blue_covered` analogue of `header_agree_transfers`),
/// and no object's extent crosses a walk boundary (a pure structural fact,
/// independent of coalescing, needed to localize which objects can possibly
/// cover a position below/above a given cursor).

/// If `x`'s header agrees between two heaps, `x`'s contribution to
/// `blue_covered` at any position transfers: same colour, same extent.
let blue_covered_by_agree (g g': heap) (x: obj_addr) (p: nat)
  : Lemma
    (requires
      Seq.length g == heap_size /\ Seq.length g' == heap_size /\
      read_word g (hd_address x) == read_word g' (hd_address x))
    (ensures (is_blue x g /\ in_extent g x p) <==> (is_blue x g' /\ in_extent g' x p))
  = header_agree_transfers g g' x

/// No object visited along the walk from `s` to `bound` extends past
/// `bound`: if `x` is on the walk from `s` with `hd_address x < bound`, and
/// the walk from `s` reaches `bound`, `x`'s own extent ends at or before
/// `bound`.  A structural fact about how `objects`/`walk_visits` tile the
/// heap; proved by an induction mirroring `objects_split_from`'s own.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec objects_no_straddle (g: heap) (s bound: hp_addr) (x: obj_addr)
  : Lemma
    (requires
      Seq.length g == heap_size /\ walk_visits g s bound /\
      Seq.mem x (objects s g) /\ U64.v (hd_address x) < U64.v bound)
    (ensures next_pos g x <= U64.v bound)
    (decreases (heap_size - U64.v s))
  = if U64.v s = U64.v bound then begin
      objects_addresses_gt_start s g x;
      hd_address_spec x
    end
    else begin
      walk_visits_above g s bound;
      WE.walk_end_step g s;
      WE.walk_head g s;
      f_address_spec s;
      let y : obj_addr = f_address s in
      hd_address_spec y;
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      let nxt = mk_hp_addr next_nat in
      assert (walk_visits g nxt bound);
      if x = y then begin
        wosize_of_object_spec x g;
        walk_visits_above g nxt bound
      end else begin
        Seq.cons_head_tail (objects s g);
        mem_cons_lemma x y (objects nxt g);
        objects_no_straddle g nxt bound x
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Blue coverage: the walk invariant
/// ---------------------------------------------------------------------------

let blue_cov_inv
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (all_objs: seq obj_addr)
  : prop =
  white_inv g0 g start objs first_blue run_words all_objs /\
  (forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g p)) /\
  (run_words > 0 ==>
    (forall (p: nat). U64.v first_blue - U64.v mword <= p /\ p < U64.v start ==>
       blue_covered g p))

/// A flush conserves blue coverage at every position: below the run's
/// floor, the same split witness (`objects_prefix_agree`) plus header
/// agreement carries any covering object across unchanged; inside the run,
/// the merged block itself covers exactly `[h, start)`, matching the
/// invariant's own "run is covered" clause; at or above `start`, no object
/// can straddle the boundary (`objects_no_straddle`), so any covering
/// object is untouched by the flush.
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let flush_conserves_coverage
  (g: heap) (start: hp_addr) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start /\
      walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)) /\
      walk_visits g zero_addr start /\
      (forall (p: nat). U64.v first_blue - U64.v mword <= p /\ p < U64.v start ==>
         blue_covered g p))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (p: nat). p < heap_size ==> (blue_covered g p <==> blue_covered g1 p)))
  = let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let g1 = fst (flush_blue g first_blue run_words fp) in
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    objects_prefix_agree g g1 zero_addr h;
    flush_preserves_walk g (U64.v start) first_blue run_words fp;
    flush_reaches_run_end g first_blue run_words fp start;
    flush_h_decompose g first_blue run_words fp start;
    flush_blue_header_spec g fb run_words fp;
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    makeHeader_getColor wz_u64 Blue 0UL;
    wosize_of_object_spec fb g1;
    color_of_object_spec fb g1;
    is_blue_iff fb g1;
    assert (is_blue fb g1);
    assert (wosize_of_object fb g1 == wz_u64);
    assert (next_pos g1 fb == U64.v start);
    objects_split_from g zero_addr start;
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g == Seq.append pre (objects h g) /\
        objects zero_addr g1 == Seq.append pre (objects h g1) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h)
    with begin
      Seq.head_cons fb (objects start g1);
      Seq.lemma_tl fb (objects start g1);
      assert (objects h g1 == Seq.cons fb (objects start g1));
      eliminate exists (pre2: seq obj_addr).
          objects zero_addr g == Seq.append pre2 (objects start g) /\
          (forall (z: obj_addr). Seq.mem z pre2 ==> U64.v (hd_address z) < U64.v start) /\
          (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
      with begin
      objects_split_from g1 zero_addr start;
      eliminate exists (pre3: seq obj_addr).
          objects zero_addr g1 == Seq.append pre3 (objects start g1) /\
          (forall (z: obj_addr). Seq.mem z pre3 ==> U64.v (hd_address z) < U64.v start) /\
          (forall (z: obj_addr). Seq.mem z (objects start g1) ==> U64.v (hd_address z) >= U64.v start)
      with begin
        let step (p: nat)
          : Lemma
            (requires p < heap_size)
            (ensures blue_covered g p <==> blue_covered g1 p)
          = if p < U64.v h then begin
              let fwd (witness: obj_addr)
                : Lemma
                  (requires
                    Seq.mem witness (objects zero_addr g) /\ is_blue witness g /\
                    in_extent g witness p)
                  (ensures blue_covered g1 p)
                = mem_append_lemma witness pre (objects h g);
                  (if not (Seq.mem witness pre) then mem_from_le_hd_address h g witness);
                  mem_append_lemma witness pre (objects h g1);
                  blue_covered_by_agree g g1 witness p
              in
              let bwd (witness: obj_addr)
                : Lemma
                  (requires
                    Seq.mem witness (objects zero_addr g1) /\ is_blue witness g1 /\
                    in_extent g1 witness p)
                  (ensures blue_covered g p)
                = mem_append_lemma witness pre (objects h g1);
                  (if not (Seq.mem witness pre) then mem_from_le_hd_address h g1 witness);
                  mem_append_lemma witness pre (objects h g);
                  blue_covered_by_agree g g1 witness p
              in
              (if blue_covered g p then
                 eliminate exists (witness: obj_addr).
                     Seq.mem witness (objects zero_addr g) /\ is_blue witness g /\
                     in_extent g witness p
                 with begin fwd witness end);
              (if blue_covered g1 p then
                 eliminate exists (witness: obj_addr).
                     Seq.mem witness (objects zero_addr g1) /\ is_blue witness g1 /\
                     in_extent g1 witness p
                 with begin bwd witness end)
            end
            else if p < U64.v start then begin
              assert (blue_covered g p);
              mem_append_lemma fb pre (objects h g1);
              assert (Seq.mem fb (objects zero_addr g1));
              assert (in_extent g1 fb p);
              assert (blue_covered g1 p)
            end
            else begin
              let fwd (witness: obj_addr)
                : Lemma
                  (requires
                    Seq.mem witness (objects zero_addr g) /\ is_blue witness g /\
                    in_extent g witness p)
                  (ensures blue_covered g1 p)
                = (if U64.v (hd_address witness) < U64.v start then
                     objects_no_straddle g zero_addr start witness);
                  assert (U64.v (hd_address witness) >= U64.v start);
                  mem_append_lemma witness pre2 (objects start g);
                  assert (Seq.mem witness (objects start g));
                  assert (objects start g1 == objects start g);
                  assert (Seq.mem witness (objects start g1));
                  mem_append_lemma witness pre3 (objects start g1);
                  assert (Seq.mem witness (objects zero_addr g1));
                  blue_covered_by_agree g g1 witness p;
                  assert (is_blue witness g1 /\ in_extent g1 witness p);
                  assert (blue_covered g1 p)
              in
              let bwd (witness: obj_addr)
                : Lemma
                  (requires
                    Seq.mem witness (objects zero_addr g1) /\ is_blue witness g1 /\
                    in_extent g1 witness p)
                  (ensures blue_covered g p)
                = (if U64.v (hd_address witness) < U64.v start then
                     objects_no_straddle g1 zero_addr start witness);
                  assert (U64.v (hd_address witness) >= U64.v start);
                  mem_append_lemma witness pre3 (objects start g1);
                  assert (Seq.mem witness (objects start g1));
                  assert (objects start g1 == objects start g);
                  assert (Seq.mem witness (objects start g));
                  mem_append_lemma witness pre2 (objects start g);
                  assert (Seq.mem witness (objects zero_addr g));
                  blue_covered_by_agree g g1 witness p;
                  assert (is_blue witness g /\ in_extent g witness p);
                  assert (blue_covered g p)
              in
              (if blue_covered g p then
                 eliminate exists (witness: obj_addr).
                     Seq.mem witness (objects zero_addr g) /\ is_blue witness g /\
                     in_extent g witness p
                 with begin fwd witness end);
              (if blue_covered g1 p then
                 eliminate exists (witness: obj_addr).
                     Seq.mem witness (objects zero_addr g1) /\ is_blue witness g1 /\
                     in_extent g1 witness p
                 with begin bwd witness end)
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires step)
      end
      end
    end
#pop-options

/// The top-of-heap analogue of `flush_conserves_coverage`: the run ends
/// exactly at `heap_size`, so there is no "at or above `start`" case at all
/// -- every position below `heap_size` is either below the run's floor or
/// inside the run itself.
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let flush_conserves_coverage_at_end
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == heap_size /\
      walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)) /\
      (forall (p: nat). U64.v first_blue - U64.v mword <= p /\ p < heap_size ==>
         blue_covered g p))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (p: nat). p < heap_size ==> (blue_covered g p <==> blue_covered g1 p)))
  = let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let g1 = fst (flush_blue g first_blue run_words fp) in
    assert (U64.v h + U64.v mword == U64.v first_blue);
    // `objects h g` is nonempty: `h` itself is covered (by hypothesis, since
    // `h < heap_size`), and no object visited from `zero_addr` can straddle
    // the walk position `h` (`objects_no_straddle`), so the covering object
    // sits exactly at `h`, giving `objects h g` its head.
    assert (blue_covered g (U64.v h));
    objects_split_from g zero_addr h;
    eliminate exists (pre0: seq obj_addr).
        objects zero_addr g == Seq.append pre0 (objects h g) /\
        (forall (z: obj_addr). Seq.mem z pre0 ==> U64.v (hd_address z) < U64.v h) /\
        (forall (z: obj_addr). Seq.mem z (objects h g) ==> U64.v (hd_address z) >= U64.v h)
    with begin
      let land (x: obj_addr)
        : Lemma
          (requires
            Seq.mem x (objects zero_addr g) /\ is_blue x g /\ in_extent g x (U64.v h))
          (ensures Seq.mem x (objects h g))
        = (if U64.v (hd_address x) < U64.v h then objects_no_straddle g zero_addr h x);
          assert (U64.v (hd_address x) >= U64.v h);
          mem_append_lemma x pre0 (objects h g)
      in
      eliminate exists (x: obj_addr).
          Seq.mem x (objects zero_addr g) /\ is_blue x g /\ in_extent g x (U64.v h)
      with begin
        land x;
        assert (Seq.length (objects h g) > 0)
      end
    end;
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    objects_prefix_agree g g1 zero_addr h;
    flush_blue_header_spec g fb run_words fp;
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    makeHeader_getColor wz_u64 Blue 0UL;
    wosize_of_object_spec fb g1;
    color_of_object_spec fb g1;
    is_blue_iff fb g1;
    assert (is_blue fb g1);
    assert (wosize_of_object fb g1 == wz_u64);
    assert (next_pos g1 fb == heap_size);
    f_hd_roundtrip fb;
    assert (Seq.length (objects h g1) > 0);
    WE.walk_end_step g1 h;
    Seq.lemma_eq_elim (objects h g1) (Seq.cons fb Seq.empty);
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g == Seq.append pre (objects h g) /\
        objects zero_addr g1 == Seq.append pre (objects h g1) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h)
    with begin
      let step (p: nat)
        : Lemma
          (requires p < heap_size)
          (ensures blue_covered g p <==> blue_covered g1 p)
        = if p < U64.v h then begin
            let fwd (witness: obj_addr)
              : Lemma
                (requires
                  Seq.mem witness (objects zero_addr g) /\ is_blue witness g /\
                  in_extent g witness p)
                (ensures blue_covered g1 p)
              = mem_append_lemma witness pre (objects h g);
                (if not (Seq.mem witness pre) then mem_from_le_hd_address h g witness);
                mem_append_lemma witness pre (objects h g1);
                blue_covered_by_agree g g1 witness p
            in
            let bwd (witness: obj_addr)
              : Lemma
                (requires
                  Seq.mem witness (objects zero_addr g1) /\ is_blue witness g1 /\
                  in_extent g1 witness p)
                (ensures blue_covered g p)
              = mem_append_lemma witness pre (objects h g1);
                (if not (Seq.mem witness pre) then mem_from_le_hd_address h g1 witness);
                mem_append_lemma witness pre (objects h g);
                blue_covered_by_agree g g1 witness p
            in
            (if blue_covered g p then
               eliminate exists (witness: obj_addr).
                   Seq.mem witness (objects zero_addr g) /\ is_blue witness g /\
                   in_extent g witness p
               with begin fwd witness end);
            (if blue_covered g1 p then
               eliminate exists (witness: obj_addr).
                   Seq.mem witness (objects zero_addr g1) /\ is_blue witness g1 /\
                   in_extent g1 witness p
               with begin bwd witness end)
          end
          else begin
            assert (blue_covered g p);
            mem_append_lemma fb pre (objects h g1);
            assert (Seq.mem fb (objects zero_addr g1));
            assert (in_extent g1 fb p);
            assert (blue_covered g1 p)
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires step)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Blue coverage: the induction
/// ---------------------------------------------------------------------------

/// Empty case: flush whatever run is pending, using `flush_conserves_coverage`
/// (vacuous if `run_words = 0`).
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let caw_bc_empty
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      blue_cov_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs = 0)
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g1 p)))
  = if run_words = 0 then ()
    else begin
      run_words_bound first_blue run_words start;
      assert (objects start g == objs);
      assert (forall (p: nat). U64.v first_blue - U64.v mword <= p /\ p < U64.v start ==>
                blue_covered g p);
      flush_conserves_coverage g start first_blue run_words fp
    end
#pop-options

/// Top-of-heap case: `x` is the last object.  Blue: extend the run and
/// flush it against the top of the heap, `x`'s own extent covering exactly
/// `[floor, heap_size)`.  White: the pending run (if any) ends exactly at
/// `start`, an ordinary flush.
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
private let caw_bc_top
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      blue_cov_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g' p)))
  = let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    let wz = U64.v (wosize_of_object x g0) in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    Seq.lemma_eq_elim (objects start g0) (Seq.cons x Seq.empty);
    Seq.lemma_eq_elim (Seq.tail objs) Seq.empty;
    assert (objects start g == objs);
    if is_blue x g0 then begin
      let fb' = if run_words = 0 then x else first_blue in
      let rw' = run_words + wz + 1 in
      coalesce_aux_blue_step g0 g objs first_blue run_words fp;
      coalesce_aux_empty g0 g fb' rw' fp;
      hd_address_spec fb';
      h_addr_agree fb';
      assert (U64.v fb' - U64.v mword + rw' * U64.v mword == heap_size);
      header_agree_transfers g0 g x;
      assert (is_blue x g);
      wosize_of_object_spec x g;
      assert (next_pos g x == heap_size);
      objects_split_from g zero_addr start;
      eliminate exists (pre: seq obj_addr).
          objects zero_addr g == Seq.append pre (objects start g) /\
          (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v start) /\
          (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
      with begin
        mem_append_lemma x pre (objects start g);
        assert (Seq.mem x (objects zero_addr g));
        let cov_run (p: nat)
          : Lemma
            (requires U64.v fb' - U64.v mword <= p /\ p < heap_size)
            (ensures blue_covered g p)
          = if run_words = 0 then begin
              assert (in_extent g x p)
            end
            else if p < U64.v start then ()
            else assert (in_extent g x p)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires cov_run);
        run_words_bound_top fb' rw';
        flush_conserves_coverage_at_end g fb' rw' fp;
        let g1 = fst (flush_blue g fb' rw' fp) in
        assert (forall (p: nat). p < heap_size ==> (blue_covered g p <==> blue_covered g1 p));
        assert (forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g1 p))
      end
    end else begin
      coalesce_aux_white_step g0 g objs first_blue run_words fp;
      let (g1, fp1) = flush_blue g first_blue run_words fp in
      coalesce_aux_empty g0 g1 0UL 0 fp1;
      if run_words = 0 then ()
      else begin
        run_words_bound first_blue run_words start;
        assert (forall (p: nat). U64.v first_blue - U64.v mword <= p /\ p < U64.v start ==>
                  blue_covered g p);
        flush_conserves_coverage g start first_blue run_words fp
      end
    end
#pop-options

/// The real induction.  Four-way dispatcher, mirroring
/// `coalesce_aux_conserves_whsize_aux`'s own structure and reusing the same
/// leaf lemmas (`caw_extend_run_white_free`, `caw_clause4_ext_blue`,
/// `caw_clause4_ext_white`) for the `white_inv` bookkeeping.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec coalesce_aux_preserves_blue_coverage_aux
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires blue_cov_inv g0 g start objs first_blue run_words all_objs)
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g' p)))
    (decreases %[Seq.length objs; 1])
  = if Seq.length objs = 0 then
      caw_bc_empty g0 g start objs first_blue run_words fp all_objs
    else begin
      let x = Seq.head objs in
      if U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size then
        caw_bc_top g0 g start objs first_blue run_words fp all_objs
      else if is_blue x g0 then
        caw_bc_blue_head g0 g start objs first_blue run_words fp all_objs
      else
        caw_bc_white_head g0 g start objs first_blue run_words fp all_objs
    end

and caw_bc_blue_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      blue_cov_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ is_blue (Seq.head objs) g0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g' p)))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    let fb' = if run_words = 0 then x else first_blue in
    let rw' = run_words + wz + 1 in
    coalesce_aux_blue_step g0 g objs first_blue run_words fp;
    assert (read_word g start == read_word g0 start);
    header_agree_transfers g0 g x;
    walk_visits_step g zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    hd_address_spec fb';
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    let only_x (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g) /\
          U64.v (hd_address y) >= U64.v start /\ U64.v (hd_address y) < U64.v nxt)
        (ensures y == x)
      = objects_agree_above g0 g start (U64.v start);
        objects_split_from g zero_addr start;
        eliminate exists (pre: seq obj_addr).
            objects zero_addr g == Seq.append pre (objects start g) /\
            (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v start) /\
            (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
        with begin
          mem_append_lemma y pre (objects start g);
          mem_cons_lemma y x (objects nxt g);
          if y = x then ()
          else begin
            objects_addresses_gt_start nxt g y;
            hd_address_spec y
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires only_x);
    caw_extend_run_white_free g0 g start x (U64.v nxt) first_blue fb' run_words;
    (if run_words = 0 then h_addr_agree fb');
    assert (walk_pre g0 g nxt (Seq.tail objs) all_objs fb' rw');
    assert (Seq.length g == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g);
    assert (post_sweep_strong g0);
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g p == read_word g0 p);
    assert (walk_visits g zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g == Seq.tail objs);
    caw_clause4_ext_blue g0 g start nxt x;
    assert (rw' > 0 ==>
              (forall (y: obj_addr).
                 Seq.mem y (objects zero_addr g) /\ is_white y g /\
                 U64.v (hd_address y) >= U64.v fb' - U64.v mword /\
                 U64.v (hd_address y) < U64.v nxt ==> False));
    assert (rw' > 0 ==> walk_visits g zero_addr (mk_hp_addr (U64.v fb' - U64.v mword)));
    assert (white_inv g0 g nxt (Seq.tail objs) fb' rw' all_objs);
    // blue_cov_inv's own two extra clauses at the new state: coverage is a
    // global equivalence unaffected by the blue step (`g` doesn't change),
    // and the extended run's own coverage, mirroring `caw_ws_head_whsize`'s
    // role for whsize but for the "is covered" predicate instead of a sum.
    assert (forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g p));
    let cov_run (p: nat)
      : Lemma
        (requires U64.v fb' - U64.v mword <= p /\ p < U64.v nxt)
        (ensures blue_covered g p)
      = if p < U64.v start then ()
        else assert (in_extent g x p)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires cov_run);
    assert (blue_cov_inv g0 g nxt (Seq.tail objs) fb' rw' all_objs);
    coalesce_aux_preserves_blue_coverage_aux g0 g nxt (Seq.tail objs) fb' rw' fp all_objs

and caw_bc_white_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      blue_cov_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ ~(is_blue (Seq.head objs) g0) /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g' p)))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    coalesce_aux_white_step g0 g objs first_blue run_words fp;
    let (g1, fp1) = flush_blue g first_blue run_words fp in
    flush_preserves_walk g (U64.v start) first_blue run_words fp;
    objects_split_from g zero_addr start;
    eliminate exists (pre0: seq obj_addr).
        objects zero_addr g == Seq.append pre0 (objects start g) /\
        (forall (z: obj_addr). Seq.mem z pre0 ==> U64.v (hd_address z) < U64.v start) /\
        (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
    with begin
      Seq.lemma_len_append pre0 (objects start g)
    end;
    assert (Seq.length (objects zero_addr g) > 0);
    (if run_words > 0 then begin
       run_words_bound first_blue run_words start;
       h_addr_agree first_blue;
       flush_white_transfer g start first_blue run_words fp;
       flush_density_transfer g start first_blue run_words fp;
       flush_reaches_run_end g first_blue run_words fp start;
       assert (forall (p: nat). U64.v first_blue - U64.v mword <= p /\ p < U64.v start ==>
                 blue_covered g p);
       flush_conserves_coverage g start first_blue run_words fp
     end);
    assert (forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g1 p));
    assert (walk_visits g1 zero_addr start);
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    assert (objects nxt g0 == Seq.tail objs);
    assert (objects nxt g1 == Seq.tail objs);
    walk_visits_step g1 zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    assert (Seq.tail objs == objects nxt g0);
    assert (all_objs == objects zero_addr g0);
    assert (Seq.length g0 == heap_size);
    assert (Seq.length g1 == heap_size);
    assert (post_sweep_strong g0);
    assert (post_sweep g0);
    (let subset (o: obj_addr)
       : Lemma (requires Seq.mem o (Seq.tail objs)) (ensures Seq.mem o all_objs)
       = mem_cons_lemma o x (Seq.tail objs)
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires subset));
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g1 p == read_word g0 p);
    (let word_agree (o: obj_addr)
       : Lemma
         (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
         (ensures read_word g1 (hd_address o) == read_word g0 (hd_address o))
       = assert (Seq.mem o (objects nxt g0));
         mem_from_le_hd_address nxt g0 o;
         hd_address_bounds o
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires word_agree));
    assert (walk_pre g0 g1 nxt (Seq.tail objs) all_objs 0UL 0);
    assert (Seq.length g1 == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g1);
    assert (post_sweep_strong g0);
    assert (walk_visits g1 zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g1 == Seq.tail objs);
    objects_agree_above g g1 start (U64.v start);
    objects_agree_above g g1 nxt (U64.v start);
    assert (objects start g1 == Seq.cons x (objects nxt g1));
    assert (read_word g start == read_word g0 start);
    caw_clause4_ext_white g0 g g1 start nxt x first_blue run_words fp;
    assert (white_inv g0 g1 nxt (Seq.tail objs) 0UL 0 all_objs);
    assert (blue_cov_inv g0 g1 nxt (Seq.tail objs) 0UL 0 all_objs);
    coalesce_aux_preserves_blue_coverage_aux g0 g1 nxt (Seq.tail objs) 0UL 0 fp1 all_objs
#pop-options

let coalesce_preserves_blue_coverage g =
  coalesce_aux_preserves_blue_coverage_aux g g zero_addr (objects zero_addr g) 0UL 0 0UL
                                           (objects zero_addr g)

/// ---------------------------------------------------------------------------
/// No adjacent blue: general helpers
/// ---------------------------------------------------------------------------
///
/// The invariant tracks two facts about the *already-finalized* region
/// (below the pending run's own floor, or below `start` when no run is
/// pending): no two blue objects there are adjacent, and no blue object
/// there ends exactly at the floor (needed so that, when a fresh run
/// starts, the object immediately preceding it is known not to be blue --
/// otherwise the fresh run and that object would themselves already be an
/// unmerged adjacent pair).

/// If `x` and `y`'s headers both agree between two heaps, the whole
/// "adjacent and both blue" triple transfers -- the `adjacent` analogue of
/// `header_agree_transfers`/`blue_covered_by_agree`.
let adjacent_by_agree (g g': heap) (x y: obj_addr)
  : Lemma
    (requires
      Seq.length g == heap_size /\ Seq.length g' == heap_size /\
      read_word g (hd_address x) == read_word g' (hd_address x) /\
      read_word g (hd_address y) == read_word g' (hd_address y))
    (ensures
      (is_blue x g /\ is_blue y g /\ adjacent g x y) <==>
      (is_blue x g' /\ is_blue y g' /\ adjacent g' x y))
  = header_agree_transfers g g' x;
    header_agree_transfers g g' y

/// A flush conserves "no adjacent blue pair below `start`": below the run's
/// floor `h`, the same split witness plus header agreement carries any
/// pair across unchanged; the merged block itself (occupying `[h, start)`)
/// cannot be the `y` of a violating pair, since whatever would end exactly
/// at `h` (its only possible `x` partner) is ruled out by the "no blue ends
/// at the floor" hypothesis.
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let flush_conserves_adj_free
  (g: heap) (start: hp_addr) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start /\
      walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)) /\
      (forall (x y: obj_addr).
         Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
         is_blue x g /\ is_blue y g /\ adjacent g x y /\
         U64.v (hd_address y) < U64.v first_blue - U64.v mword ==> False) /\
      (forall (z: obj_addr).
         Seq.mem z (objects zero_addr g) /\ is_blue z g /\
         next_pos g z == U64.v first_blue - U64.v mword ==> False))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
          is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y /\
          U64.v (hd_address y) < U64.v start ==> False))
  = let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let g1 = fst (flush_blue g first_blue run_words fp) in
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    objects_prefix_agree g g1 zero_addr h;
    flush_h_decompose g first_blue run_words fp start;
    flush_blue_header_spec g fb run_words fp;
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    makeHeader_getColor wz_u64 Blue 0UL;
    wosize_of_object_spec fb g1;
    color_of_object_spec fb g1;
    is_blue_iff fb g1;
    assert (is_blue fb g1);
    assert (wosize_of_object fb g1 == wz_u64);
    assert (next_pos g1 fb == U64.v start);
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g == Seq.append pre (objects h g) /\
        objects zero_addr g1 == Seq.append pre (objects h g1) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h)
    with begin
      Seq.head_cons fb (objects start g1);
      Seq.lemma_tl fb (objects start g1);
      assert (objects h g1 == Seq.cons fb (objects start g1));
      // `pre`'s own header words agree between `g` and `g1`.
      let pre_agree (z: obj_addr)
        : Lemma
          (requires Seq.mem z pre)
          (ensures read_word g (hd_address z) == read_word g1 (hd_address z))
        = hd_address_spec z;
          FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v h) (U64.v (hd_address z)) (U64.v mword);
          assert (U64.v h - U64.v (hd_address z) >= U64.v mword);
          flush_blue_preserves_outside g first_blue run_words fp (hd_address z)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires pre_agree);
      let step (x y: obj_addr)
        : Lemma
          (requires
            Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
            is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y /\
            U64.v (hd_address y) < U64.v start)
          (ensures False)
        = mem_append_lemma y pre (objects h g1);
          if Seq.mem y pre then begin
            // y < h: x, adjacent to y, has next_pos == hd_address y < h too,
            // so x is also below h, and both transfer to g via `pre_agree`.
            mem_from_le_hd_address zero_addr g1 x;
            (if not (Seq.mem x pre) then begin
               mem_append_lemma x pre (objects h g1);
               mem_from_le_hd_address h g1 x;
               // hd_address x >= h, but adjacent x y gives next_pos g1 x ==
               // hd_address y < h, and next_pos g1 x > hd_address x -- so
               // hd_address x < h, contradiction.
               ()
             end);
            pre_agree x; pre_agree y;
            adjacent_by_agree g g1 x y;
            mem_append_lemma x pre (objects h g);
            mem_append_lemma y pre (objects h g)
          end else begin
            // y not in pre, and y < start, so (via the split) y is in
            // `objects h g1 == cons fb (objects start g1)` with hd_address y
            // < start; the only such element is fb itself.
            assert (Seq.mem y (objects h g1));
            Seq.cons_head_tail (objects h g1);
            mem_cons_lemma y fb (objects start g1);
            (if not (y = fb) then begin
               mem_from_le_hd_address start g1 y
               // hd_address y >= start, contradicting hd_address y < start.
             end);
            assert (y == fb);
            // adjacent x fb: next_pos g1 x == h.  x < h (same argument as
            // above), so x transfers to g via `pre_agree`.
            (if not (Seq.mem x pre) then begin
               mem_append_lemma x pre (objects h g1);
               mem_from_le_hd_address h g1 x
             end);
            pre_agree x;
            header_agree_transfers g g1 x;
            mem_append_lemma x pre (objects h g)
          end
      in
      FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (step x))
    end
#pop-options

/// The top-of-heap analogue of `flush_conserves_adj_free`: the run ends
/// exactly at `heap_size`, so the merged block is the very last object --
/// the ensures is the full, unconditional "no adjacent blue pair anywhere."
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let flush_conserves_adj_free_at_end
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == heap_size /\
      walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)) /\
      (forall (x y: obj_addr).
         Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
         is_blue x g /\ is_blue y g /\ adjacent g x y /\
         U64.v (hd_address y) < U64.v first_blue - U64.v mword ==> False) /\
      (forall (z: obj_addr).
         Seq.mem z (objects zero_addr g) /\ is_blue z g /\
         next_pos g z == U64.v first_blue - U64.v mword ==> False))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
          is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y ==> False))
  = let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let g1 = fst (flush_blue g first_blue run_words fp) in
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    objects_prefix_agree g g1 zero_addr h;
    flush_blue_header_spec g fb run_words fp;
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    makeHeader_getColor wz_u64 Blue 0UL;
    wosize_of_object_spec fb g1;
    color_of_object_spec fb g1;
    is_blue_iff fb g1;
    assert (is_blue fb g1);
    assert (wosize_of_object fb g1 == wz_u64);
    assert (next_pos g1 fb == heap_size);
    f_hd_roundtrip fb;
    assert (U64.v h + U64.v mword == U64.v first_blue);
    assert (Seq.length (objects h g1) > 0);
    WE.walk_end_step g1 h;
    Seq.lemma_eq_elim (objects h g1) (Seq.cons fb Seq.empty);
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g == Seq.append pre (objects h g) /\
        objects zero_addr g1 == Seq.append pre (objects h g1) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h)
    with begin
      let pre_agree (z: obj_addr)
        : Lemma
          (requires Seq.mem z pre)
          (ensures read_word g (hd_address z) == read_word g1 (hd_address z))
        = hd_address_spec z;
          FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v h) (U64.v (hd_address z)) (U64.v mword);
          assert (U64.v h - U64.v (hd_address z) >= U64.v mword);
          flush_blue_preserves_outside g first_blue run_words fp (hd_address z)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires pre_agree);
      let step (x y: obj_addr)
        : Lemma
          (requires
            Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
            is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y)
          (ensures False)
        = mem_append_lemma y pre (objects h g1);
          if Seq.mem y pre then begin
            (if not (Seq.mem x pre) then begin
               mem_append_lemma x pre (objects h g1);
               mem_from_le_hd_address h g1 x
             end);
            pre_agree x; pre_agree y;
            adjacent_by_agree g g1 x y;
            mem_append_lemma x pre (objects h g);
            mem_append_lemma y pre (objects h g)
          end else begin
            assert (Seq.mem y (objects h g1));
            Seq.cons_head_tail (objects h g1);
            mem_cons_lemma y fb Seq.empty;
            assert (y == fb);
            (if not (Seq.mem x pre) then begin
               mem_append_lemma x pre (objects h g1);
               mem_from_le_hd_address h g1 x
             end);
            pre_agree x;
            header_agree_transfers g g1 x;
            mem_append_lemma x pre (objects h g)
          end
      in
      FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (step x))
    end
#pop-options

/// ---------------------------------------------------------------------------
/// No adjacent blue: the walk invariant
/// ---------------------------------------------------------------------------
///
/// Built on `white_inv`, tracking (below the pending run's own floor, or
/// below `start` when no run is pending): no two blue objects are adjacent,
/// and no blue object ends exactly at the floor -- the latter is what makes
/// it safe, when a run later starts fresh right there, to know the object
/// immediately preceding it isn't blue (else that object and the fresh run
/// would already be an unmerged adjacent pair).
let adj_free_inv
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (all_objs: seq obj_addr)
  : prop =
  white_inv g0 g start objs first_blue run_words all_objs /\
  (run_words = 0 ==>
    (forall (x y: obj_addr).
       Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
       is_blue x g /\ is_blue y g /\ adjacent g x y /\
       U64.v (hd_address y) < U64.v start ==> False) /\
    (forall (z: obj_addr).
       Seq.mem z (objects zero_addr g) /\ is_blue z g /\
       next_pos g z == U64.v start ==> False)) /\
  (run_words > 0 ==>
    (forall (x y: obj_addr).
       Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
       is_blue x g /\ is_blue y g /\ adjacent g x y /\
       U64.v (hd_address y) < U64.v first_blue - U64.v mword ==> False) /\
    (forall (z: obj_addr).
       Seq.mem z (objects zero_addr g) /\ is_blue z g /\
       next_pos g z == U64.v first_blue - U64.v mword ==> False))

/// Empty case: flush whatever run is pending, using `flush_conserves_adj_free`
/// (vacuous if `run_words = 0`), then note that with `objs` empty, every
/// object of `g1` genuinely sits below `start` -- so "below `start`"
/// becomes the full, unconditional fact.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
private let caw_adj_empty
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      adj_free_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs = 0)
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
          is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y ==> False))
  = Seq.lemma_eq_elim objs Seq.empty;
    let g1 = fst (flush_blue g first_blue run_words fp) in
    (if run_words = 0 then ()
     else begin
       run_words_bound first_blue run_words start;
       h_addr_agree first_blue;
       flush_conserves_adj_free g start first_blue run_words fp
     end);
    assert (forall (x y: obj_addr).
              Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
              is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y /\
              U64.v (hd_address y) < U64.v start ==> False);
    (if run_words > 0 then flush_preserves_walk g (U64.v start) first_blue run_words fp);
    assert (objects start g1 == Seq.empty);
    (if run_words > 0 then flush_reaches_run_end g first_blue run_words fp start);
    assert (walk_visits g1 zero_addr start);
    objects_split_from g1 zero_addr start;
    eliminate exists (pre1: seq obj_addr).
        objects zero_addr g1 == Seq.append pre1 (objects start g1) /\
        (forall (z: obj_addr). Seq.mem z pre1 ==> U64.v (hd_address z) < U64.v start) /\
        (forall (z: obj_addr). Seq.mem z (objects start g1) ==> U64.v (hd_address z) >= U64.v start)
    with begin
      Seq.lemma_eq_elim (objects zero_addr g1) pre1;
      let final (x y: obj_addr)
        : Lemma
          (requires
            Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
            is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y)
          (ensures False)
        = assert (Seq.mem y pre1)
      in
      FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (final x))
    end
#pop-options

/// Top-of-heap case: `x` is the last object.  Blue: extend the run and
/// flush against the top of the heap -- `flush_conserves_adj_free_at_end`
/// gives the full unconditional fact directly.  White: the pending run (if
/// any) ends exactly at `start`; `x` itself is white, so any pair
/// involving it is automatically not a blue-blue violation.
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
private let caw_adj_top
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      adj_free_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g') /\ Seq.mem y (objects zero_addr g') /\
          is_blue x g' /\ is_blue y g' /\ adjacent g' x y ==> False))
  = let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    let wz = U64.v (wosize_of_object x g0) in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    Seq.lemma_eq_elim (objects start g0) (Seq.cons x Seq.empty);
    Seq.lemma_eq_elim (Seq.tail objs) Seq.empty;
    assert (objects start g == objs);
    if is_blue x g0 then begin
      let fb' = if run_words = 0 then x else first_blue in
      let rw' = run_words + wz + 1 in
      coalesce_aux_blue_step g0 g objs first_blue run_words fp;
      coalesce_aux_empty g0 g fb' rw' fp;
      hd_address_spec fb';
      h_addr_agree fb';
      assert (U64.v fb' - U64.v mword + rw' * U64.v mword == heap_size);
      run_words_bound_top fb' rw';
      assert (walk_visits g zero_addr (mk_hp_addr (U64.v fb' - U64.v mword)));
      flush_conserves_adj_free_at_end g fb' rw' fp
    end else begin
      coalesce_aux_white_step g0 g objs first_blue run_words fp;
      let (g1, fp1) = flush_blue g first_blue run_words fp in
      coalesce_aux_empty g0 g1 0UL 0 fp1;
      (if run_words > 0 then begin
         run_words_bound first_blue run_words start;
         h_addr_agree first_blue;
         flush_preserves_walk g (U64.v start) first_blue run_words fp
       end);
      assert (objects start g1 == Seq.cons x Seq.empty);
      is_white_iff x g0;
      is_blue_iff x g0;
      header_agree_transfers g0 g1 x;
      assert (~(is_blue x g1));
      (if run_words > 0 then flush_reaches_run_end g first_blue run_words fp start);
      assert (walk_visits g1 zero_addr start);
      objects_split_from g1 zero_addr start;
      eliminate exists (pre1: seq obj_addr).
          objects zero_addr g1 == Seq.append pre1 (objects start g1) /\
          (forall (z: obj_addr). Seq.mem z pre1 ==> U64.v (hd_address z) < U64.v start) /\
          (forall (z: obj_addr). Seq.mem z (objects start g1) ==> U64.v (hd_address z) >= U64.v start)
      with begin
        let final (x' y': obj_addr)
          : Lemma
            (requires
              Seq.mem x' (objects zero_addr g1) /\ Seq.mem y' (objects zero_addr g1) /\
              is_blue x' g1 /\ is_blue y' g1 /\ adjacent g1 x' y')
            (ensures False)
          = mem_append_lemma y' pre1 (objects start g1);
            if Seq.mem y' pre1 then begin
              if run_words = 0 then ()
              else begin
                run_words_bound first_blue run_words start;
                h_addr_agree first_blue;
                flush_conserves_adj_free g start first_blue run_words fp;
                eliminate forall (x: obj_addr) (y: obj_addr).
                    Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
                    is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y /\
                    U64.v (hd_address y) < U64.v start ==> False
                with x' y'
              end
            end else begin
              mem_cons_lemma y' x Seq.empty;
              assert (y' == x)
            end
        in
        FStar.Classical.forall_intro_2 (fun x' -> FStar.Classical.move_requires (final x'))
      end
    end
#pop-options

/// The real induction.  Four-way dispatcher, mirroring
/// `coalesce_aux_conserves_whsize_aux`'s own structure and reusing the same
/// leaf lemmas (`caw_extend_run_white_free`, `caw_clause4_ext_blue`,
/// `caw_clause4_ext_white`) for the `white_inv` bookkeeping.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec coalesce_aux_no_adjacent_blue_aux
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires adj_free_inv g0 g start objs first_blue run_words all_objs)
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g') /\ Seq.mem y (objects zero_addr g') /\
          is_blue x g' /\ is_blue y g' /\ adjacent g' x y ==> False))
    (decreases %[Seq.length objs; 1])
  = if Seq.length objs = 0 then
      caw_adj_empty g0 g start objs first_blue run_words fp all_objs
    else begin
      let x = Seq.head objs in
      if U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size then
        caw_adj_top g0 g start objs first_blue run_words fp all_objs
      else if is_blue x g0 then
        caw_adj_blue_head g0 g start objs first_blue run_words fp all_objs
      else
        caw_adj_white_head g0 g start objs first_blue run_words fp all_objs
    end

/// Ordinary step, `x` blue: extend the run and recurse.  The finalized
/// floor is invariant across a blue step (whether starting fresh, where the
/// new floor `hd_address fb'` equals the old `start`, or continuing, where
/// `first_blue` -- and hence the floor -- doesn't change at all, since `g`
/// itself is untouched) -- so `adj_free_inv`'s own two extra clauses just
/// carry over from the old state's matching branch, unlike `white_inv`'s
/// clauses which need re-establishing at the new cursor `nxt`.
and caw_adj_blue_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      adj_free_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ is_blue (Seq.head objs) g0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g') /\ Seq.mem y (objects zero_addr g') /\
          is_blue x g' /\ is_blue y g' /\ adjacent g' x y ==> False))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    let fb' = if run_words = 0 then x else first_blue in
    let rw' = run_words + wz + 1 in
    coalesce_aux_blue_step g0 g objs first_blue run_words fp;
    assert (read_word g start == read_word g0 start);
    header_agree_transfers g0 g x;
    walk_visits_step g zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    hd_address_spec fb';
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    let only_x (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g) /\
          U64.v (hd_address y) >= U64.v start /\ U64.v (hd_address y) < U64.v nxt)
        (ensures y == x)
      = objects_agree_above g0 g start (U64.v start);
        objects_split_from g zero_addr start;
        eliminate exists (pre: seq obj_addr).
            objects zero_addr g == Seq.append pre (objects start g) /\
            (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v start) /\
            (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
        with begin
          mem_append_lemma y pre (objects start g);
          mem_cons_lemma y x (objects nxt g);
          if y = x then ()
          else begin
            objects_addresses_gt_start nxt g y;
            hd_address_spec y
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires only_x);
    caw_extend_run_white_free g0 g start x (U64.v nxt) first_blue fb' run_words;
    (if run_words = 0 then h_addr_agree fb' else ());
    assert (walk_pre g0 g nxt (Seq.tail objs) all_objs fb' rw');
    assert (Seq.length g == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g);
    assert (post_sweep_strong g0);
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g p == read_word g0 p);
    assert (walk_visits g zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g == Seq.tail objs);
    caw_clause4_ext_blue g0 g start nxt x;
    assert (rw' > 0 ==>
              (forall (y: obj_addr).
                 Seq.mem y (objects zero_addr g) /\ is_white y g /\
                 U64.v (hd_address y) >= U64.v fb' - U64.v mword /\
                 U64.v (hd_address y) < U64.v nxt ==> False));
    assert (rw' > 0 ==> walk_visits g zero_addr (mk_hp_addr (U64.v fb' - U64.v mword)));
    assert (white_inv g0 g nxt (Seq.tail objs) fb' rw' all_objs);
    // The floor is invariant: `hd_address fb' == (if run_words = 0 then
    // start else first_blue - mword)` -- the *same* floor the old state's
    // matching branch already has facts about, since `g` doesn't change.
    (if run_words = 0 then begin
       assert (U64.v (hd_address fb') == U64.v start);
       assert (forall (x' y': obj_addr).
                 Seq.mem x' (objects zero_addr g) /\ Seq.mem y' (objects zero_addr g) /\
                 is_blue x' g /\ is_blue y' g /\ adjacent g x' y' /\
                 U64.v (hd_address y') < U64.v (hd_address fb') ==> False);
       assert (forall (z: obj_addr).
                 Seq.mem z (objects zero_addr g) /\ is_blue z g /\
                 next_pos g z == U64.v (hd_address fb') ==> False)
     end else begin
       assert (U64.v (hd_address fb') == U64.v first_blue - U64.v mword);
       assert (forall (x' y': obj_addr).
                 Seq.mem x' (objects zero_addr g) /\ Seq.mem y' (objects zero_addr g) /\
                 is_blue x' g /\ is_blue y' g /\ adjacent g x' y' /\
                 U64.v (hd_address y') < U64.v (hd_address fb') ==> False);
       assert (forall (z: obj_addr).
                 Seq.mem z (objects zero_addr g) /\ is_blue z g /\
                 next_pos g z == U64.v (hd_address fb') ==> False)
     end);
    assert (adj_free_inv g0 g nxt (Seq.tail objs) fb' rw' all_objs);
    coalesce_aux_no_adjacent_blue_aux g0 g nxt (Seq.tail objs) fb' rw' fp all_objs

/// Ordinary step, `x` white: flush whatever run was pending, then recurse
/// from `nxt` with a fresh, empty run.  The new floor is `nxt`; below
/// `start` it transfers via `flush_conserves_adj_free` (the merged block,
/// if any, is handled inside that lemma via the "no blue ends at the old
/// floor" hypothesis), and `[start, nxt)` is just `x` itself, white, so
/// contributes no violation; "no blue ends at `nxt`" holds because `x` is
/// the *unique* object whose extent reaches `nxt` (`objects_no_straddle`
/// rules out anything below `start` reaching that far, and anything at or
/// above `nxt` can't have `next_pos == nxt` either), and `x` isn't blue.
and caw_adj_white_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      adj_free_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ ~(is_blue (Seq.head objs) g0) /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g') /\ Seq.mem y (objects zero_addr g') /\
          is_blue x g' /\ is_blue y g' /\ adjacent g' x y ==> False))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    coalesce_aux_white_step g0 g objs first_blue run_words fp;
    let (g1, fp1) = flush_blue g first_blue run_words fp in
    objects_split_from g zero_addr start;
    eliminate exists (pre0: seq obj_addr).
        objects zero_addr g == Seq.append pre0 (objects start g) /\
        (forall (z: obj_addr). Seq.mem z pre0 ==> U64.v (hd_address z) < U64.v start) /\
        (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
    with begin
      Seq.lemma_len_append pre0 (objects start g)
    end;
    assert (Seq.length (objects zero_addr g) > 0);
    (if run_words > 0 then begin
       run_words_bound first_blue run_words start;
       h_addr_agree first_blue;
       flush_preserves_walk g (U64.v start) first_blue run_words fp;
       flush_density_transfer g start first_blue run_words fp
     end);
    assert (read_word g1 start == read_word g start);
    assert (read_word g start == read_word g0 start);
    is_white_iff x g0;
    is_blue_iff x g0;
    header_agree_transfers g0 g1 x;
    assert (~(is_blue x g1));
    (if run_words > 0 then flush_reaches_run_end g first_blue run_words fp start);
    assert (walk_visits g1 zero_addr start);
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    assert (objects nxt g0 == Seq.tail objs);
    walk_visits_step g1 zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    assert (all_objs == objects zero_addr g0);
    assert (Seq.length g0 == heap_size);
    assert (Seq.length g1 == heap_size);
    assert (post_sweep_strong g0);
    assert (post_sweep g0);
    (let subset (o: obj_addr)
       : Lemma (requires Seq.mem o (Seq.tail objs)) (ensures Seq.mem o all_objs)
       = mem_cons_lemma o x (Seq.tail objs)
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires subset));
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g1 p == read_word g0 p);
    (let word_agree (o: obj_addr)
       : Lemma
         (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
         (ensures read_word g1 (hd_address o) == read_word g0 (hd_address o))
       = assert (Seq.mem o (objects nxt g0));
         mem_from_le_hd_address nxt g0 o;
         hd_address_bounds o
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires word_agree));
    assert (walk_pre g0 g1 nxt (Seq.tail objs) all_objs 0UL 0);
    assert (Seq.length g1 == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g1);
    assert (post_sweep_strong g0);
    assert (walk_visits g1 zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g1 == Seq.tail objs);
    objects_agree_above g g1 start (U64.v start);
    objects_agree_above g g1 nxt (U64.v start);
    assert (objects start g1 == Seq.cons x (objects nxt g1));
    assert (read_word g start == read_word g0 start);
    caw_clause4_ext_white g0 g g1 start nxt x first_blue run_words fp;
    assert (white_inv g0 g1 nxt (Seq.tail objs) 0UL 0 all_objs);
    // adj_free_inv's own extra clauses at the reset state (floor = `nxt`).
    objects_split_from g1 zero_addr start;
    eliminate exists (pre1: seq obj_addr).
        objects zero_addr g1 == Seq.append pre1 (objects start g1) /\
        (forall (z: obj_addr). Seq.mem z pre1 ==> U64.v (hd_address z) < U64.v start) /\
        (forall (z: obj_addr). Seq.mem z (objects start g1) ==> U64.v (hd_address z) >= U64.v start)
    with begin
      let pairwise (x' y': obj_addr)
        : Lemma
          (requires
            Seq.mem x' (objects zero_addr g1) /\ Seq.mem y' (objects zero_addr g1) /\
            is_blue x' g1 /\ is_blue y' g1 /\ adjacent g1 x' y' /\
            U64.v (hd_address y') < U64.v nxt)
          (ensures False)
        = mem_append_lemma y' pre1 (objects start g1);
          if Seq.mem y' pre1 then begin
            if run_words = 0 then ()
            else begin
              run_words_bound first_blue run_words start;
              h_addr_agree first_blue;
              flush_conserves_adj_free g start first_blue run_words fp;
              eliminate forall (x: obj_addr) (y: obj_addr).
                  Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
                  is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y /\
                  U64.v (hd_address y) < U64.v start ==> False
              with x' y'
            end
          end else begin
            mem_cons_lemma y' x (objects nxt g1);
            (if not (y' = x) then begin
               objects_addresses_gt_start nxt g1 y';
               hd_address_spec y'
             end);
            assert (y' == x)
          end
      in
      FStar.Classical.forall_intro_2 (fun x' -> FStar.Classical.move_requires (pairwise x'));
      let no_blue_ends (z: obj_addr)
        : Lemma
          (requires Seq.mem z (objects zero_addr g1) /\ is_blue z g1 /\ next_pos g1 z == U64.v nxt)
          (ensures False)
        = mem_append_lemma z pre1 (objects start g1);
          if Seq.mem z pre1 then begin
            objects_no_straddle g1 zero_addr start z
            // next_pos g1 z <= start < nxt, contradicting next_pos g1 z == nxt.
          end else begin
            mem_cons_lemma z x (objects nxt g1);
            (if not (z = x) then begin
               objects_addresses_gt_start nxt g1 z;
               hd_address_spec z
               // hd_address z >= nxt, so next_pos g1 z > nxt, contradicting == nxt.
             end);
            assert (z == x)
            // x is white, contradicting is_blue z g1.
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires no_blue_ends)
    end;
    assert (adj_free_inv g0 g1 nxt (Seq.tail objs) 0UL 0 all_objs);
    coalesce_aux_no_adjacent_blue_aux g0 g1 nxt (Seq.tail objs) 0UL 0 fp1 all_objs
#pop-options

let coalesce_no_adjacent_blue g =
  // `adj_free_inv`'s two extra clauses at the top level: vacuous, since no
  // object's header can sit strictly below `zero_addr` (the walk's own
  // start) or have its extent end exactly there.
  let no_pairwise (x y: obj_addr)
    : Lemma
      (requires
        Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
        is_blue x g /\ is_blue y g /\ adjacent g x y /\
        U64.v (hd_address y) < U64.v zero_addr)
      (ensures False)
    = mem_from_le_hd_address zero_addr g y
  in
  FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (no_pairwise x));
  let no_blue_ends (z: obj_addr)
    : Lemma
      (requires
        Seq.mem z (objects zero_addr g) /\ is_blue z g /\
        next_pos g z == U64.v zero_addr)
      (ensures False)
    = mem_from_le_hd_address zero_addr g z
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires no_blue_ends);
  coalesce_aux_no_adjacent_blue_aux g g zero_addr (objects zero_addr g) 0UL 0 0UL
                                    (objects zero_addr g)

/// ---------------------------------------------------------------------------
/// Top level
/// ---------------------------------------------------------------------------

/// **Coalescing correctness.**
///
/// 3a and 3b together say that each input run becomes exactly one output
/// block: identical blue coverage means no run splits or moves, and
/// non-adjacency means no run stays as two blocks.  Neither needs a
/// definition of "run".
val coalesce_correct (g: heap)
  : Lemma
    (requires post_sweep_strong g /\
              SI.heap_objects_dense g /\
              Seq.length g == heap_size /\
              Seq.length (objects zero_addr g) > 0)
    (ensures
      (let g' = fst (coalesce g) in

       // 2. No free word is gained or lost.
       total_blue_whsize g' == total_blue_whsize g /\

       // 3a. The blue region of the heap is unchanged, word for word.
       (forall (p: nat). p < heap_size ==> (blue_covered g' p <==> blue_covered g p)) /\

       // 3b. No two blue objects of the output are adjacent.
       (forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g') /\ Seq.mem y (objects zero_addr g') /\
          is_blue x g' /\ is_blue y g' /\ adjacent g' x y ==> False) /\

       // White objects are untouched: same object, same size.
       (forall (x: obj_addr).
          Seq.mem x (objects zero_addr g) /\ is_white x g ==>
          Seq.mem x (objects zero_addr g') /\ is_white x g' /\
          wosize_of_object x g' == wosize_of_object x g)))

let coalesce_correct g =
  coalesce_conserves_whsize g;
  coalesce_preserves_blue_coverage g;
  coalesce_no_adjacent_blue g;
  coalesce_preserves_white g