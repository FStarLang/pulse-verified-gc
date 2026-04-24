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

#set-options "--z3rlimit 50 --fuel 2 --ifuel 1"

open FStar.Seq

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
module HeapGraph = GC.Spec.HeapGraph
module Alloc = GC.Spec.Allocator

/// ---------------------------------------------------------------------------
/// Post-sweep heap predicate
/// ---------------------------------------------------------------------------

/// A heap where all objects are white or blue (output of sweep)
let post_sweep (g: heap) : prop =
  well_formed_heap g /\
  (forall (x: obj_addr). Seq.mem x (objects 0UL g) ==>
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
  coalesce_aux g g (objects 0UL g) 0UL 0 0UL

/// One-step unfolding: empty case
let coalesce_aux_empty (g0 g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma (coalesce_aux g0 g Seq.empty first_blue run_words fp ==
           flush_blue g first_blue run_words fp)
  = ()

/// One-step unfolding: white (non-blue) case — fst projection
/// Takes flush results as parameters to avoid Z3 substitution issues
let coalesce_aux_white_step_fst
  (g0 g: heap) (objs: seq obj_addr) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (gf: heap) (fpf: U64.t)
  : Lemma
    (requires Seq.length objs > 0 /\ ~(is_blue (Seq.head objs) g0) /\
              gf == fst (flush_blue g first_blue run_words fp) /\
              fpf == snd (flush_blue g first_blue run_words fp))
    (ensures
      fst (coalesce_aux g0 g objs first_blue run_words fp) ==
        fst (coalesce_aux g0 gf (Seq.tail objs) 0UL 0 fpf))
  = ()

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
#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
val addr_in_object_outside_other
  (g: heap) (x o: obj_addr) (addr: hp_addr)
  : Lemma
    (requires
      Seq.mem x (objects 0UL g) /\ Seq.mem o (objects 0UL g) /\
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
    objects_separated 0UL g x o;
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
    objects_separated 0UL g o x;
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
      Seq.mem x (objects 0UL g) /\ is_white x g /\
      U64.v addr >= U64.v (hd_address x) /\
      U64.v addr < U64.v (hd_address x) + (U64.v (wosize_of_object x g) + 1) * U64.v mword)
    (ensures
      forall (o: obj_addr). Seq.mem o (objects 0UL g) /\ is_blue o g ==>
        (U64.v addr + U64.v mword <= U64.v (hd_address o) \/
         U64.v addr >= U64.v (hd_address o) + (U64.v (wosize_of_object o g) + 1) * U64.v mword))

let white_addr_outside_all_blue g x addr =
  let aux (o: obj_addr)
    : Lemma
      (requires Seq.mem o (objects 0UL g) /\ is_blue o g)
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

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
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

#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
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

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
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

/// The merged header has getWosize == run_words - 1
val flush_blue_wosize_spec
  (g: heap) (first_blue: obj_addr) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      run_words > 0 /\
      run_words - 1 < pow2 54 /\
      U64.v (hd_address first_blue) + run_words * U64.v mword <= heap_size /\
      Seq.length g == heap_size)
    (ensures (
      let (g', _) = flush_blue g first_blue run_words fp in
      U64.v (getWosize (read_word g' (hd_address first_blue))) == run_words - 1))

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let flush_blue_wosize_spec g first_blue run_words fp =
  flush_blue_header_spec g first_blue run_words fp;
  let wz = run_words - 1 in
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  let wz_u64 : wosize = U64.uint_to_t wz in
  makeHeader_getWosize wz_u64 Blue 0UL
#pop-options

/// ---------------------------------------------------------------------------
/// Walk structure helpers (moved early for use by later lemmas)
/// ---------------------------------------------------------------------------

/// When objects walk ends (next >= heap_size), tail is empty.
/// This follows from the objects definition with fuel 2.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
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

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
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
      all_objs == objects 0UL g0 /\
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
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
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

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
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
    (requires post_sweep g /\ Seq.mem x (objects 0UL g) /\ is_white x g)
    (ensures read_word (fst (coalesce g)) (hd_address x)
          == read_word g (hd_address x))

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let coalesce_preserves_survivor_header g x =
  hd_address_spec x;
  wosize_of_object_bound x g;
  let addr = hd_address x in
  white_addr_outside_all_blue g x addr;
  coalesce_aux_preserves_outside g g 0UL (objects 0UL g) 0UL 0 0UL (objects 0UL g) addr
#pop-options

/// Coalesce preserves survivor fields
val coalesce_preserves_survivor_field
  (g: heap) (x: obj_addr) (i: U64.t{U64.v i >= 1})
  : Lemma
    (requires post_sweep g /\
             Seq.mem x (objects 0UL g) /\ is_white x g /\
             U64.v i <= U64.v (wosize_of_object x g))
    (ensures HeapGraph.get_field (fst (coalesce g)) x i
          == HeapGraph.get_field g x i)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
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
    coalesce_aux_preserves_outside g g 0UL (objects 0UL g) 0UL 0 0UL (objects 0UL g) field_addr
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
  coalesce_aux_preserves_length g g (objects 0UL g) 0UL 0 0UL

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

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let coalesce_heap_preserves_outside
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr) (addr: hp_addr)
  : Lemma
    (requires
      objs == objects start g0 /\
      all_objs == objects 0UL g0 /\
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

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
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
  all_objs == objects 0UL g0 /\
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
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let objects_nonempty_at (start: hp_addr) (g g0: heap)
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
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let run_words_bound
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

/// Helper: stepping over a merged blue block.
/// If the merged header at hd_address fb has wosize = run_words - 1,
/// and the next from there equals start, then:
/// - objects (hd_address fb) g' is non-empty
/// - fb is in that list
/// - any x in objects start g' is also in that list
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
private let merged_block_step
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
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
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
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
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

/// Helper: flush preserves headers of white objects that come later in the walk.
/// Used to maintain the walk_pre invariant across the white case.
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
private let flush_preserves_later_white_headers
  (g0 g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (start: hp_addr) (next: hp_addr) (objs_tail: seq obj_addr)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      Seq.length g0 == heap_size /\
      objs_tail == objects next g0 /\
      U64.v next > U64.v start /\
      (run_words > 0 ==>
        (U64.v first_blue >= U64.v mword /\
         U64.v first_blue < heap_size /\
         U64.v first_blue % U64.v mword == 0 /\
         U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start)) /\
      (forall (o: obj_addr). Seq.mem o objs_tail /\ is_white o g0 ==>
        read_word g (hd_address o) == read_word g0 (hd_address o)))
    (ensures (
      let (g_flush, _) = flush_blue g first_blue run_words fp in
      forall (o: obj_addr). Seq.mem o objs_tail /\ is_white o g0 ==>
        read_word g_flush (hd_address o) == read_word g0 (hd_address o)))
  = let (g_flush, _) = flush_blue g first_blue run_words fp in
    let aux (o: obj_addr)
      : Lemma
        (requires Seq.mem o objs_tail /\ is_white o g0)
        (ensures read_word g_flush (hd_address o) == read_word g0 (hd_address o))
      = // o is in objects next g0 so U64.v o > U64.v next > U64.v start
        objects_addresses_gt_start next g0 o;
        hd_address_spec o;
        // hd_address o = o - 8 > next - 8 >= start
        // flush region: [first_blue - 8, first_blue - 8 + run_words * 8) = [first_blue - 8, start)
        // hd_address o >= start, so outside flush region
        flush_blue_preserves_outside g first_blue run_words fp (hd_address o)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

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

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1 --split_queries always"
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
/// Property B: all objects in coalesced walk are white or blue
/// ---------------------------------------------------------------------------

val coalesce_aux_walk_all_wb
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr) (y: obj_addr)
  : Lemma
    (requires
      walk_pre g0 g start objs all_objs first_blue run_words /\
      (forall (addr: hp_addr). U64.v addr >= U64.v start ==>
        read_word g addr == read_word g0 addr) /\
      (let sync : hp_addr =
         if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
       Seq.mem y (objects sync (coalesce_heap g0 g objs first_blue run_words fp))))
    (ensures (
      let g' = coalesce_heap g0 g objs first_blue run_words fp in
      (Seq.mem y objs /\ is_white y g0) \/ is_blue y g'))
    (decreases Seq.length objs)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1 --split_queries always"
let rec coalesce_aux_walk_all_wb g0 g start objs first_blue run_words fp all_objs y =
  if Seq.length objs = 0 then begin
    assert (Seq.equal objs Seq.empty);
    coalesce_heap_empty g0 g first_blue run_words fp;
    let g' = coalesce_heap g0 g objs first_blue run_words fp in
    if run_words > 0 then begin
      flush_blue_preserves_length g first_blue run_words fp;
      hd_address_spec (first_blue <: obj_addr);
      run_words_bound first_blue run_words start;
      flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
      let wz : wosize = U64.uint_to_t (run_words - 1) in
      merged_block_decompose g' (first_blue <: obj_addr) run_words start y;
      if y = (first_blue <: obj_addr) then
        merged_block_is_blue g' (first_blue <: obj_addr) wz
      else begin
        // y ≠ first_blue, so from merged_block_decompose: y ∈ objects start g'
        // We show objects start g' = objects start g0 = Seq.empty → contradiction
        // Step 1: g' = fst (flush_blue g first_blue run_words fp) (from coalesce_heap_empty)
        // Step 2: flush preserves reads at start (start >= end of blue run)
        flush_blue_preserves_outside g first_blue run_words fp start;
        assert (read_word g' start == read_word g start);
        // Step 3: g agrees with g0 at start (new invariant)
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
        coalesce_aux_walk_all_wb g0 g next (Seq.tail objs)
          new_first new_rw fp all_objs y
      end
      else begin
        objects_tail_empty_when_done start g0;
        assert (Seq.equal (Seq.tail objs) Seq.empty);
        coalesce_heap_empty g0 g new_first new_rw fp;
        let g' = coalesce_heap g0 g objs first_blue run_words fp in
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
        FStar.Math.Lemmas.pow2_lt_compat 64 54;
        let wz_merged : wosize = U64.uint_to_t (new_rw - 1) in
        flush_blue_header_spec g (new_first <: obj_addr) new_rw fp;
        merged_block_decompose g' (new_first <: obj_addr) new_rw rest_u64 y;
        merged_block_is_blue g' (new_first <: obj_addr) wz_merged
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
      let g' = coalesce_heap g0 g objs first_blue run_words fp in
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
          // sync = hd_address first_blue
          // Need merged header in g' for decomposition
          hd_address_spec (first_blue <: obj_addr);
          run_words_bound first_blue run_words start;
          flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
          // Preserve merged header from g_flush to g'
          coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
            0UL 0 fp_flush (hd_address (first_blue <: obj_addr));
          let wz_fb : wosize = U64.uint_to_t (run_words - 1) in
          merged_block_decompose g' (first_blue <: obj_addr) run_words start y;
          if y = (first_blue <: obj_addr) then
            merged_block_is_blue g' (first_blue <: obj_addr) wz_fb
          else begin
            // y ∈ objects start g', decompose further
            // y = obj or y ∈ objects next g'
            if y = obj then ()  // white in objs
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
              coalesce_aux_walk_all_wb g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs y;
              if Seq.mem y (Seq.tail objs) then
                mem_cons_lemma y obj (Seq.tail objs)
            end
          end
        end
        else begin
          // run_words = 0, sync = start
          // y ∈ objects start g'
          // y = obj or y ∈ objects next g'
          if y = obj then ()  // white in objs
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
            coalesce_aux_walk_all_wb g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs y;
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
          if y = (first_blue <: obj_addr) then
            merged_block_is_blue g' (first_blue <: obj_addr) wz_fb
          else begin
            // y ∈ objects start g', but rest_start >= heap_size
            flush_blue_preserves_outside g first_blue run_words fp start;
            assert (read_word g' start == read_word g0 start);
            objects_nonempty_at start g' g0;
            objects_nonempty_next start g';
            mem_cons_lemma y (f_address start) (Seq.tail (objects start g'));
            // y = obj (rest is empty since rest_start >= heap_size)
            assert (y == obj);
            assert (Seq.mem y objs /\ is_white y g0)
          end
        end
        else begin
          // run_words = 0, sync = start, g' = g_flush = g
          objects_nonempty_at start g' g0;
          objects_nonempty_next start g';
          mem_cons_lemma y (f_address start) (Seq.tail (objects start g'));
          assert (y == obj);
          assert (Seq.mem y objs /\ is_white y g0)
        end
      end
    end
  end
#pop-options

/// ---------------------------------------------------------------------------

val coalesce_survivors_in_objects (g: heap) (x: obj_addr)
  : Lemma
    (requires post_sweep g /\ Seq.mem x (objects 0UL g) /\ is_white x g)
    (ensures Seq.mem x (objects 0UL (fst (coalesce g))))

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let coalesce_survivors_in_objects g x =
  coalesce_aux_survivors_in_walk g g 0UL (objects 0UL g) 0UL 0 0UL (objects 0UL g) x;
  coalesce_heap_unfold g g (objects 0UL g) 0UL 0 0UL
#pop-options

val coalesce_all_white_or_blue (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures (forall (x: obj_addr).
               Seq.mem x (objects 0UL (fst (coalesce g))) ==>
               is_white x (fst (coalesce g)) \/ is_blue x (fst (coalesce g))))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries always"
let coalesce_all_white_or_blue g =
  coalesce_heap_unfold g g (objects 0UL g) 0UL 0 0UL;
  let g' = fst (coalesce g) in
  assert (g' == coalesce_heap g g (objects 0UL g) 0UL 0 0UL);
  let aux (x: obj_addr)
    : Lemma (requires Seq.mem x (objects 0UL g'))
            (ensures is_white x g' \/ is_blue x g')
    = coalesce_aux_walk_all_wb g g 0UL (objects 0UL g) 0UL 0 0UL (objects 0UL g) x;
      // walk_all_wb gives: (mem x (objects 0UL g) /\ is_white x g) \/ is_blue x g'
      // White case: coalesce preserves white headers → is_white x g'
      if Seq.mem x (objects 0UL g) && is_white x g then begin
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
    Seq.mem x (objects 0UL g) /\ is_white x g /\
    i >= 1 /\ i <= U64.v (wosize_of_object x g) /\ i < pow2 64 ==>
    (let iu = U64.uint_to_t i in
     let field_val = HeapGraph.get_field g x iu in
     field_val = 0UL \/
     U64.v field_val < U64.v mword \/
     U64.v field_val >= heap_size \/
     U64.v field_val % U64.v mword <> 0 \/
     ~(Seq.mem (field_val <: obj_addr) (objects 0UL g) /\ is_blue (field_val <: obj_addr) g)))

val coalesce_preserves_wf (g: heap)
  : Lemma
    (requires post_sweep_strong g)
    (ensures well_formed_heap (fst (coalesce g)))

/// ---------------------------------------------------------------------------
/// coalesce_preserves_wf proof helpers
/// ---------------------------------------------------------------------------

/// Arithmetic: efptu field address doesn't overflow for obj_addr indices
#push-options "--z3rlimit 100"
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
#push-options "--z3rlimit 50"
private let coalesce_blue_size_bound (g: heap) (obj: obj_addr)
  : Lemma
    (requires
      post_sweep_strong g /\
      Seq.mem obj (objects 0UL (fst (coalesce g))) /\
      is_blue obj (fst (coalesce g)))
    (ensures (
      let g' = fst (coalesce g) in
      let wz = wosize_of_object obj g' in
      U64.v (hd_address obj) + 8 + U64.v wz * 8 <= Seq.length g'))
  = let g' = fst (coalesce g) in
    coalesce_preserves_length g;
    objects_member_size_bound 0UL g' obj;
    hd_address_spec obj;
    wosize_of_object_spec obj g'

#pop-options

/// ---------------------------------------------------------------------------
/// Property C: blue objects in coalesced walk have tag 0
/// ---------------------------------------------------------------------------

/// For any object in the coalesced walk that is blue, tag_of_object = 0UL.
/// Same structure as coalesce_aux_walk_all_wb but with strengthened postcondition.
val coalesce_aux_blue_tag_zero
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr) (y: obj_addr)
  : Lemma
    (requires
      walk_pre g0 g start objs all_objs first_blue run_words /\
      (forall (addr: hp_addr). U64.v addr >= U64.v start ==>
        read_word g addr == read_word g0 addr) /\
      (let sync : hp_addr =
         if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
       Seq.mem y (objects sync (coalesce_heap g0 g objs first_blue run_words fp))) /\
      is_blue y (coalesce_heap g0 g objs first_blue run_words fp))
    (ensures tag_of_object y (coalesce_heap g0 g objs first_blue run_words fp) == 0UL)
    (decreases Seq.length objs)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1 --split_queries always"
let rec coalesce_aux_blue_tag_zero g0 g start objs first_blue run_words fp all_objs y =
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
        makeHeader_getTag wz Blue 0UL;
        tag_of_object_spec y g'
      end else begin
        // y in objects start g' but objs = empty => objects start g0 = empty
        // g' at start = g at start = g0 at start (preserved)
        flush_blue_preserves_outside g first_blue run_words fp start;
        assert (read_word g' start == read_word g0 start);
        assert (Seq.length g' == heap_size);
        // objects start g' must be consistent with objects start g0
        // but objs == Seq.empty means start >= heap_size from objects def
        // so objects start g' is also empty -> contradiction with y in it
        ()
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
        coalesce_aux_blue_tag_zero g0 g next (Seq.tail objs)
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
        assert (new_rw - 1 < pow2 54);
        let wz_merged : wosize = U64.uint_to_t (new_rw - 1) in
        flush_blue_header_spec g (new_first <: obj_addr) new_rw fp;
        merged_block_decompose g' (new_first <: obj_addr) new_rw rest_u64 y;
        // y must be new_first since rest is empty
        makeHeader_getTag wz_merged Blue 0UL;
        tag_of_object_spec y g'
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

        coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
          0UL 0 fp_flush start;
        flush_blue_preserves_outside g first_blue run_words fp start;
        assert (read_word g' start == read_word g0 start);

        objects_nonempty_at start g' g0;
        objects_nonempty_next start g';
        Seq.cons_head_tail (objects start g');
        f_address_spec start;
        mem_cons_lemma y (f_address start) (Seq.tail (objects start g'));
        Seq.lemma_tl obj (objects next g');

        if run_words > 0 then begin
          hd_address_spec (first_blue <: obj_addr);
          run_words_bound first_blue run_words start;
          flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
          coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
            0UL 0 fp_flush (hd_address (first_blue <: obj_addr));
          let wz_fb : wosize = U64.uint_to_t (run_words - 1) in
          merged_block_decompose g' (first_blue <: obj_addr) run_words start y;
          if y = (first_blue <: obj_addr) then begin
            makeHeader_getTag wz_fb Blue 0UL;
            tag_of_object_spec y g'
          end
          else begin
            // y in objects start g': either y = obj or y in objects next g'
            if y = obj then begin
              // obj is white in g0. Show ~(is_blue obj g') => contradiction with precondition
              // Header of obj at start is preserved: read_word g' start == read_word g0 start
              // hd_address obj = start, and header is same => same color
              color_of_header_eq obj g0 g';
              is_blue_iff obj g'; is_blue_iff obj g0
              // obj is white in g0, so is_blue obj g0 = false = is_blue obj g' — contradicts precondition
            end
            else begin
              assert (Seq.mem y (objects next g'));
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
              coalesce_aux_blue_tag_zero g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs y
            end
          end
        end
        else begin
          // run_words = 0: sync = start, y in objects start g'
          if y = obj then begin
            // obj is white in g0. Show ~(is_blue obj g')
            color_of_header_eq obj g0 g';
            is_blue_iff obj g'; is_blue_iff obj g0
          end
          else begin
            assert (Seq.mem y (objects next g'));
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
            coalesce_aux_blue_tag_zero g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs y
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
            makeHeader_getTag wz_fb Blue 0UL;
            tag_of_object_spec y g'
          end
          else begin
            // y in objects start g' but tail is empty => next >= heap_size
            flush_blue_preserves_outside g first_blue run_words fp start;
            assert (read_word g' start == read_word g0 start);
            objects_nonempty_at start g' g0;
            objects_nonempty_next start g';
            mem_cons_lemma y (f_address start) (Seq.tail (objects start g'));
            // y = obj, which is white in g0
            assert (y == obj);
            color_of_header_eq y g0 g';
            is_blue_iff y g'; is_blue_iff y g0
          end
        end
        else begin
          // run_words = 0: g' = g_flush = fst(flush_blue g 0UL 0 fp') = g (no-op flush)
          // g_flush = g since flush_blue with run_words=0 is identity
          flush_blue_preserves_outside g first_blue run_words fp start;
          assert (read_word g' start == read_word g0 start);
          objects_nonempty_at start g' g0;
          objects_nonempty_next start g';
          mem_cons_lemma y (f_address start) (Seq.tail (objects start g'));
          assert (y == obj);
          color_of_header_eq y g0 g';
          is_blue_iff y g'; is_blue_iff y g0
        end
      end
    end
  end
#pop-options

/// Blue objects after coalescing are not infix (tag = 0, not infix_tag).
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
private let coalesce_blue_not_infix (g: heap) (obj: obj_addr)
  : Lemma
    (requires
      post_sweep_strong g /\
      Seq.mem obj (objects 0UL (fst (coalesce g))) /\
      is_blue obj (fst (coalesce g)))
    (ensures ~(is_infix obj (fst (coalesce g))))
  = let g' = fst (coalesce g) in
    coalesce_heap_unfold g g (objects 0UL g) 0UL 0 0UL;
    assert (g' == coalesce_heap g g (objects 0UL g) 0UL 0 0UL);
    coalesce_aux_blue_tag_zero g g 0UL (objects 0UL g) 0UL 0 0UL (objects 0UL g) obj;
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
private let flush_blue_field1_spec
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
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
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
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
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
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
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
#push-options "--z3rlimit 600 --fuel 2 --ifuel 1 --split_queries always"
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

#push-options "--z3rlimit 600 --fuel 1 --ifuel 1 --split_queries always"
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
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
private let coalesce_blue_field_closure (g: heap) (src dst: obj_addr)
  : Lemma
    (requires
      post_sweep_strong g /\
      Seq.mem src (objects 0UL (fst (coalesce g))) /\
      is_blue src (fst (coalesce g)) /\
      (let g' = fst (coalesce g) in
       let wz = wosize_of_object src g' in
       U64.v wz < pow2 54 /\
       exists_field_pointing_to_unchecked g' src wz dst))
    (ensures Seq.mem dst (objects 0UL (fst (coalesce g))))
  = let g' = fst (coalesce g) in
    let wz = wosize_of_object src g' in
    coalesce_heap_unfold g g (objects 0UL g) 0UL 0 0UL;
    assert (g' == coalesce_heap g g (objects 0UL g) 0UL 0 0UL);
    coalesce_preserves_length g;
    // wz >= 1 since efptu requires a matching field at idx in [0, wz)
    assert (wz <> 0UL);
    assert (U64.v wz >= 1);
    coalesce_aux_blue_field0_valid g g 0UL (objects 0UL g) (objects 0UL g) 0UL 0 0UL src;
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
    // fv != 0UL, so from the disjunction: bounds /\ mem fv (objects 0UL g')
    assert (Seq.mem (fv <: obj_addr) (objects 0UL g'));
    hd_address_spec (fv <: obj_addr);
    hd_address_spec dst;
    assert (hd_address fv == hd_address dst);
    assert (fv == dst)
#pop-options

/// Helper: if efptu g src wz dst and src is white and dst is blue, contradiction
/// from post_sweep_strong.
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
private let rec coalesce_white_field_not_blue
  (g: heap) (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (dst: obj_addr)
  : Lemma
    (requires
      post_sweep_strong g /\
      Seq.mem src (objects 0UL g) /\ is_white src g /\
      U64.v wz <= U64.v (wosize_of_object src g) /\
      exists_field_pointing_to_unchecked g src wz dst /\
      Seq.mem dst (objects 0UL g) /\ is_blue dst g)
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
        assert (Seq.mem (fv <: obj_addr) (objects 0UL g) /\ is_blue (fv <: obj_addr) g)
      end
      else begin
        coalesce_white_field_not_blue g src idx dst
      end
    end
#pop-options

/// Key recursive lemma: for white survivors, efptu on g' implies efptu on g.
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
private let rec white_src_efptu_transfer
  (g: heap) (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (dst: obj_addr)
  : Lemma
    (requires
      post_sweep_strong g /\
      Seq.mem src (objects 0UL g) /\ is_white src g /\
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
      coalesce_aux_preserves_outside g g 0UL (objects 0UL g) 0UL 0 0UL (objects 0UL g) (far <: hp_addr);
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

/// For a white source in g', if efptu g' src wz dst, then dst in objects 0UL g'.
#push-options "--z3rlimit 400 --fuel 1 --ifuel 0"
private let white_src_field_closure (g: heap) (src dst: obj_addr)
  : Lemma
    (requires
      post_sweep_strong g /\
      Seq.mem src (objects 0UL g) /\ is_white src g /\
      Seq.mem src (objects 0UL (fst (coalesce g))) /\
      (let g' = fst (coalesce g) in
       let wz = wosize_of_object src g' in
       U64.v wz < pow2 54 /\
       exists_field_pointing_to_unchecked g' src wz dst))
    (ensures Seq.mem dst (objects 0UL (fst (coalesce g))))
  = let g' = fst (coalesce g) in
    coalesce_preserves_survivor_header g src;
    wosize_of_object_spec src g;
    wosize_of_object_spec src g';
    assert (wosize_of_object src g' == wosize_of_object src g);
    let wz = wosize_of_object src g in
    wosize_of_object_bound src g;
    // Transfer efptu from g' to g
    white_src_efptu_transfer g src wz dst;
    // In g, wf gives dst in objects 0UL g
    wf_field_target_in_objects g src dst;
    assert (Seq.mem dst (objects 0UL g));
    // If blue: contradiction from post_sweep_strong
    // If white: coalesce_survivors_in_objects gives dst in objects g'
    if is_blue dst g then
      coalesce_white_field_not_blue g src wz dst
    else
      coalesce_survivors_in_objects g dst
#pop-options

/// ---------------------------------------------------------------------------
/// Main proof: coalesce_preserves_wf
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
let coalesce_preserves_wf g =
  let g' = fst (coalesce g) in
  coalesce_heap_unfold g g (objects 0UL g) 0UL 0 0UL;
  coalesce_preserves_length g;

  // --- Part 4: no infix objects in g' ---
  let part4_aux (obj: obj_addr)
    : Lemma
      (requires Seq.mem obj (objects 0UL g'))
      (ensures ~(is_infix obj g'))
    = coalesce_all_white_or_blue g;
      if is_blue obj g' then
        coalesce_blue_not_infix g obj
      else begin
        assert (g' == coalesce_heap g g (objects 0UL g) 0UL 0 0UL);
        coalesce_aux_walk_all_wb g g 0UL (objects 0UL g) 0UL 0 0UL (objects 0UL g) obj;
        is_white_iff obj g';
        is_blue_iff obj g';
        assert (Seq.mem obj (objects 0UL g) /\ is_white obj g);
        coalesce_preserves_survivor_header g obj;
        tag_of_object_spec obj g;
        tag_of_object_spec obj g';
        is_infix_spec obj g;
        is_infix_spec obj g';
        wf_objects_non_infix g obj
      end
  in
  let part4_imp (obj: obj_addr)
    : Lemma (Seq.mem obj (objects 0UL g') ==> ~(is_infix obj g'))
    = FStar.Classical.move_requires part4_aux obj
  in
  FStar.Classical.forall_intro part4_imp;
  assert (well_formed_heap_part4 g');

  // --- Part 3: infix_wf (vacuously true from Part 4) ---
  let part3_pf (h: obj_addr)
    : Lemma
      (requires Seq.mem h (objects 0UL g') /\ is_infix h g')
      (ensures (let p = GC.Spec.Object.parent_closure_addr_nat h g' in
                p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
                Seq.mem (U64.uint_to_t p) (objects 0UL g') /\
                GC.Spec.Object.is_closure (U64.uint_to_t p) g'))
    = part4_aux h
  in
  GC.Spec.Object.infix_wf_intro g' (objects 0UL g') part3_pf;
  assert (well_formed_heap_part3 g');

  // --- Part 1: size bounds ---
  let part1_aux (h: obj_addr)
    : Lemma
      (requires Seq.mem h (objects 0UL g'))
      (ensures (let wz = wosize_of_object h g' in
                U64.v (hd_address h) + 8 + U64.v wz * 8 <= Seq.length g'))
    = coalesce_all_white_or_blue g;
      if is_blue h g' then
        coalesce_blue_size_bound g h
      else begin
        assert (g' == coalesce_heap g g (objects 0UL g) 0UL 0 0UL);
        coalesce_aux_walk_all_wb g g 0UL (objects 0UL g) 0UL 0 0UL (objects 0UL g) h;
        is_white_iff h g';
        is_blue_iff h g';
        assert (Seq.mem h (objects 0UL g) /\ is_white h g);
        coalesce_preserves_survivor_header g h;
        wosize_of_object_spec h g;
        wosize_of_object_spec h g';
        assert (wosize_of_object h g' == wosize_of_object h g);
        wf_object_size_bound g h
      end
  in
  let part1_imp (h: obj_addr)
    : Lemma (Seq.mem h (objects 0UL g') ==>
             (let wz = wosize_of_object h g' in
              U64.v (hd_address h) + 8 + U64.v wz * 8 <= Seq.length g'))
    = FStar.Classical.move_requires part1_aux h
  in
  FStar.Classical.forall_intro part1_imp;
  assert (well_formed_heap_part1 g');

  // --- Part 2: field pointer closure ---
  let part2_aux (src dst: obj_addr)
    : Lemma
      (requires
        Seq.mem src (objects 0UL g') /\
        (let wz = wosize_of_object src g' in
         U64.v wz < pow2 54 /\
         exists_field_pointing_to_unchecked g' src wz dst))
      (ensures Seq.mem dst (objects 0UL g'))
    = coalesce_all_white_or_blue g;
      if is_blue src g' then
        coalesce_blue_field_closure g src dst
      else begin
        assert (g' == coalesce_heap g g (objects 0UL g) 0UL 0 0UL);
        coalesce_aux_walk_all_wb g g 0UL (objects 0UL g) 0UL 0 0UL (objects 0UL g) src;
        is_white_iff src g';
        is_blue_iff src g';
        assert (Seq.mem src (objects 0UL g) /\ is_white src g);
        white_src_field_closure g src dst
      end
  in
  let part2_flat (src dst: obj_addr)
    : Lemma
      (requires
        Seq.mem src (objects 0UL g') /\
        U64.v (wosize_of_object src g') < pow2 54 /\
        exists_field_pointing_to_unchecked g' src (wosize_of_object src g') dst)
      (ensures Seq.mem dst (objects 0UL g'))
    = part2_aux src dst
  in
  let part2_imp (src dst: obj_addr)
    : Lemma ((Seq.mem src (objects 0UL g') /\
              U64.v (wosize_of_object src g') < pow2 54 /\
              exists_field_pointing_to_unchecked g' src (wosize_of_object src g') dst) ==>
             Seq.mem dst (objects 0UL g'))
    = FStar.Classical.move_requires (part2_flat src) dst
  in
  FStar.Classical.forall_intro_2 part2_imp;
  assert (well_formed_heap_part2 g');

  // --- Combine all parts ---
  reveal_opaque (`%well_formed_heap) well_formed_heap
#pop-options

/// ---------------------------------------------------------------------------
/// Free list validity
/// ---------------------------------------------------------------------------

val coalesce_fp_valid (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures (let (g', fp') = coalesce g in
             fp' = 0UL \/
             (U64.v fp' >= U64.v mword /\
              U64.v fp' < heap_size /\
              U64.v fp' % U64.v mword == 0 /\
              Seq.mem (fp' <: obj_addr) (objects 0UL g'))))

/// Helper: flush_blue's second component is either fp or first_blue
private let flush_blue_snd_cases (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma (snd (flush_blue g first_blue run_words fp) == fp \/
           snd (flush_blue g first_blue run_words fp) == first_blue)
  = ()

/// Helper: when flush returns first_blue, it's in the walk from sync
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
private let flush_blue_fb_in_walk
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t) (start: hp_addr)
  : Lemma
    (requires
      run_words > 0 /\
      U64.v first_blue >= U64.v mword /\
      U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start /\
      run_words - 1 < pow2 54 /\
      Seq.length g == heap_size /\
      snd (flush_blue g first_blue run_words fp) == first_blue)
    (ensures (
      let g' = fst (flush_blue g first_blue run_words fp) in
      let sync : hp_addr = hd_address (first_blue <: obj_addr) in
      Seq.mem (first_blue <: obj_addr) (objects sync g')))
  = let fb : obj_addr = first_blue in
    hd_address_spec fb;
    let sync = hd_address fb in
    flush_blue_header_spec g fb run_words fp;
    flush_blue_preserves_length g first_blue run_words fp;
    let g' = fst (flush_blue g first_blue run_words fp) in
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    f_address_spec sync;
    if U64.v start >= heap_size then
      mem_cons_lemma fb fb Seq.empty
    else
      mem_cons_lemma fb fb (objects start g')
#pop-options


/// Recursive lemma: the fp returned by coalesce_aux is either 0UL,
/// the incoming fp, or a valid obj_addr in the walk from sync.
val coalesce_aux_fp_in_walk
  (g0 g: heap) (start: hp_addr) (objs all_objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires walk_pre g0 g start objs all_objs first_blue run_words /\
             (forall (addr: hp_addr). U64.v addr >= U64.v start ==>
               read_word g addr == read_word g0 addr))
    (ensures (
      let fp' = snd (coalesce_aux g0 g objs first_blue run_words fp) in
      let g' = coalesce_heap g0 g objs first_blue run_words fp in
      let sync : hp_addr =
        if run_words > 0 then hd_address (first_blue <: obj_addr) else start in
      fp' == fp \/ fp' = 0UL \/
      (U64.v fp' >= U64.v mword /\ U64.v fp' < heap_size /\
       U64.v fp' % U64.v mword == 0 /\
       Seq.mem (fp' <: obj_addr) (objects sync g'))))
    (decreases Seq.length objs)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1 --split_queries always"
let rec coalesce_aux_fp_in_walk g0 g start objs all_objs first_blue run_words fp =
  if Seq.length objs = 0 then begin
    assert (Seq.equal objs Seq.empty);
    coalesce_heap_empty g0 g first_blue run_words fp;
    flush_blue_snd_cases g first_blue run_words fp;
    let fp' = snd (flush_blue g first_blue run_words fp) in
    if fp' = fp then ()
    else begin
      if run_words > 0 then begin
        run_words_bound first_blue run_words start;
        flush_blue_fb_in_walk g first_blue run_words fp start
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

      let tail_white_inv (o: obj_addr)
        : Lemma (Seq.mem o (Seq.tail objs) /\ is_white o g0 ==>
                 read_word g (hd_address o) == read_word g0 (hd_address o))
        = mem_cons_lemma o obj (Seq.tail objs)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires tail_white_inv);

      coalesce_heap_blue_step g0 g objs first_blue run_words fp;

      assert (snd (coalesce_aux g0 g objs first_blue run_words fp) ==
              snd (coalesce_aux g0 g (Seq.tail objs) new_first (run_words + ws + 1) fp));

      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        assert (Seq.tail objs == objects next g0);
        coalesce_aux_fp_in_walk g0 g next (Seq.tail objs) all_objs
          new_first (run_words + ws + 1) fp
      end
      else begin
        // rest_start_nat >= heap_size, tail is empty
        objects_tail_empty_when_done start g0;
        assert (Seq.equal (Seq.tail objs) Seq.empty);
        let new_rw : pos = run_words + ws + 1 in
        coalesce_aux_empty g0 g new_first new_rw fp;
        flush_blue_snd_cases g new_first new_rw fp;
        let fp' = snd (flush_blue g new_first new_rw fp) in
        if fp' = fp then ()
        else begin
          assert (fp' == new_first);
          // Bound: new_rw - 1 < pow2 54
          hd_address_spec (new_first <: obj_addr);
          assert (rest_start_nat <= heap_size);
          let sync = hd_address (new_first <: obj_addr) in
          assert (U64.v sync + new_rw * U64.v mword == rest_start_nat);
          assert (new_rw * U64.v mword <= heap_size);
          assert (heap_size <= pow2 57);
          FStar.Math.Lemmas.lemma_div_le (new_rw * U64.v mword) (pow2 57) (U64.v mword);
          assert_norm (pow2 57 = pow2 54 * 8);
          FStar.Math.Lemmas.cancel_mul_div new_rw (U64.v mword);
          assert (new_rw - 1 < pow2 54);
          // new_first ∈ objects sync g'
          flush_blue_preserves_length g new_first new_rw fp;
          flush_blue_header_spec g (new_first <: obj_addr) new_rw fp;
          let wz_u64 : wosize = U64.uint_to_t (new_rw - 1) in
          makeHeader_getWosize wz_u64 Blue 0UL;
          f_address_spec sync;
          coalesce_heap_empty g0 g new_first new_rw fp;
          mem_cons_lemma (new_first <: obj_addr) (new_first <: obj_addr) Seq.empty
        end
      end
    end
    else begin
      // White: flush then continue
      mem_cons_lemma obj obj (Seq.tail objs);
      assert (Seq.mem obj all_objs);
      is_blue_iff obj g0; is_white_iff obj g0;
      assert (is_white obj g0);

      let (g_flush, fp_flush) = flush_blue g first_blue run_words fp in
      flush_blue_preserves_length g first_blue run_words fp;
      flush_blue_snd_cases g first_blue run_words fp;

      coalesce_heap_white_step g0 g objs first_blue run_words fp g_flush fp_flush;
      let g_result = coalesce_heap g0 g_flush (Seq.tail objs) 0UL 0 fp_flush in
      coalesce_heap_preserves_length g0 g_flush (Seq.tail objs) 0UL 0 fp_flush;

      let fp_outer = snd (coalesce_aux g0 g objs first_blue run_words fp) in
      let fp_inner = snd (coalesce_aux g0 g_flush (Seq.tail objs) 0UL 0 fp_flush) in
      assert (fp_outer == fp_inner);

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

        let flush_ge_next (addr: hp_addr)
          : Lemma (requires U64.v addr >= U64.v next)
                  (ensures read_word g_flush addr == read_word g0 addr)
          = flush_blue_preserves_outside g first_blue run_words fp addr
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires flush_ge_next);

        coalesce_aux_fp_in_walk g0 g_flush next (Seq.tail objs) all_objs 0UL 0 fp_flush;

        let fp_result = snd (coalesce_aux g0 g_flush (Seq.tail objs) 0UL 0 fp_flush) in

        if fp_result = 0UL then ()
        else if fp_result = fp_flush then begin
          if fp_flush = fp then ()
          else begin
            if run_words > 0 then begin
              run_words_bound first_blue run_words start;
              hd_address_spec (first_blue <: obj_addr);
              coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
                0UL 0 fp_flush (hd_address (first_blue <: obj_addr));
              flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
              merged_block_step g_result (first_blue <: obj_addr) run_words start (first_blue <: obj_addr);
              assert (Seq.mem (first_blue <: obj_addr)
                        (objects (hd_address (first_blue <: obj_addr)) g_result))
            end
            else ()
          end
        end
        else begin
          if run_words > 0 then begin
            run_words_bound first_blue run_words start;
            hd_address_spec (first_blue <: obj_addr);
            flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
            coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
              0UL 0 fp_flush (hd_address (first_blue <: obj_addr));
            white_addr_outside_all_blue g0 obj start;
            flush_blue_preserves_outside g first_blue run_words fp start;
            coalesce_heap_preserves_outside g0 g_flush next (Seq.tail objs)
              0UL 0 fp_flush all_objs start;
            objects_nonempty_at start g_result g0;
            objects_nonempty_next start g_result;
            mem_cons_lemma (fp_result <: obj_addr)
              (f_address start) (Seq.tail (objects start g_result));
            objects_later_subset start g_result (fp_result <: obj_addr);
            merged_block_step g_result (first_blue <: obj_addr)
              run_words start (fp_result <: obj_addr)
          end
          else begin
            white_addr_outside_all_blue g0 obj start;
            flush_blue_preserves_outside g first_blue run_words fp start;
            coalesce_heap_preserves_outside g0 g_flush next (Seq.tail objs)
              0UL 0 fp_flush all_objs start;
            objects_nonempty_at start g_result g0;
            objects_nonempty_next start g_result;
            objects_later_subset start g_result (fp_result <: obj_addr)
          end
        end
      end
      else begin
        // rest_start_nat >= heap_size, tail is empty
        objects_tail_empty_when_done start g0;
        assert (Seq.tail objs == Seq.empty);
        coalesce_heap_empty g0 g_flush 0UL 0 fp_flush;
        let fp_result = snd (coalesce_aux g0 g_flush (Seq.tail objs) 0UL 0 fp_flush) in
        assert (fp_result == fp_flush);
        if fp_flush = fp then ()
        else begin
          assert (fp_flush == first_blue);
          if run_words > 0 then begin
            run_words_bound first_blue run_words start;
            hd_address_spec (first_blue <: obj_addr);
            assert (U64.v (hd_address (first_blue <: obj_addr)) +
                      run_words * U64.v mword == U64.v start);
            assert (U64.v start < heap_size);
            flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
            let g_r = coalesce_heap g0 g_flush (Seq.tail objs) 0UL 0 fp_flush in
            assert (g_r == g_flush);
            flush_blue_fb_in_walk g first_blue run_words fp start;
            assert (Seq.mem (first_blue <: obj_addr)
                      (objects (hd_address (first_blue <: obj_addr)) g_r))
          end
        end
      end
    end
  end
#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let coalesce_fp_valid g =
  coalesce_aux_fp_in_walk g g 0UL (objects 0UL g) (objects 0UL g) 0UL 0 0UL;
  coalesce_heap_unfold g g (objects 0UL g) 0UL 0 0UL
#pop-options

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
    (decreases Seq.length objs)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1 --split_queries always"
let rec coalesce_aux_objects_subset g0 g start objs first_blue run_words fp all_objs y =
  if Seq.length objs = 0 then begin
    assert (Seq.equal objs Seq.empty);
    coalesce_heap_empty g0 g first_blue run_words fp;
    let g' = coalesce_heap g0 g objs first_blue run_words fp in
    if run_words > 0 then begin
      flush_blue_preserves_length g first_blue run_words fp;
      hd_address_spec (first_blue <: obj_addr);
      run_words_bound first_blue run_words start;
      flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
      let wz : wosize = U64.uint_to_t (run_words - 1) in
      merged_block_decompose g' (first_blue <: obj_addr) run_words start y;
      if y = (first_blue <: obj_addr) then
        // Blue base case: y = first_blue, have mem first_blue all_objs from precondition
        assert (Seq.mem (first_blue <: obj_addr) all_objs)
      else begin
        // y ≠ first_blue, from merged_block_decompose: y ∈ objects start g'
        // But objects start g' is empty (same header as g0 at start, objs=[])
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
        // Establish IH precondition: new_rw > 0 ==> mem (new_first <: obj_addr) all_objs
        // new_rw = run_words + ws + 1 > 0 always
        // If run_words = 0: new_first = obj, mem obj objs ==> mem obj all_objs
        // If run_words > 0: new_first = first_blue, already have it
        assert (Seq.mem (new_first <: obj_addr) all_objs);
        coalesce_aux_objects_subset g0 g next (Seq.tail objs)
          new_first new_rw fp all_objs y
      end
      else begin
        objects_tail_empty_when_done start g0;
        assert (Seq.equal (Seq.tail objs) Seq.empty);
        coalesce_heap_empty g0 g new_first new_rw fp;
        let g' = coalesce_heap g0 g objs first_blue run_words fp in
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
        FStar.Math.Lemmas.pow2_lt_compat 64 54;
        let wz_merged : wosize = U64.uint_to_t (new_rw - 1) in
        flush_blue_header_spec g (new_first <: obj_addr) new_rw fp;
        merged_block_decompose g' (new_first <: obj_addr) new_rw rest_u64 y;
        // From merged_block_decompose: y = new_first (rest_start >= heap_size
        // eliminates the other disjunct)
        // new_first is either obj (rw=0) or first_blue (rw>0), both in all_objs
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
      let g' = coalesce_heap g0 g objs first_blue run_words fp in
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
        assert (read_word g' start == read_word g0 start);

        // objects start g' is non-empty (same header as g0 at start)
        objects_nonempty_at start g' g0;
        objects_nonempty_next start g';
        Seq.cons_head_tail (objects start g');
        f_address_spec start;
        mem_cons_lemma y (f_address start) (Seq.tail (objects start g'));
        Seq.lemma_tl obj (objects next g');

        if run_words > 0 then begin
          // sync = hd_address first_blue
          hd_address_spec (first_blue <: obj_addr);
          run_words_bound first_blue run_words start;
          flush_blue_header_spec g (first_blue <: obj_addr) run_words fp;
          // Preserve merged header from g_flush to g'
          coalesce_heap_preserves_before_run_start g0 g_flush next (Seq.tail objs)
            0UL 0 fp_flush (hd_address (first_blue <: obj_addr));
          let wz_fb : wosize = U64.uint_to_t (run_words - 1) in
          merged_block_decompose g' (first_blue <: obj_addr) run_words start y;
          if y = (first_blue <: obj_addr) then
            // y = first_blue, have mem first_blue all_objs from precondition
            assert (Seq.mem (first_blue <: obj_addr) all_objs)
          else begin
            // y ∈ objects start g', decompose: y = obj or y ∈ objects next g'
            if y = obj then
              // obj is white in objs, mem obj all_objs
              assert (Seq.mem obj all_objs)
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
              coalesce_aux_objects_subset g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs y
            end
          end
        end
        else begin
          // run_words = 0, sync = start
          // y ∈ objects start g', decompose: y = obj or y ∈ objects next g'
          if y = obj then
            assert (Seq.mem obj all_objs)
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
            coalesce_aux_objects_subset g0 g_flush next (Seq.tail objs) 0UL 0 fp_flush all_objs y
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
          if y = (first_blue <: obj_addr) then
            // y = first_blue, have mem first_blue all_objs from precondition
            assert (Seq.mem (first_blue <: obj_addr) all_objs)
          else begin
            // y ∈ objects start g', but rest_start >= heap_size
            flush_blue_preserves_outside g first_blue run_words fp start;
            assert (read_word g' start == read_word g0 start);
            objects_nonempty_at start g' g0;
            objects_nonempty_next start g';
            mem_cons_lemma y (f_address start) (Seq.tail (objects start g'));
            // y = obj (rest is empty since rest_start >= heap_size)
            assert (y == obj);
            assert (Seq.mem obj all_objs)
          end
        end
        else begin
          // run_words = 0, sync = start, g' = g_flush = g
          objects_nonempty_at start g' g0;
          objects_nonempty_next start g';
          mem_cons_lemma y (f_address start) (Seq.tail (objects start g'));
          assert (y == obj);
          assert (Seq.mem obj all_objs)
        end
      end
    end
  end
#pop-options

val coalesce_objects_subset (g: heap) (y: obj_addr)
  : Lemma
    (requires post_sweep g /\ Seq.mem y (objects 0UL (fst (coalesce g))))
    (ensures Seq.mem y (objects 0UL g))

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let coalesce_objects_subset g y =
  coalesce_heap_unfold g g (objects 0UL g) 0UL 0 0UL;
  coalesce_aux_objects_subset g g 0UL (objects 0UL g) 0UL 0 0UL (objects 0UL g) y
#pop-options
