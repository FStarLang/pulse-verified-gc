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
open FStar.Mul

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
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
        let wz_u64 : (x:U64.t{U64.v x < pow2 54}) = U64.uint_to_t wz in
        let hdr = Alloc.make_header wz_u64 Alloc.blue_bits 0UL in
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
/// first_blue: obj_addr of first blue in current run (unused when run_words=0)
/// run_words: total words accumulated in current blue run (0 = no pending run)
/// fp: free list pointer being threaded through

let rec coalesce_aux (g: heap) (objs: seq obj_addr)
    (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : GTot (heap & U64.t) (decreases Seq.length objs)
  = if Seq.length objs = 0 then
      flush_blue g first_blue run_words fp
    else
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      if is_blue obj g then
        let ws = U64.v (wosize_of_object obj g) in
        let new_first : U64.t = if run_words = 0 then obj else first_blue in
        coalesce_aux g rest new_first (run_words + ws + 1) fp
      else begin
        // White object: flush pending blue run, then continue
        let (g', fp') = flush_blue g first_blue run_words fp in
        coalesce_aux g' rest 0UL 0 fp'
      end

/// Top-level coalesce: walk all objects, build fresh free list.
let coalesce (g: heap) : GTot (heap & U64.t) =
  coalesce_aux g (objects 0UL g) 0UL 0 0UL

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
      let wz_u64 : (x:U64.t{U64.v x < pow2 54}) = U64.uint_to_t wz in
      let hdr = Alloc.make_header wz_u64 Alloc.blue_bits 0UL in
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
      let wz_u64 : (x:U64.t{U64.v x < pow2 54}) = U64.uint_to_t wz in
      let hdr = Alloc.make_header wz_u64 Alloc.blue_bits 0UL in
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
/// Coalesce preserves survivor data
/// ---------------------------------------------------------------------------

/// Helper: coalesce_aux preserves reads at white objects' positions
val coalesce_aux_preserves_outside
  (g: heap) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (addr: hp_addr)
  : Lemma
    (requires
      post_sweep g /\
      (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects 0UL g)) /\
      // addr is in a white object region (not in any blue run)
      (exists (x: obj_addr).
        Seq.mem x (objects 0UL g) /\ is_white x g /\
        U64.v addr >= U64.v (hd_address x) /\
        U64.v addr < U64.v (hd_address x) +
          (U64.v (wosize_of_object x g) + 1) * U64.v mword))
    (ensures read_word (fst (coalesce_aux g objs first_blue run_words fp)) addr
          == read_word g addr)
    (decreases Seq.length objs)

let coalesce_aux_preserves_outside g objs first_blue run_words fp addr =
  admit ()

/// Coalesce preserves survivor headers
val coalesce_preserves_survivor_header (g: heap) (x: obj_addr)
  : Lemma
    (requires post_sweep g /\ Seq.mem x (objects 0UL g) /\ is_white x g)
    (ensures read_word (fst (coalesce g)) (hd_address x)
          == read_word g (hd_address x))

let coalesce_preserves_survivor_header g x =
  admit ()

/// Coalesce preserves survivor fields
val coalesce_preserves_survivor_field
  (g: heap) (x: obj_addr) (i: U64.t{U64.v i >= 1})
  : Lemma
    (requires post_sweep g /\
             Seq.mem x (objects 0UL g) /\ is_white x g /\
             U64.v i <= U64.v (wosize_of_object x g))
    (ensures HeapGraph.get_field (fst (coalesce g)) x i
          == HeapGraph.get_field g x i)

let coalesce_preserves_survivor_field g x i =
  admit ()

/// ---------------------------------------------------------------------------
/// Well-formedness of coalesced heap
/// ---------------------------------------------------------------------------

val coalesce_preserves_wf (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures well_formed_heap (fst (coalesce g)))

let coalesce_preserves_wf g = admit ()

/// ---------------------------------------------------------------------------
/// Color postcondition
/// ---------------------------------------------------------------------------

val coalesce_all_white_or_blue (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures (forall (x: obj_addr).
               Seq.mem x (objects 0UL (fst (coalesce g))) ==>
               is_white x (fst (coalesce g)) \/ is_blue x (fst (coalesce g))))

let coalesce_all_white_or_blue g = admit ()

/// ---------------------------------------------------------------------------
/// Survivors appear in coalesced objects
/// ---------------------------------------------------------------------------

val coalesce_survivors_in_objects (g: heap) (x: obj_addr)
  : Lemma
    (requires post_sweep g /\ Seq.mem x (objects 0UL g) /\ is_white x g)
    (ensures Seq.mem x (objects 0UL (fst (coalesce g))))

let coalesce_survivors_in_objects g x = admit ()

/// ---------------------------------------------------------------------------
/// Free list validity
/// ---------------------------------------------------------------------------

/// The coalesce result's free pointer is null or in the new objects set
val coalesce_fp_valid (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures (let (g', fp') = coalesce g in
             fp' = 0UL \/
             (U64.v fp' >= U64.v mword /\
              U64.v fp' < heap_size /\
              U64.v fp' % U64.v mword == 0 /\
              Seq.mem (fp' <: obj_addr) (objects 0UL g'))))

let coalesce_fp_valid g = admit ()

/// ---------------------------------------------------------------------------
/// Heap length preservation
/// ---------------------------------------------------------------------------

/// Heap length preservation
/// ---------------------------------------------------------------------------

let rec coalesce_aux_preserves_length
  (g: heap) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma (ensures Seq.length (fst (coalesce_aux g objs first_blue run_words fp)) == Seq.length g)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then
      flush_blue_preserves_length g first_blue run_words fp
    else
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      if is_blue obj g then
        let ws = U64.v (wosize_of_object obj g) in
        let new_first : U64.t = if run_words = 0 then obj else first_blue in
        coalesce_aux_preserves_length g rest new_first (run_words + ws + 1) fp
      else begin
        let (g', fp') = flush_blue g first_blue run_words fp in
        flush_blue_preserves_length g first_blue run_words fp;
        coalesce_aux_preserves_length g' rest 0UL 0 fp'
      end

val coalesce_preserves_length (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures Seq.length (fst (coalesce g)) == Seq.length g)

let coalesce_preserves_length g =
  coalesce_aux_preserves_length g (objects 0UL g) 0UL 0 0UL
