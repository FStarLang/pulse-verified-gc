(*
   Pure F* bridge lemmas for the fused sweep+coalesce implementation.
   Bridges between spec-level fused_aux definitions and the imperative loop.
   Follows the pattern from GC.Impl.Coalesce.Lemmas but for fused_aux.
*)

module GC.Impl.FusedSweepCoalesce.Lemmas

open FStar.Seq
open FStar.Mul
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
module Defs = GC.Spec.SweepCoalesce.Defs
module SpecCoalesce = GC.Spec.Coalesce
module Alloc = GC.Spec.Allocator
module HeapGraph = GC.Spec.HeapGraph
module Header = GC.Lib.Header
module SI = GC.Spec.SweepInv

/// ---------------------------------------------------------------------------
/// Unfold fused_sweep_coalesce
/// ---------------------------------------------------------------------------

/// The initial call to fused_sweep_coalesce matches fused_aux with initial state
val fused_unfold (g: heap)
  : Lemma
    (requires Seq.length g == heap_size)
    (ensures Defs.fused_sweep_coalesce g ==
             Defs.fused_aux g g (objects 0UL g) 0UL 0 0UL)

/// ---------------------------------------------------------------------------
/// is_black reading from current heap via suffix preservation
/// ---------------------------------------------------------------------------

/// When the suffix of g agrees with g0 at start, is_black/wosize are equivalent
val is_black_from_original
  (g0 g: heap) (obj: obj_addr) (start: hp_addr)
  : Lemma
    (requires
      Seq.length g0 == heap_size /\
      Seq.length g == heap_size /\
      U64.v start + U64.v mword < heap_size /\
      (forall (addr: hp_addr). U64.v addr >= U64.v start ==>
        read_word g addr == read_word g0 addr) /\
      obj == f_address start)
    (ensures
      is_black obj g == is_black obj g0 /\
      is_white obj g == is_white obj g0 /\
      is_blue obj g == is_blue obj g0 /\
      getWosize (read_word g start) == getWosize (read_word g0 start))

/// ---------------------------------------------------------------------------
/// makeWhite suffix preservation
/// ---------------------------------------------------------------------------

/// makeWhite only writes at hd_address obj; suffix past hd_address obj + 8 is preserved
val makeWhite_suffix_preserved
  (g: heap) (obj: obj_addr) (bound: nat)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v (hd_address obj) + U64.v mword <= bound)
    (ensures
      forall (addr: hp_addr). U64.v addr >= bound ==>
        read_word (makeWhite obj g) addr == read_word g addr)

/// makeWhite preserves heap length
val makeWhite_length (g: heap) (obj: obj_addr)
  : Lemma
    (requires Seq.length g == heap_size)
    (ensures Seq.length (makeWhite obj g) == heap_size)

/// ---------------------------------------------------------------------------
/// Whiten bridge for fused loop
/// ---------------------------------------------------------------------------

/// Bridge: write_word g' (hd_address obj) (makeHeader wz white tag) == makeWhite obj g'
/// when the header at hd_address obj in g' equals that in g0, and obj is black in g0.
/// Requires g0 well-formed (for valid_header64 proof).
val whiten_from_original
  (g0 g': heap) (obj: obj_addr)
  : Lemma
    (requires
      Seq.length g0 == heap_size /\
      Seq.length g' == heap_size /\
      is_black obj g0 /\
      read_word g' (hd_address obj) == read_word g0 (hd_address obj) /\
      well_formed_heap g0 /\
      Seq.mem obj (objects 0UL g0))
    (ensures
      (let h_addr = hd_address obj in
       let hdr = read_word g' h_addr in
       let new_hdr = GC.Impl.Object.makeHeader (getWosize hdr) Header.White (getTag hdr) in
       write_word g' h_addr new_hdr == makeWhite obj g'))

/// ---------------------------------------------------------------------------
/// Nonblack step: accumulate into blue run (no heap writes)
/// ---------------------------------------------------------------------------

/// For the non-black case: unfold fused_aux one step and establish
/// all invariant facts for the next iteration.
val nonblack_step_fused_aux_eq
  (g0 g: heap) (start: hp_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      U64.v start + U64.v mword < heap_size /\
      Seq.length (objects start g0) > 0 /\
      ~(is_black (f_address start) g0) /\
      Seq.length g0 == heap_size /\
      Defs.fused_aux g0 g (objects start g0) first_blue run_words fp ==
        Defs.fused_sweep_coalesce g0 /\
      (run_words > 0 ==>
        U64.v first_blue >= U64.v mword /\
        U64.v first_blue < heap_size /\
        U64.v first_blue % U64.v mword == 0 /\
        U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start))
    (ensures (
      let wz = getWosize (read_word g0 start) in
      let ws = U64.v wz in
      let obj = f_address start in
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      let new_rw = run_words + ws + 1 in
      let next_nat = U64.v start + (ws + 1) * U64.v mword in
      next_nat <= heap_size /\
      next_nat % U64.v mword = 0 /\
      next_nat + U64.v mword < pow2 64 /\
      new_rw > 0 /\
      new_rw < pow2 54 /\
      U64.v new_first >= U64.v mword /\
      U64.v new_first < heap_size /\
      U64.v new_first % U64.v mword == 0 /\
      U64.v new_first - U64.v mword + new_rw * U64.v mword == next_nat /\
      (next_nat < heap_size /\ next_nat % U64.v mword = 0 ==>
        Defs.fused_aux g0 g (objects (U64.uint_to_t next_nat) g0)
          new_first new_rw fp == Defs.fused_sweep_coalesce g0) /\
      (next_nat >= heap_size ==>
        Defs.fused_aux g0 g Seq.empty
          new_first new_rw fp == Defs.fused_sweep_coalesce g0)))

/// ---------------------------------------------------------------------------
/// Black step: flush pending run + makeWhite
/// ---------------------------------------------------------------------------

/// For the black case: unfold fused_aux one step, flush the blue run,
/// then apply makeWhite. Establishes invariant for next iteration.
val black_step_fused_aux_eq
  (g0 g: heap) (start: hp_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      U64.v start + U64.v mword < heap_size /\
      Seq.length (objects start g0) > 0 /\
      is_black (f_address start) g0 /\
      Seq.length g0 == heap_size /\
      Seq.length g == heap_size /\
      Defs.fused_aux g0 g (objects start g0) first_blue run_words fp ==
        Defs.fused_sweep_coalesce g0 /\
      (run_words > 0 ==>
        run_words < pow2 54 /\
        U64.v first_blue >= U64.v mword /\
        U64.v first_blue < heap_size /\
        U64.v first_blue % U64.v mword == 0 /\
        U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start) /\
      (forall (addr: hp_addr). U64.v addr >= U64.v start ==>
        read_word g addr == read_word g0 addr))
    (ensures (
      let wz = getWosize (read_word g0 start) in
      let ws = U64.v wz in
      let obj = f_address start in
      let (g', fp') = SpecCoalesce.flush_blue g first_blue run_words fp in
      let g'' = makeWhite obj g' in
      let next_nat = U64.v start + (ws + 1) * U64.v mword in
      Seq.length g' == heap_size /\
      Seq.length g'' == heap_size /\
      next_nat <= heap_size /\
      next_nat % U64.v mword = 0 /\
      next_nat + U64.v mword < pow2 64 /\
      // Suffix: g'' agrees with g0 past next_nat
      (forall (addr: hp_addr). U64.v addr >= next_nat ==>
        read_word g'' addr == read_word g0 addr) /\
      // Spec: fused_aux from next step == fused_sweep_coalesce g0
      (next_nat < heap_size /\ next_nat % U64.v mword = 0 ==>
        Defs.fused_aux g0 g'' (objects (U64.uint_to_t next_nat) g0)
          0UL 0 fp' == Defs.fused_sweep_coalesce g0) /\
      (next_nat >= heap_size ==>
        Defs.fused_aux g0 g'' Seq.empty
          0UL 0 fp' == Defs.fused_sweep_coalesce g0)))

/// ---------------------------------------------------------------------------
/// Reexport from GC.Impl.Coalesce.Lemmas
/// ---------------------------------------------------------------------------

/// These are used by both coalesce and fused loops; we re-export the signatures
/// so callers only need to open one Lemmas module.

/// flush_blue preserves heap length
val flush_blue_length
  (g: heap) (fb: U64.t) (rw: nat) (fp: U64.t)
  : Lemma (Seq.length (fst (SpecCoalesce.flush_blue g fb rw fp)) == Seq.length g)

/// Empty case: flush final run
val fused_step_empty
  (g0 g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (Defs.fused_aux g0 g Seq.empty first_blue run_words fp ==
     SpecCoalesce.flush_blue g first_blue run_words fp)
