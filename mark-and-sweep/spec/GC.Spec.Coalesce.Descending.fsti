/// ---------------------------------------------------------------------------
/// GC.Spec.Coalesce.Descending - the coalescer rebuilds a downhill free list
/// ---------------------------------------------------------------------------
///
/// `GC.Spec.Coalesce.coalesce` does not thread the sweep's free list through:
/// it starts from a null head (`coalesce_aux g g (objects zero_addr g) 0UL 0 0UL`)
/// and rebuilds the list from scratch, pushing each merged block onto the front
/// as the walk passes it.  Since the walk runs upwards through the heap, every
/// link written points back at a block the walk has already left behind, so the
/// resulting list is *descending* in the sense of
/// `GC.Spec.FreeList.Descending.fl_desc_chain`.
///
/// That is the whole content of this module.  Combined with
/// `fl_desc_chain_gives_valid` it discharges the allocator's `fl_valid` and
/// `fl_chain_terminates` entry conditions for the collector's output, which are
/// the two hardest conjuncts of `GC.Gen.HeapInvariant.major_heap_shape`.

module GC.Spec.Coalesce.Descending

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Coalesce

module U64 = FStar.UInt64
module FLD = GC.Spec.FreeList.Descending
module AllocLemmas = GC.Spec.Allocator.Lemmas

/// The lowest address the pending blue run occupies, or the walk position when
/// there is no pending run.  Everything the free list has been built out of so
/// far lies strictly below this, which is what makes the chain invariant
/// frameable across the rest of the walk.
let run_floor (run_end: nat) (first_blue: U64.t) (run_words: nat) : nat =
  if run_words > 0 && U64.v first_blue >= U64.v mword
  then U64.v first_blue - U64.v mword
  else run_end

/// Geometric side condition of the walk: a pending run is in bounds and ends
/// exactly at the current walk position.  This is the fragment of
/// `GC.Spec.Coalesce.walk_pre` that the descending argument needs.
let run_geometry (run_end: nat) (first_blue: U64.t) (run_words: nat) : prop =
  run_words > 0 ==>
    (U64.v first_blue >= U64.v mword /\
     U64.v first_blue < heap_size /\
     U64.v first_blue % U64.v mword == 0 /\
     U64.v first_blue - U64.v mword + run_words * U64.v mword == run_end)

/// **Flushing a run keeps the free list descending.**
///
/// Either nothing is flushed, in which case the list is untouched and only its
/// bound has to be relaxed from the run floor up to the walk position; or a
/// merged block is pushed onto the front, in which case the block sits at the
/// run floor, above every existing cell, and its link word is the old head.
val flush_blue_desc
  (g: heap) (run_end: nat) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      run_end <= heap_size /\
      run_geometry run_end first_blue run_words /\
      FLD.fl_desc_chain g fp (run_floor run_end first_blue run_words))
    (ensures (let r = flush_blue g first_blue run_words fp in
              Seq.length (fst r) == heap_size /\
              FLD.fl_desc_chain (fst r) (snd r) run_end))

/// **The walk keeps the free list descending.**
val coalesce_aux_desc
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      objs == objects start g0 /\
      Seq.length g0 == heap_size /\
      Seq.length g == heap_size /\
      run_geometry (U64.v start) first_blue run_words /\
      FLD.fl_desc_chain g fp (run_floor (U64.v start) first_blue run_words))
    (ensures (let r = coalesce_aux g0 g objs first_blue run_words fp in
              FLD.fl_desc_chain (fst r) (snd r) heap_size))
    (decreases Seq.length objs)

/// **The coalescer's output free list runs downhill.**
val coalesce_desc (g: heap)
  : Lemma (ensures (let r = coalesce g in
                    FLD.fl_desc_chain (fst r) (snd r) heap_size))

/// **The allocator's entry conditions hold for the coalescer's output.**
///
/// This is the payoff: `fl_valid` and `fl_chain_terminates` -- the two
/// conjuncts of `GC.Gen.HeapInvariant.major_heap_shape` that talk about the
/// free list -- follow from the descending property plus the fact that every
/// link the coalescer writes points at a heap object.
val coalesce_fl_entry (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures (let r = coalesce g in
              AllocLemmas.fl_valid (fst r) (snd r) heap_words /\
              AllocLemmas.fl_chain_terminates (fst r) (snd r) heap_words))
