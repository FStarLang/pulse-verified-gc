/// ---------------------------------------------------------------------------
/// GC.Spec.Coalesce.Shape - structural facts about the coalescer's output
/// ---------------------------------------------------------------------------
///
/// `GC.Gen.HeapInvariant.major_heap_shape` is the invariant the generational
/// collector carries about the major heap between collections.  Most of its
/// conjuncts had no proof connecting them to the mark-and-sweep collector's
/// output, so the invariant could not be shown to be re-established by a major
/// collection.  This module supplies them, stated in raw form (mark-and-sweep
/// cannot mention the generational predicates that package them).
///
/// The free-list conjuncts -- `fl_valid` and `fl_chain_terminates` -- live in
/// `GC.Spec.Coalesce.Descending` instead, since they need the descending-chain
/// argument rather than the walk lemmas used here.

module GC.Spec.Coalesce.Shape

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Coalesce

module U64 = FStar.UInt64
module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module AllocChain = GC.Spec.Allocator.Lemmas.Chain
module FLD = GC.Spec.FreeList.Descending
module CD = GC.Spec.Coalesce.Descending

/// A blue object of the coalesced walk was blue before the coalesce too.
///
/// Coalescing only ever merges blue runs, and it leaves survivors' headers
/// alone, so a block that is blue afterwards cannot have been a survivor.
val coalesce_blue_transfer (g: heap) (y: obj_addr)
  : Lemma
    (requires post_sweep g /\
              Seq.mem y (objects zero_addr (fst (coalesce g))) /\
              is_blue y (fst (coalesce g)))
    (ensures Seq.mem y (objects zero_addr g) /\ is_blue y g)

/// A non-blue object of the coalesced walk is an untouched survivor.
val coalesce_survivor_transfer (g: heap) (y: obj_addr)
  : Lemma
    (requires post_sweep g /\
              Seq.mem y (objects zero_addr (fst (coalesce g))) /\
              ~(is_blue y (fst (coalesce g))))
    (ensures Seq.mem y (objects zero_addr g) /\ is_white y g /\
             read_word (fst (coalesce g)) (hd_address y) == read_word g (hd_address y))

/// **`chain_objects_blue`**: no live object sits on the free list.
///
/// Immediate from the descending property, every cell of which is blue.
val coalesce_chain_objects_blue (g: heap) (obj: obj_addr)
  : Lemma
    (requires post_sweep g /\ ~(is_blue obj (fst (coalesce g))))
    (ensures (let r = coalesce g in
              AllocChain.chain_avoids (fst r) (snd r) obj heap_words = true))

/// **`blue_link_fields_valid`**: a free block's link word is null or a pointer.
val coalesce_blue_link_fields_valid (g: heap) (src: obj_addr)
  : Lemma
    (requires post_sweep g /\
              Seq.mem src (objects zero_addr (fst (coalesce g))) /\
              is_blue src (fst (coalesce g)) /\
              U64.v (wosize_of_object src (fst (coalesce g))) >= 1 /\
              U64.v (hd_address src) + 16 <= heap_size)
    (ensures (let v = read_word (fst (coalesce g)) src in
              v = 0UL \/ HeapGraph.is_pointer_field v))

/// **`fp_pointer_or_zero`**: the free-list head is null or a pointer.
val coalesce_fp_pointer_or_zero (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures (let r = coalesce g in
              snd r = 0UL \/ HeapGraph.is_pointer_field (snd r)))

/// **`no_pointer_to_blue`**: nothing live points into the free list.
///
/// `post_sweep_strong` says exactly this of the input heap, for survivors.
/// Coalescing preserves both a survivor's fields and how they resolve, and it
/// only turns already-blue blocks into (bigger) blue blocks, so no new pointer
/// into the free list can appear.
val coalesce_no_pointer_to_blue (g: heap)
  : Lemma
    (requires post_sweep_strong g /\ well_formed_heap g)
    (ensures Mark.no_pointer_to_blue (fst (coalesce g)))
