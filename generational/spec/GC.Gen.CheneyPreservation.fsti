/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation — Additional Cheney BFS preservation lemmas
/// ---------------------------------------------------------------------------
///
/// The stop-the-world collection's shape facts, for the Pulse implementation:
/// where a non-free block of the result comes from, and the preserved
/// `collection_heap_shape`.  The per-family facts about a Cheney run are in
/// `GC.Gen.CheneyPreservation.{Forwarding,Frame,Injectivity,NonBlueOrigin,Fields}`
/// and `GC.Gen.Cheney.Steps`.

module GC.Gen.CheneyPreservation

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module GenInv = GC.Gen.HeapInvariant
module FreeListShape = GC.Gen.FreeListShape
module CE = GC.Gen.CheneyGeneric

/// **A block of a stop-the-world collection's result** is, if not blue, an
/// old non-blue block with the same header, or a promoted copy -- which the
/// idle allocator wrote white.  Promotion allocates from the free list and
/// writes only the new blocks; the pointer update writes no header.  So the
/// collection creates no grey or black block.
val cheney_collect_block_origin
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires CE.promote_pre minor major fp)
          (ensures (let g' = (cheney_collect_spec minor major fp roots).mc_major in
                    in_use free_stw g' x ==>
                    (in_use free_stw major x /\
                     read_word g' (hd_address x) == read_word major (hd_address x)) \/
                    is_white x g'))

/// **The stop-the-world collection keeps the stop-the-world shape.**  The
/// `free_stw` instance of `GC.Gen.CheneyGeneric.cheney_collect_with_preserves_shape`,
/// plus the two colour facts (no black, no gray objects) that
/// `collection_heap_shape` adds to the shape at `free_stw`
/// (`cheney_collect_block_origin`).
val cheney_collect_preserves_collection_heap_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires GenInv.collection_heap_shape minor major fp)
          (ensures GenInv.collection_heap_shape
            (cheney_collect_spec minor major fp roots).mc_minor
            (cheney_collect_spec minor major fp roots).mc_major
            (cheney_collect_spec minor major fp roots).mc_fp)

/// One of its conjuncts, for callers that want only this one.
val cheney_collect_preserves_wfh_from_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures well_formed_heap
      (cheney_collect_spec minor major fp roots).mc_major)
