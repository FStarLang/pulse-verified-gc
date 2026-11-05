/// ---------------------------------------------------------------------------
/// GC.Gen.PostCollectionShape - the collector restores its own precondition
/// ---------------------------------------------------------------------------
///
/// `GC.Gen.HeapInvariant.collection_heap_shape` is what `gen_gc` demands of the
/// heap it is handed.  For that to be usable by a runtime driving repeated
/// collections, `gen_gc` must also *re-establish* it on the heap it returns.
///
/// The minor half of that is already available
/// (`GC.Gen.HeapInvariant.collection_heap_shape_after_minor_reset`: the nursery
/// is emptied, so every minor-side and cross-generation clause is vacuous), so
/// the whole obligation reduces to `major_heap_shape` of the major collector's
/// output.  This module proves exactly that.

module GC.Gen.PostCollectionShape

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Corr = GC.Spec.Correctness
module Sweep = GC.Spec.Sweep
module Coalesce = GC.Spec.Coalesce
module GenInv = GC.Gen.HeapInvariant
module FLs = GC.Spec.FreeLists
module CL = GC.Spec.CollectLists

/// **The major collector restores `major_heap_shape`.**
///
/// The heap `s2` and the free lists `fls` the collector hands back
/// (`GC.Impl.collect_with_roots`, described by `gc_coalesce_source_lists`)
/// satisfy the shape invariant again, from any mark output of any heap.
///
/// This is what makes the generational invariant *inductive* rather than merely
/// assumed: composed with `collection_heap_shape_after_minor_reset` it gives
/// `gen_gc` a postcondition that is literally its own precondition.
val major_gc_restores_major_heap_shape_of_source
  (h_init: heap) (s2: heap) (roots: seq obj_addr) (fls: FLs.fl_state)
  : Lemma
    (requires CL.gc_coalesce_source_lists h_init s2 roots fls)
    (ensures GenInv.major_heap_shape s2 fls)
