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

/// **The major collector restores `major_heap_shape`.**
///
/// Given a heap satisfying the shape invariant and any mark output for it, the
/// heap and free pointer produced by `coalesce (sweep ...)` -- which is what
/// `GC.Impl.FusedSweepCoalesce.fused_sweep_coalesce` computes -- satisfy the
/// shape invariant again.
///
/// This is what makes the generational invariant *inductive* rather than merely
/// assumed: composed with `collection_heap_shape_after_minor_reset` it gives
/// `gen_gc` a postcondition that is literally its own precondition.
val major_gc_restores_major_heap_shape
  (major: heap) (h_mark: heap) (roots: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires Corr.mark_post major h_mark roots fp)
    (ensures (let r = Coalesce.coalesce (fst (Sweep.sweep h_mark fp)) in
              GenInv.major_heap_shape (fst r) (snd r)))

/// The same statement against the collector's Pulse postcondition.
///
/// `GC.Impl.collect_with_roots` does not expose the marked heap -- it exposes
/// `Corr.gc_coalesce_source`, which says only that *some* marked heap produced
/// the result.  This lemma discharges that existential so callers of the Pulse
/// entry point can use the theorem directly.
val major_gc_restores_major_heap_shape_of_source
  (h_init: heap) (s2: heap) (roots: seq obj_addr) (fp: U64.t) (final_fp: U64.t)
  : Lemma
    (requires Corr.gc_coalesce_source h_init s2 roots fp final_fp)
    (ensures GenInv.major_heap_shape s2 final_fp)
