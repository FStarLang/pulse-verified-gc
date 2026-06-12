module GC.Spec.ChunkedMarkBounded.OuterCompat

module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module BMark = GC.Spec.MarkBounded
module Fields = GC.Spec.Fields
module MH = GC.Spec.MajorHeap
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BLoop = GC.Spec.ChunkedMarkBounded.LoopCompat

val mark_bounded_single_chunk_ready
  (g: heap)
  (cap: nat)
  (fuel: nat)
  : Tot prop

val chunked_mark_bounded_single_chunk_compat
  (g: heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires mark_bounded_single_chunk_ready g cap fuel)
      (ensures
        BDefs.chunked_mark_bounded
          (MH.single_chunk_major_heap g) cap fuel ==
        MH.single_chunk_major_heap (BMark.mark_bounded g cap fuel))
