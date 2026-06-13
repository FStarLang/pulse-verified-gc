module GC.Spec.ChunkedMajorGC.Defs

open GC.Spec.Base
open GC.Spec.Heap

module U64 = FStar.UInt64
module MH = GC.Spec.MajorHeap
module BMark = GC.Spec.MarkBounded
module DenseFused = GC.Spec.SweepCoalesce.Defs
module ChunkedMark = GC.Spec.ChunkedMarkBounded.Defs
module ChunkedMarkOuter = GC.Spec.ChunkedMarkBounded.OuterCompat
module ChunkedSweep = GC.Spec.ChunkedSweepCoalesce.Defs

val chunked_major_gc_bounded
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : GTot (MH.major_heap & U64.t)

val chunked_major_gc_bounded_equation:
  mh:MH.major_heap ->
  cap:nat{cap > 0} ->
  fuel:nat ->
  Lemma
    (chunked_major_gc_bounded mh cap fuel ==
     ChunkedSweep.chunked_fused_sweep_coalesce
       (ChunkedMark.chunked_mark_bounded mh cap fuel))

val chunked_major_gc_bounded_single_chunk_compat
  (g: heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        ChunkedMarkOuter.mark_bounded_single_chunk_ready g cap fuel)
      (ensures
        chunked_major_gc_bounded
          (MH.single_chunk_major_heap g) cap fuel ==
        (let h_mark = BMark.mark_bounded g cap fuel in
         let (h_final, fp_final) =
           DenseFused.fused_sweep_coalesce h_mark in
         (MH.single_chunk_major_heap h_final, fp_final)))

