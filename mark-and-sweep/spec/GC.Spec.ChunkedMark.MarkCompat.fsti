module GC.Spec.ChunkedMark.MarkCompat

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module Obj = GC.Spec.Object
module Mark = GC.Spec.Mark
module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs

val mark_step_single_chunk_ready
  (g: heap)
  (st: Seq.seq obj_addr)
  : Tot prop

val mark_aux_single_chunk_ready
  (g: heap)
  (st: Seq.seq obj_addr)
  (fuel: nat)
  : Tot prop

val chunked_mark_step_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires mark_step_single_chunk_ready g st)
      (ensures
        MarkDefs.chunked_mark_step (MH.single_chunk_major_heap g) st ==
        (let (g', st') = Mark.mark_step g st in
         (MH.single_chunk_major_heap g', st')))

val chunked_mark_aux_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (fuel: nat)
  : Lemma
      (requires mark_aux_single_chunk_ready g st fuel)
      (ensures
        MarkDefs.chunked_mark_aux (MH.single_chunk_major_heap g) st fuel ==
        MH.single_chunk_major_heap (Mark.mark_aux g st fuel))

val chunked_mark_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        mark_aux_single_chunk_ready
          g st (heap_size / U64.v mword))
      (ensures
        MarkDefs.chunked_mark (MH.single_chunk_major_heap g) st ==
        MH.single_chunk_major_heap (Mark.mark g st))
