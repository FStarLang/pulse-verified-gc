module GC.Spec.ChunkedMarkBounded.LoopCompat

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module BMark = GC.Spec.MarkBounded
module Fields = GC.Spec.Fields
module MH = GC.Spec.MajorHeap
module BDefs = GC.Spec.ChunkedMarkBounded.Defs

val object_list_ready
  (objs: Seq.seq obj_addr)
  : Tot prop

val chunked_count_non_black_in_single_chunk_compat
  (g: heap)
  (objs: Seq.seq obj_addr)
  : Lemma
      (requires object_list_ready objs)
      (ensures
        BDefs.chunked_count_non_black_in
          (MH.single_chunk_major_heap g) objs ==
        BMark.count_non_black_in g objs)

val chunked_count_non_black_single_chunk_compat
  (g: heap)
  : Lemma
      (requires object_list_ready (Fields.objects zero_addr g))
      (ensures
        BDefs.chunked_count_non_black (MH.single_chunk_major_heap g) ==
        BMark.count_non_black g)

val chunked_rescan_objects_single_chunk_compat
  (g: heap)
  (objs: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires object_list_ready objs)
      (ensures
        BDefs.chunked_rescan_objects
          (MH.single_chunk_major_heap g) objs st cap ==
        BMark.rescan_heap g objs st cap)

val chunked_rescan_heap_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires object_list_ready (Fields.objects zero_addr g))
      (ensures
        BDefs.chunked_rescan_heap
          (MH.single_chunk_major_heap g) st cap ==
        BMark.rescan_heap g (Fields.objects zero_addr g) st cap)

val mark_inner_loop_single_chunk_ready
  (g: heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Tot prop

val chunked_mark_inner_loop_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires mark_inner_loop_single_chunk_ready g st cap fuel)
      (ensures
        BDefs.chunked_mark_inner_loop
          (MH.single_chunk_major_heap g) st cap fuel ==
        (let (g', st') = BMark.mark_inner_loop g st cap fuel in
         (MH.single_chunk_major_heap g', st')))
