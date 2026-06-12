module GC.Spec.ChunkedMark.PushCompat

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module Obj = GC.Spec.Object
module Fields = GC.Spec.Fields
module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs

val pointer_field_as_obj_addr:
  v:U64.t{HeapGraph.is_pointer_field v} ->
  GTot obj_addr

val push_children_single_chunk_ready
  (g: heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Tot prop

val chunked_push_children_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires push_children_single_chunk_ready g obj i ws)
      (ensures
        MarkDefs.chunked_push_children
          (MH.single_chunk_major_heap g) st obj i ws ==
        (let (g', st') = Mark.push_children g st obj i ws in
         (MH.single_chunk_major_heap g', st')))

val chunked_mark_step_scan_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        U64.v (Seq.head st) >= U64.v zero_addr + U64.v mword /\
        ~(Obj.is_no_scan (Seq.head st) g) /\
        push_children_single_chunk_ready
          (Obj.makeBlack (Seq.head st) g)
          (Seq.head st)
          1UL
          (Obj.wosize_of_object (Seq.head st) g))
      (ensures
        MarkDefs.chunked_mark_step (MH.single_chunk_major_heap g) st ==
        (let (g', st') = Mark.mark_step g st in
         (MH.single_chunk_major_heap g', st')))
