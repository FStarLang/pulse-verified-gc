module GC.Spec.ChunkedMarkBounded.Compat

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module Obj = GC.Spec.Object
module Fields = GC.Spec.Fields
module HeapGraph = GC.Spec.HeapGraph
module BMark = GC.Spec.MarkBounded
module MH = GC.Spec.MajorHeap
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module MarkDefs = GC.Spec.ChunkedMark.Defs

val chunked_is_gray_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (BDefs.chunked_is_gray (MH.single_chunk_major_heap g) obj ==
       Obj.is_gray obj g)

val push_children_bounded_single_chunk_ready
  (g: heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Tot prop

val chunked_push_children_bounded_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires push_children_bounded_single_chunk_ready g st obj i ws cap)
      (ensures
        BDefs.chunked_push_children_bounded
          (MH.single_chunk_major_heap g) st obj i ws cap ==
        (let (g', st') =
          BMark.push_children_bounded g st obj i ws cap in
         (MH.single_chunk_major_heap g', st')))

val chunked_mark_step_bounded_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        (if Seq.length st = 0 then True
         else
           let obj = Seq.head st in
           U64.v obj >= U64.v zero_addr + U64.v mword /\
           (if Obj.is_no_scan obj g then
              True
            else
              push_children_bounded_single_chunk_ready
                (Obj.makeBlack obj g)
                (Seq.tail st)
                obj
                1UL
                (Obj.wosize_of_object obj g)
                cap)))
      (ensures
        BDefs.chunked_mark_step_bounded
          (MH.single_chunk_major_heap g) st cap ==
        (let (g', st') = BMark.mark_step_bounded g st cap in
         (MH.single_chunk_major_heap g', st')))
