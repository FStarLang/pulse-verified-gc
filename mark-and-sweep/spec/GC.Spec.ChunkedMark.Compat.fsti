module GC.Spec.ChunkedMark.Compat

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

val chunked_get_field_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (MarkDefs.chunked_get_field (MH.single_chunk_major_heap g) obj i ==
       HeapGraph.get_field g obj i)

val chunked_is_pointer_field_single_chunk_compat
  (g: heap)
  (v: U64.t)
  : Lemma
      (MarkDefs.chunked_is_pointer_field (MH.single_chunk_major_heap g) v ==
       HeapGraph.is_pointer_field v)

val chunked_make_gray_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (MarkDefs.chunked_make_gray (MH.single_chunk_major_heap g) obj ==
       MH.single_chunk_major_heap (Obj.makeGray obj g))

val chunked_make_black_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (MarkDefs.chunked_make_black (MH.single_chunk_major_heap g) obj ==
       MH.single_chunk_major_heap (Obj.makeBlack obj g))

val chunked_is_no_scan_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (MarkDefs.chunked_is_no_scan (MH.single_chunk_major_heap g) obj ==
       Obj.is_no_scan obj g)

val chunked_parent_closure_addr_nat_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (MarkDefs.chunked_parent_closure_addr_nat
        obj (MH.single_chunk_major_heap g) ==
       Obj.parent_closure_addr_nat obj g)

val chunked_resolve_object_single_chunk_compat
  (g: heap)
  (addr: obj_addr{U64.v addr >= U64.v zero_addr + U64.v mword})
  : Lemma
      (requires
        Obj.is_infix addr g ==>
        (let p = Obj.parent_closure_addr_nat addr g in
         p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
         Fields.is_pointer (U64.uint_to_t p)))
      (ensures
        MarkDefs.chunked_resolve_object (MH.single_chunk_major_heap g) addr ==
        Obj.resolve_object addr g)

val chunked_mark_step_empty_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st = 0)
      (ensures
        MarkDefs.chunked_mark_step (MH.single_chunk_major_heap g) st ==
        (let (g', st') = Mark.mark_step g st in
         (MH.single_chunk_major_heap g', st')))

val chunked_mark_step_no_scan_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st > 0 /\
                U64.v (Seq.head st) >= U64.v zero_addr + U64.v mword /\
                Obj.is_no_scan (Seq.head st) g)
      (ensures
        MarkDefs.chunked_mark_step (MH.single_chunk_major_heap g) st ==
        (let (g', st') = Mark.mark_step g st in
         (MH.single_chunk_major_heap g', st')))

val chunked_mark_aux_empty_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (fuel: nat)
  : Lemma
      (requires Seq.length st = 0)
      (ensures
        MarkDefs.chunked_mark_aux (MH.single_chunk_major_heap g) st fuel ==
        MH.single_chunk_major_heap (Mark.mark_aux g st fuel))

val chunked_mark_aux_out_of_fuel_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (ensures
        MarkDefs.chunked_mark_aux (MH.single_chunk_major_heap g) st 0 ==
        MH.single_chunk_major_heap (Mark.mark_aux g st 0))
