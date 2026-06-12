module GC.Spec.ChunkedMarkBounded.LoopCompat

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module Obj = GC.Spec.Object
module Fields = GC.Spec.Fields
module BMark = GC.Spec.MarkBounded
module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BCompat = GC.Spec.ChunkedMarkBounded.Compat

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let rec object_list_ready
    (objs: Seq.seq obj_addr)
  : Tot prop
    (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then True
  else
    U64.v (Seq.head objs) >= U64.v zero_addr + U64.v mword /\
    object_list_ready (Seq.tail objs)

let rec chunked_count_non_black_in_single_chunk_compat
    (g: heap)
    (objs: Seq.seq obj_addr)
  : Lemma
      (requires object_list_ready objs)
      (ensures
        BDefs.chunked_count_non_black_in
          (MH.single_chunk_major_heap g) objs ==
        BMark.count_non_black_in g objs)
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then
    BDefs.chunked_count_non_black_in_empty (MH.single_chunk_major_heap g) objs
  else begin
    let obj = Seq.head objs in
    BDefs.chunked_count_non_black_in_step
      (MH.single_chunk_major_heap g) objs;
    SweepDefs.chunked_is_black_single_chunk_compat g obj;
    assert (object_list_ready (Seq.tail objs));
    chunked_count_non_black_in_single_chunk_compat g (Seq.tail objs)
  end

let chunked_count_non_black_single_chunk_compat
    (g: heap)
  : Lemma
      (requires object_list_ready (Fields.objects zero_addr g))
      (ensures
        BDefs.chunked_count_non_black (MH.single_chunk_major_heap g) ==
        BMark.count_non_black g)
  =
  BDefs.chunked_count_non_black_equation (MH.single_chunk_major_heap g);
  MH.single_chunk_major_objects_compat g;
  chunked_count_non_black_in_single_chunk_compat
    g (Fields.objects zero_addr g)

let rec chunked_rescan_objects_single_chunk_compat
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
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then
    BDefs.chunked_rescan_objects_empty
      (MH.single_chunk_major_heap g) objs st cap
  else begin
    let obj = Seq.head objs in
    BDefs.chunked_rescan_objects_step
      (MH.single_chunk_major_heap g) objs st cap;
    BCompat.chunked_is_gray_single_chunk_compat g obj;
    let st' =
      if Obj.is_gray obj g && not (Seq.mem obj st) &&
         Seq.length st < cap then
        Seq.cons obj st
      else
        st
    in
    assert (object_list_ready (Seq.tail objs));
    chunked_rescan_objects_single_chunk_compat
      g (Seq.tail objs) st' cap
  end

let chunked_rescan_heap_single_chunk_compat
    (g: heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires object_list_ready (Fields.objects zero_addr g))
      (ensures
        BDefs.chunked_rescan_heap
          (MH.single_chunk_major_heap g) st cap ==
        BMark.rescan_heap g (Fields.objects zero_addr g) st cap)
  =
  BDefs.chunked_rescan_heap_equation
    (MH.single_chunk_major_heap g) st cap;
  MH.single_chunk_major_objects_compat g;
  chunked_rescan_objects_single_chunk_compat
    g (Fields.objects zero_addr g) st cap

let mark_step_bounded_single_chunk_ready
    (g: heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Tot prop
  =
  if Seq.length st = 0 then True
  else
    let obj = Seq.head st in
    U64.v obj >= U64.v zero_addr + U64.v mword /\
    (if Obj.is_no_scan obj g then
       True
     else
       BCompat.push_children_bounded_single_chunk_ready
         (Obj.makeBlack obj g)
         (Seq.tail st)
         obj
         1UL
         (Obj.wosize_of_object obj g)
         cap)

let rec mark_inner_loop_single_chunk_ready
    (g: heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Tot prop
    (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then True
  else
    mark_step_bounded_single_chunk_ready g st cap /\
    (let (g', st') = BMark.mark_step_bounded g st cap in
     mark_inner_loop_single_chunk_ready g' st' cap (fuel - 1))

let rec chunked_mark_inner_loop_single_chunk_compat
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
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    BDefs.chunked_mark_inner_loop_base
      (MH.single_chunk_major_heap g) st cap fuel
  else begin
    assert (fuel > 0);
    let (g', st') = BMark.mark_step_bounded g st cap in
    BCompat.chunked_mark_step_bounded_single_chunk_compat g st cap;
    BDefs.chunked_mark_inner_loop_step
      (MH.single_chunk_major_heap g) st cap fuel;
    assert (BDefs.chunked_mark_step_bounded
      (MH.single_chunk_major_heap g) st cap ==
      (MH.single_chunk_major_heap g', st'));
    assert (mark_inner_loop_single_chunk_ready g' st' cap (fuel - 1));
    chunked_mark_inner_loop_single_chunk_compat g' st' cap (fuel - 1)
  end
