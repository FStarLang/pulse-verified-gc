module GC.Spec.ChunkedMark.MarkCompat

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module Obj = GC.Spec.Object
module Mark = GC.Spec.Mark
module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkDefs = GC.Spec.ChunkedMark.Defs
module MarkPrimCompat = GC.Spec.ChunkedMark.Compat
module PushCompat = GC.Spec.ChunkedMark.PushCompat

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let mark_step_single_chunk_ready
    (g: heap)
    (st: Seq.seq obj_addr)
  : Tot prop
  =
  if Seq.length st = 0 then True
  else
    let obj = Seq.head st in
    U64.v obj >= U64.v zero_addr + U64.v mword /\
    (if Obj.is_no_scan obj g then
       True
     else
       PushCompat.push_children_single_chunk_ready
         (Obj.makeBlack obj g)
         obj
         1UL
         (Obj.wosize_of_object obj g))

let rec mark_aux_single_chunk_ready
    (g: heap)
    (st: Seq.seq obj_addr)
    (fuel: nat)
  : Tot prop
    (decreases fuel)
  =
  if Seq.length st = 0 then True
  else if fuel = 0 then True
  else
    mark_step_single_chunk_ready g st /\
    (let (g', st') = Mark.mark_step g st in
     mark_aux_single_chunk_ready g' st' (fuel - 1))

let chunked_mark_step_single_chunk_compat
    (g: heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires mark_step_single_chunk_ready g st)
      (ensures
        MarkDefs.chunked_mark_step (MH.single_chunk_major_heap g) st ==
        (let (g', st') = Mark.mark_step g st in
         (MH.single_chunk_major_heap g', st')))
  =
  if Seq.length st = 0 then
    MarkPrimCompat.chunked_mark_step_empty_single_chunk_compat g st
  else begin
    let obj = Seq.head st in
    if Obj.is_no_scan obj g then
      MarkPrimCompat.chunked_mark_step_no_scan_single_chunk_compat g st
    else
      PushCompat.chunked_mark_step_scan_single_chunk_compat g st
  end

let rec chunked_mark_aux_single_chunk_compat
    (g: heap)
    (st: Seq.seq obj_addr)
    (fuel: nat)
  : Lemma
      (requires mark_aux_single_chunk_ready g st fuel)
      (ensures
        MarkDefs.chunked_mark_aux (MH.single_chunk_major_heap g) st fuel ==
        MH.single_chunk_major_heap (Mark.mark_aux g st fuel))
      (decreases fuel)
  =
  if Seq.length st = 0 then
    MarkPrimCompat.chunked_mark_aux_empty_single_chunk_compat g st fuel
  else if fuel = 0 then
    MarkPrimCompat.chunked_mark_aux_out_of_fuel_single_chunk_compat g st
  else begin
    assert (fuel > 0);
    let (g', st') = Mark.mark_step g st in
    chunked_mark_step_single_chunk_compat g st;
    MarkDefs.chunked_mark_aux_step
      (MH.single_chunk_major_heap g) st fuel;
    assert (MarkDefs.chunked_mark_step
      (MH.single_chunk_major_heap g) st ==
      (MH.single_chunk_major_heap g', st'));
    assert (mark_aux_single_chunk_ready g' st' (fuel - 1));
    chunked_mark_aux_single_chunk_compat g' st' (fuel - 1)
  end

let chunked_mark_single_chunk_compat
    (g: heap)
    (st: Seq.seq obj_addr)
  : Lemma
      (requires
        mark_aux_single_chunk_ready
          g st (heap_size / U64.v mword))
      (ensures
        MarkDefs.chunked_mark (MH.single_chunk_major_heap g) st ==
        MH.single_chunk_major_heap (Mark.mark g st))
  =
  MarkDefs.chunked_mark_equation (MH.single_chunk_major_heap g) st;
  chunked_mark_aux_single_chunk_compat g st (heap_size / U64.v mword)
