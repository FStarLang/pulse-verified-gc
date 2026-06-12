module GC.Spec.ChunkedMarkBounded.OuterCompat

module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module BMark = GC.Spec.MarkBounded
module Fields = GC.Spec.Fields
module MH = GC.Spec.MajorHeap
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BLoop = GC.Spec.ChunkedMarkBounded.LoopCompat

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let rec mark_bounded_single_chunk_ready
    (g: heap)
    (cap: nat)
    (fuel: nat)
  : Tot prop
    (decreases fuel)
  =
  if fuel = 0 then True
  else
    BLoop.object_list_ready (Fields.objects zero_addr g) /\
    (let st = BMark.rescan_heap g (Fields.objects zero_addr g) Seq.empty cap in
     if Seq.length st = 0 then True
     else
       let inner_fuel = BMark.count_non_black g in
       let (g', st') = BMark.mark_inner_loop g st cap inner_fuel in
       BLoop.mark_inner_loop_single_chunk_ready g st cap inner_fuel /\
       mark_bounded_single_chunk_ready g' cap (fuel - 1))

let rec chunked_mark_bounded_single_chunk_compat
    (g: heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires mark_bounded_single_chunk_ready g cap fuel)
      (ensures
        BDefs.chunked_mark_bounded
          (MH.single_chunk_major_heap g) cap fuel ==
        MH.single_chunk_major_heap (BMark.mark_bounded g cap fuel))
      (decreases fuel)
  =
  if fuel = 0 then
    BDefs.chunked_mark_bounded_base
      (MH.single_chunk_major_heap g) cap
  else begin
    assert (fuel > 0);
    let st = BMark.rescan_heap g (Fields.objects zero_addr g) Seq.empty cap in
    BLoop.chunked_rescan_heap_single_chunk_compat g Seq.empty cap;
    BLoop.chunked_count_non_black_single_chunk_compat g;
    BDefs.chunked_mark_bounded_step
      (MH.single_chunk_major_heap g) cap fuel;
    assert (BDefs.chunked_rescan_heap
      (MH.single_chunk_major_heap g) Seq.empty cap == st);
    if Seq.length st = 0 then
      ()
    else begin
      let inner_fuel = BMark.count_non_black g in
      let (g', st') = BMark.mark_inner_loop g st cap inner_fuel in
      BLoop.chunked_mark_inner_loop_single_chunk_compat
        g st cap inner_fuel;
      assert (BDefs.chunked_count_non_black
        (MH.single_chunk_major_heap g) == inner_fuel);
      assert (BDefs.chunked_mark_inner_loop
        (MH.single_chunk_major_heap g) st cap inner_fuel ==
        (MH.single_chunk_major_heap g', st'));
      assert (mark_bounded_single_chunk_ready g' cap (fuel - 1));
      chunked_mark_bounded_single_chunk_compat g' cap (fuel - 1)
    end
  end
