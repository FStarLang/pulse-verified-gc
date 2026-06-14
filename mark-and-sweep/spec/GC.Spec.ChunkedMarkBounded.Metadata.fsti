module GC.Spec.ChunkedMarkBounded.Metadata

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module RangePres = GC.Spec.ChunkedSweepCoalesce.RangePreservation
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady

val chunked_push_children_bounded_preserves_wosize_of_object
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         SweepDefs.chunked_wosize_of_object mh' target ==
         SweepDefs.chunked_wosize_of_object mh target))

val chunked_push_children_bounded_preserves_get_field
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  (target: obj_addr)
  (j: U64.t{U64.v j >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v j <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
      (ensures
        (let (mh', _) =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         MarkDefs.chunked_get_field mh' target j ==
         MarkDefs.chunked_get_field mh target j))

val chunked_push_children_bounded_preserves_no_scan_status
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) =
         BDefs.chunked_push_children_bounded mh st obj i ws cap in
         MarkDefs.chunked_is_no_scan mh' target ==
         MarkDefs.chunked_is_no_scan mh target))

val chunked_push_children_bounded_preserves_ranges
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (ensures
        (let (mh', _) =
         BDefs.chunked_push_children_bounded mh st obj i ws cap in
         RangePres.same_chunk_ranges mh mh'))

val chunked_mark_step_bounded_preserves_wosize_of_object
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         SweepDefs.chunked_wosize_of_object mh' target ==
         SweepDefs.chunked_wosize_of_object mh target))

val chunked_mark_step_bounded_preserves_get_field
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  (j: U64.t{U64.v j >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v j <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         MarkDefs.chunked_get_field mh' target j ==
         MarkDefs.chunked_get_field mh target j))

val chunked_mark_step_bounded_preserves_no_scan_status
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         MarkDefs.chunked_is_no_scan mh' target ==
         MarkDefs.chunked_is_no_scan mh target))

val chunked_mark_step_bounded_preserves_ranges
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         RangePres.same_chunk_ranges mh mh'))

val chunked_mark_inner_loop_preserves_wosize_of_object
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        BReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap fuel in
         SweepDefs.chunked_wosize_of_object mh' target ==
         SweepDefs.chunked_wosize_of_object mh target))

val chunked_mark_inner_loop_preserves_get_field
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  (j: U64.t{U64.v j >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        BReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v j <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap fuel in
         MarkDefs.chunked_get_field mh' target j ==
         MarkDefs.chunked_get_field mh target j))

val chunked_mark_inner_loop_preserves_no_scan_status
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        BReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap fuel in
         MarkDefs.chunked_is_no_scan mh' target ==
         MarkDefs.chunked_is_no_scan mh target))

val chunked_mark_inner_loop_preserves_ranges
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (ensures
        (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap fuel in
         RangePres.same_chunk_ranges mh mh'))

val chunked_mark_bounded_preserves_wosize_of_object
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        SweepDefs.chunked_wosize_of_object
          (BDefs.chunked_mark_bounded mh cap fuel) target ==
        SweepDefs.chunked_wosize_of_object mh target)

val chunked_mark_bounded_preserves_get_field
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  (j: U64.t{U64.v j >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v j <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
      (ensures
        MarkDefs.chunked_get_field
          (BDefs.chunked_mark_bounded mh cap fuel) target j ==
        MarkDefs.chunked_get_field mh target j)

val chunked_mark_bounded_preserves_no_scan_status
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        MarkDefs.chunked_is_no_scan
          (BDefs.chunked_mark_bounded mh cap fuel) target ==
        MarkDefs.chunked_is_no_scan mh target)

val chunked_mark_bounded_preserves_ranges
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (ensures
        RangePres.same_chunk_ranges mh
          (BDefs.chunked_mark_bounded mh cap fuel))
