module GC.Spec.ChunkedMarkBounded.ColorInvariant

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph

val chunked_push_children_bounded_no_new_blue
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
        ~(SweepDefs.chunked_is_blue mh target))
      (ensures
        (let (mh', _) =
           BDefs.chunked_push_children_bounded mh st obj i ws cap in
         ~(SweepDefs.chunked_is_blue mh' target)))

val chunked_mark_step_bounded_no_new_blue
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        ~(SweepDefs.chunked_is_blue mh target))
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_step_bounded mh st cap in
         ~(SweepDefs.chunked_is_blue mh' target)))

val chunked_mark_inner_loop_no_new_blue
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
        ~(SweepDefs.chunked_is_blue mh target))
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_inner_loop mh st cap fuel in
         ~(SweepDefs.chunked_is_blue mh' target)))

val chunked_mark_bounded_no_new_blue
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        ~(SweepDefs.chunked_is_blue mh target))
      (ensures
        ~(SweepDefs.chunked_is_blue
          (BDefs.chunked_mark_bounded mh cap fuel) target))

val chunked_push_children_bounded_no_new_white
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
        ~(SweepDefs.chunked_is_white mh target))
      (ensures
        (let (mh', _) =
           BDefs.chunked_push_children_bounded mh st obj i ws cap in
         ~(SweepDefs.chunked_is_white mh' target)))

val chunked_mark_step_bounded_no_new_white
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        ~(SweepDefs.chunked_is_white mh target))
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_step_bounded mh st cap in
         ~(SweepDefs.chunked_is_white mh' target)))

val chunked_mark_inner_loop_no_new_white
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
        ~(SweepDefs.chunked_is_white mh target))
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_inner_loop mh st cap fuel in
         ~(SweepDefs.chunked_is_white mh' target)))

val chunked_mark_bounded_no_new_white
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        ~(SweepDefs.chunked_is_white mh target))
      (ensures
        ~(SweepDefs.chunked_is_white
          (BDefs.chunked_mark_bounded mh cap fuel) target))

val chunked_push_children_bounded_preserves_blue
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
        SweepDefs.chunked_is_blue mh target)
      (ensures
        (let (mh', _) =
           BDefs.chunked_push_children_bounded mh st obj i ws cap in
         SweepDefs.chunked_is_blue mh' target))

val chunked_mark_step_bounded_preserves_blue
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        SweepDefs.chunked_is_blue mh target)
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_step_bounded mh st cap in
         SweepDefs.chunked_is_blue mh' target))

val chunked_mark_inner_loop_preserves_blue
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
        SweepDefs.chunked_is_blue mh target)
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_inner_loop mh st cap fuel in
         SweepDefs.chunked_is_blue mh' target))

val chunked_mark_bounded_preserves_blue
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        SweepDefs.chunked_is_blue mh target)
      (ensures
        SweepDefs.chunked_is_blue
          (BDefs.chunked_mark_bounded mh cap fuel) target)

val chunked_mark_bounded_field_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        ChunkedMajorGraph.chunked_major_vertex mh obj)
      (ensures
        ChunkedMajorGraph.chunked_major_field_preserved
          mh (BDefs.chunked_mark_bounded mh cap fuel) obj)

val chunked_mark_bounded_pointer_classification_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel)
      (ensures
        ChunkedMajorGraph.chunked_major_pointer_classification_preserved
          mh (BDefs.chunked_mark_bounded mh cap fuel))

val chunked_mark_bounded_preserves_no_pointer_to_blue
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        GC.Spec.ChunkedMajorGC.MarkLiveness.chunked_no_pointer_to_blue mh)
      (ensures
        GC.Spec.ChunkedMajorGC.MarkLiveness.chunked_no_pointer_to_blue
          (BDefs.chunked_mark_bounded mh cap fuel))
