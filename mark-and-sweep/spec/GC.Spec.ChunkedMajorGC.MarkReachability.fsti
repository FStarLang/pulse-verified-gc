module GC.Spec.ChunkedMajorGC.MarkReachability

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs
module MarkPres = GC.Spec.ChunkedMark.Preservation
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph
module Reach = GC.Spec.ChunkedMajorGC.Reachability

val chunked_stack_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  : prop

val chunked_stack_reachable_from_roots_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        (forall (obj: obj_addr).
          Seq.mem obj st ==>
          Reach.chunked_major_reachable_from_roots mh roots obj))
      (ensures chunked_stack_reachable_from_roots mh roots st)

val chunked_stack_reachable_from_roots_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        chunked_stack_reachable_from_roots mh roots st /\
        Seq.mem obj st)
      (ensures Reach.chunked_major_reachable_from_roots mh roots obj)

val chunked_stack_reachable_from_roots_empty
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (ensures
        chunked_stack_reachable_from_roots mh roots Seq.empty)

val chunked_stack_reachable_from_roots_cons
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Reach.chunked_major_reachable_from_roots mh roots obj /\
        chunked_stack_reachable_from_roots mh roots st)
      (ensures
        chunked_stack_reachable_from_roots mh roots (Seq.cons obj st))

val chunked_stack_reachable_from_roots_tail
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        chunked_stack_reachable_from_roots mh roots st)
      (ensures
        chunked_stack_reachable_from_roots mh roots (Seq.tail st))

val chunked_stack_reachable_from_gray_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Reach.chunked_gray_black_reachable mh roots /\
        MarkPres.stack_objects_in_major mh st /\
        BReady.chunked_stack_points_to_gray mh st)
      (ensures chunked_stack_reachable_from_roots mh roots st)

val chunked_rescan_objects_stack_reachable_from_gray_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (objs: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        Reach.chunked_gray_black_reachable mh roots /\
        MarkPres.stack_objects_in_major mh st /\
        BReady.chunked_stack_points_to_gray mh st /\
        (forall (obj: obj_addr).
          Seq.mem obj objs ==> Seq.mem obj (MH.major_objects mh)))
      (ensures
        chunked_stack_reachable_from_roots mh roots
          (BDefs.chunked_rescan_objects mh objs st cap))

val chunked_rescan_heap_stack_reachable_from_gray_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires Reach.chunked_gray_black_reachable mh roots)
      (ensures
        chunked_stack_reachable_from_roots mh roots
          (BDefs.chunked_rescan_heap mh Seq.empty cap))

val chunked_resolved_pointer_field_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        Reach.chunked_major_reachable_from_roots mh roots obj /\
        U64.v i <=
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
            mh obj) /\
        (let v = MarkDefs.chunked_get_field mh obj i in
         MarkDefs.chunked_is_pointer_field mh v /\
         (let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
          let child = MarkDefs.chunked_resolve_object mh child_raw in
          child == child_raw /\
          ChunkedMajorGraph.chunked_major_vertex mh child)))
      (ensures
        (let v = MarkDefs.chunked_get_field mh obj i in
         let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
         let child = MarkDefs.chunked_resolve_object mh child_raw in
         Reach.chunked_major_reachable_from_roots mh roots child))

val chunked_non_infix_pointer_field_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        Reach.chunked_major_reachable_from_roots mh roots obj /\
        U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) /\
        (let v = MarkDefs.chunked_get_field mh obj i in
         MarkDefs.chunked_is_pointer_field mh v /\
         (let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
          ~(SweepDefs.chunked_is_infix mh child_raw) /\
          ChunkedMajorGraph.chunked_major_vertex mh child_raw)))
      (ensures
        (let v = MarkDefs.chunked_get_field mh obj i in
         let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
         let child = MarkDefs.chunked_resolve_object mh child_raw in
         Reach.chunked_major_reachable_from_roots mh roots child))

val chunked_push_children_bounded_reachability_ready
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : GTot prop

val chunked_push_children_bounded_reachability_ready_child
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        U64.v i <= U64.v ws /\
        chunked_push_children_bounded_reachability_ready mh obj i ws /\
        (let v = MarkDefs.chunked_get_field mh obj i in
         MarkDefs.chunked_is_pointer_field mh v /\
         (let child_raw =
            MarkDefs.chunked_pointer_field_as_obj_addr mh v in
          let child = MarkDefs.chunked_resolve_object mh child_raw in
          SweepDefs.chunked_is_white mh child)))
      (ensures
        (let v = MarkDefs.chunked_get_field mh obj i in
         let child_raw =
           MarkDefs.chunked_pointer_field_as_obj_addr mh v in
         ~(SweepDefs.chunked_is_infix mh child_raw) /\
         ChunkedMajorGraph.chunked_major_vertex mh child_raw))

val chunked_push_children_bounded_reachability_ready_next
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        U64.v i <= U64.v ws /\
        U64.v i < U64.v ws /\
        chunked_push_children_bounded_reachability_ready mh obj i ws)
      (ensures
        (let v = MarkDefs.chunked_get_field mh obj i in
         let mh' =
           if MarkDefs.chunked_is_pointer_field mh v then
             let child_raw =
               MarkDefs.chunked_pointer_field_as_obj_addr mh v in
             let child =
               MarkDefs.chunked_resolve_object mh child_raw in
             if SweepDefs.chunked_is_white mh child then
               MarkDefs.chunked_make_gray mh child
             else
               mh
           else
             mh in
         chunked_push_children_bounded_reachability_ready
           mh' obj (U64.add i 1UL) ws))

val chunked_make_gray_preserves_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Reach.chunked_major_reachable_from_roots mh roots target)
      (ensures
        Reach.chunked_major_reachable_from_roots
          (MarkDefs.chunked_make_gray mh obj) roots target)

val chunked_make_gray_preserves_stack_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        chunked_stack_reachable_from_roots mh roots st)
      (ensures
        chunked_stack_reachable_from_roots
          (MarkDefs.chunked_make_gray mh obj) roots st)

val chunked_make_black_preserves_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Reach.chunked_major_reachable_from_roots mh roots target)
      (ensures
        Reach.chunked_major_reachable_from_roots
          (MarkDefs.chunked_make_black mh obj) roots target)

val chunked_make_black_preserves_stack_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        chunked_stack_reachable_from_roots mh roots st)
      (ensures
        chunked_stack_reachable_from_roots
          (MarkDefs.chunked_make_black mh obj) roots st)

val chunked_make_gray_preserves_gray_black_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Reach.chunked_major_reachable_from_roots mh roots obj /\
        Reach.chunked_gray_black_reachable mh roots)
      (ensures
        Reach.chunked_gray_black_reachable
          (MarkDefs.chunked_make_gray mh obj) roots)

val chunked_make_black_preserves_gray_black_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Reach.chunked_major_reachable_from_roots mh roots obj /\
        Reach.chunked_gray_black_reachable mh roots)
      (ensures
        Reach.chunked_gray_black_reachable
          (MarkDefs.chunked_make_black mh obj) roots)

val chunked_push_children_bounded_preserves_stack_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        chunked_push_children_bounded_reachability_ready mh obj i ws /\
        ws == SweepDefs.chunked_wosize_of_object mh obj /\
        Reach.chunked_major_reachable_from_roots mh roots obj /\
        chunked_stack_reachable_from_roots mh roots st)
      (ensures
        (let (mh', st') =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         chunked_stack_reachable_from_roots mh' roots st'))

val chunked_mark_step_bounded_reachability_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : GTot prop

val chunked_mark_step_bounded_preserves_stack_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        chunked_mark_step_bounded_reachability_ready mh st cap /\
        chunked_stack_reachable_from_roots mh roots st)
      (ensures
        (let (mh', st') =
          BDefs.chunked_mark_step_bounded mh st cap in
         chunked_stack_reachable_from_roots mh' roots st'))

val chunked_mark_inner_loop_reachability_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : GTot prop

val chunked_mark_inner_loop_preserves_stack_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        chunked_mark_inner_loop_reachability_ready mh st cap fuel /\
        chunked_stack_reachable_from_roots mh roots st)
      (ensures
        (let (mh', st') =
          BDefs.chunked_mark_inner_loop mh st cap fuel in
         chunked_stack_reachable_from_roots mh' roots st'))
