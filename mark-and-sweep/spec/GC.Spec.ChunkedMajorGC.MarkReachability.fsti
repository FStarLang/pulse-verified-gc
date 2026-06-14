module GC.Spec.ChunkedMajorGC.MarkReachability

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs
module MarkPres = GC.Spec.ChunkedMark.Preservation
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady
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
