module GC.Spec.ChunkedMajorGC.MarkLiveness

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BComplete = GC.Spec.ChunkedMarkBounded.Completion
module BStackReady = GC.Spec.ChunkedMarkBounded.StackReady
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph

val chunked_roots_gray_or_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : prop

val chunked_roots_gray_or_black_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (root: obj_addr)
  : Lemma
      (requires
        chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGraph.chunked_major_vertex mh root /\
        Seq.mem root roots)
      (ensures
        BDefs.chunked_is_gray mh root \/
        SweepDefs.chunked_is_black mh root)

val chunked_roots_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : prop

val chunked_roots_black_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        forall (root: obj_addr).
          ChunkedMajorGraph.chunked_major_vertex mh root /\
          Seq.mem root roots ==>
          SweepDefs.chunked_is_black mh root)
      (ensures chunked_roots_black mh roots)

val chunked_roots_black_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (root: obj_addr)
  : Lemma
      (requires
        chunked_roots_black mh roots /\
        ChunkedMajorGraph.chunked_major_vertex mh root /\
        Seq.mem root roots)
      (ensures SweepDefs.chunked_is_black mh root)

val chunked_no_gray_objects
  (mh: MH.major_heap)
  : prop

val chunked_no_gray_objects_elim
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        chunked_no_gray_objects mh /\
        ChunkedMajorGraph.chunked_major_vertex mh obj)
      (ensures ~(BDefs.chunked_is_gray mh obj))

val chunked_mark_bounded_no_gray_objects
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        fuel >= BDefs.chunked_count_non_black mh)
      (ensures
        chunked_no_gray_objects
          (BDefs.chunked_mark_bounded mh cap fuel))

val chunked_no_pointer_to_blue
  (mh: MH.major_heap)
  : prop

val chunked_no_pointer_to_blue_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr).
          ChunkedMajorGraph.chunked_major_edge mh src dst /\
          ~(SweepDefs.chunked_is_blue mh src) ==>
          ~(SweepDefs.chunked_is_blue mh dst))
      (ensures chunked_no_pointer_to_blue mh)

val chunked_no_pointer_to_blue_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        chunked_no_pointer_to_blue mh /\
        ChunkedMajorGraph.chunked_major_edge mh src dst /\
        ~(SweepDefs.chunked_is_blue mh src))
      (ensures ~(SweepDefs.chunked_is_blue mh dst))

val chunked_no_black_to_white
  (mh: MH.major_heap)
  : prop

val chunked_no_black_to_white_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr).
          ChunkedMajorGraph.chunked_major_edge mh src dst /\
          SweepDefs.chunked_is_black mh src ==>
          ~(SweepDefs.chunked_is_white mh dst))
      (ensures chunked_no_black_to_white mh)

val chunked_no_black_to_white_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        chunked_no_black_to_white mh /\
        ChunkedMajorGraph.chunked_major_edge mh src dst /\
        SweepDefs.chunked_is_black mh src)
      (ensures ~(SweepDefs.chunked_is_white mh dst))

val chunked_is_black_not_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires SweepDefs.chunked_is_black mh obj)
      (ensures ~(SweepDefs.chunked_is_blue mh obj))

val chunked_not_white_gray_blue_implies_black
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMajorGraph.chunked_major_vertex mh obj /\
        ~(SweepDefs.chunked_is_white mh obj) /\
        ~(BDefs.chunked_is_gray mh obj) /\
        ~(SweepDefs.chunked_is_blue mh obj))
      (ensures SweepDefs.chunked_is_black mh obj)

val chunked_major_reachable_from_roots_black_from_invariants
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_roots_black mh roots /\
        chunked_no_gray_objects mh /\
        chunked_no_pointer_to_blue mh /\
        chunked_no_black_to_white mh /\
        ChunkedMajorGraph.chunked_major_vertex mh target /\
        GC.Spec.ChunkedMajorGC.Reachability.chunked_major_reachable_from_roots
          mh roots target)
      (ensures SweepDefs.chunked_is_black mh target)

val chunked_mark_bounded_root_ready
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  (root: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGraph.chunked_major_vertex mh root /\
        Seq.mem root roots)
      (ensures
        BPres.chunked_mark_bounded_marks_target_ready
          mh cap fuel root)

val chunked_mark_bounded_roots_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        chunked_roots_gray_or_black mh roots)
      (ensures
        chunked_roots_black
          (BDefs.chunked_mark_bounded mh cap fuel) roots)
