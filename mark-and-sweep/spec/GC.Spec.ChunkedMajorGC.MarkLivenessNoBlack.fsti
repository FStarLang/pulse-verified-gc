module GC.Spec.ChunkedMajorGC.MarkLivenessNoBlack

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BEdge = GC.Spec.ChunkedMarkBounded.EdgeInvariant
module BNoBlack = GC.Spec.ChunkedMarkBounded.NoBlackToWhite
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph
module Reach = GC.Spec.ChunkedMajorGC.Reachability
module MarkLive = GC.Spec.ChunkedMajorGC.MarkLiveness

val chunked_major_reachable_from_roots_black_from_vertex_target_invariants
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        MarkLive.chunked_roots_black mh roots /\
        MarkLive.chunked_no_gray_objects mh /\
        MarkLive.chunked_no_pointer_to_blue mh /\
        BNoBlack.chunked_no_black_to_white_vertex_targets mh /\
        ChunkedMajorGraph.chunked_major_vertex mh target /\
        Reach.chunked_major_reachable_from_roots mh roots target)
      (ensures SweepDefs.chunked_is_black mh target)

val chunked_major_reachable_from_roots_black_from_all_vertex_target_invariants
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        MarkLive.chunked_roots_black mh roots /\
        MarkLive.chunked_no_gray_objects mh /\
        MarkLive.chunked_no_pointer_to_blue_vertex_targets mh /\
        BNoBlack.chunked_no_black_to_white_vertex_targets mh /\
        ChunkedMajorGraph.chunked_major_vertex mh target /\
        Reach.chunked_major_reachable_from_roots mh roots target)
      (ensures SweepDefs.chunked_is_black mh target)

val chunked_mark_bounded_reachable_black_from_vertex_no_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        fuel >= BDefs.chunked_count_non_black mh /\
        MarkLive.chunked_roots_gray_or_black mh roots /\
        MarkLive.chunked_no_pointer_to_blue mh /\
        BNoBlack.chunked_no_black_to_white_vertex_targets mh /\
        BEdge.chunked_vertex_edge_targets_non_infix mh /\
        (let mh_mark = BDefs.chunked_mark_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_vertex mh_mark target /\
         Reach.chunked_major_reachable_from_roots mh_mark roots target))
      (ensures
        SweepDefs.chunked_is_black
          (BDefs.chunked_mark_bounded mh cap fuel) target)
