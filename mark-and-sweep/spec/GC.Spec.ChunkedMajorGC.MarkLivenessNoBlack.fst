module GC.Spec.ChunkedMajorGC.MarkLivenessNoBlack

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BColor = GC.Spec.ChunkedMarkBounded.ColorInvariant
module BEdge = GC.Spec.ChunkedMarkBounded.EdgeInvariant
module BNoBlack = GC.Spec.ChunkedMarkBounded.NoBlackToWhite
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph
module Reach = GC.Spec.ChunkedMajorGC.Reachability
module MarkLive = GC.Spec.ChunkedMajorGC.MarkLiveness

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

#push-options "--z3rlimit 10"
let chunked_major_reachable_from_roots_black_from_vertex_target_invariants
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
  =
  let p (x: obj_addr) : prop = SweepDefs.chunked_is_black mh x in
  let root_case (r: obj_addr)
    : Lemma
        (requires
          ChunkedMajorGraph.chunked_major_vertex mh r /\
          Seq.mem r roots)
        (ensures p r)
    =
    MarkLive.chunked_roots_black_elim mh roots r
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires root_case);
  let edge_case (y: obj_addr) (z: obj_addr)
    : Lemma
        (requires
          Reach.chunked_major_reachable_from_roots mh roots y /\
          p y /\
          ChunkedMajorGraph.chunked_major_vertex mh z /\
          ChunkedMajorGraph.chunked_major_edge mh y z)
        (ensures p z)
    =
    MarkLive.chunked_is_black_not_blue mh y;
    MarkLive.chunked_no_pointer_to_blue_elim mh y z;
    BNoBlack.chunked_no_black_to_white_vertex_targets_elim mh y z;
    MarkLive.chunked_no_gray_objects_elim mh z;
    MarkLive.chunked_not_white_gray_blue_implies_black mh z
  in
  let edge_case_forall (y: obj_addr) (z: obj_addr)
    : Lemma
        (Reach.chunked_major_reachable_from_roots mh roots y /\
         p y /\
         ChunkedMajorGraph.chunked_major_vertex mh z /\
         ChunkedMajorGraph.chunked_major_edge mh y z ==> p z)
    =
    FStar.Classical.move_requires (edge_case y) z
  in
  FStar.Classical.forall_intro_2 edge_case_forall;
  Reach.chunked_major_reachable_from_roots_induct mh roots p target
#pop-options

#push-options "--z3rlimit 10"
let chunked_mark_bounded_reachable_black_from_vertex_no_black
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
  =
  let mh_mark = BDefs.chunked_mark_bounded mh cap fuel in
  MarkLive.chunked_mark_bounded_roots_black mh roots cap fuel;
  MarkLive.chunked_mark_bounded_no_gray_objects mh cap fuel;
  BColor.chunked_mark_bounded_preserves_no_pointer_to_blue mh cap fuel;
  BNoBlack.chunked_mark_bounded_preserves_no_black_to_white mh cap fuel;
  BPres.chunked_mark_bounded_preserves_well_formed mh cap fuel;
  chunked_major_reachable_from_roots_black_from_vertex_target_invariants
    mh_mark roots target
#pop-options
