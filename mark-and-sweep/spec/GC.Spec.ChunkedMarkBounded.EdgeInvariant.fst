module GC.Spec.ChunkedMarkBounded.EdgeInvariant

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BColor = GC.Spec.ChunkedMarkBounded.ColorInvariant
module BMetadata = GC.Spec.ChunkedMarkBounded.Metadata
module BTag = GC.Spec.ChunkedMarkBounded.TagInvariant
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let chunked_vertex_edge_targets_non_infix
  (mh: MH.major_heap)
  : prop
  =
  forall (src dst: obj_addr).
    ChunkedMajorGraph.chunked_major_edge mh src dst ==>
    ChunkedMajorGraph.chunked_major_vertex mh dst ==>
    ~(SweepDefs.chunked_is_infix mh dst)

#push-options "--z3rlimit 1 --fuel 0 --ifuel 0"
let chunked_vertex_edge_targets_non_infix_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr).
          ChunkedMajorGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGraph.chunked_major_vertex mh dst ==>
          ~(SweepDefs.chunked_is_infix mh dst))
      (ensures chunked_vertex_edge_targets_non_infix mh)
  =
  let one (src dst: obj_addr)
    : Lemma
        (requires
          ChunkedMajorGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGraph.chunked_major_vertex mh dst)
        (ensures ~(SweepDefs.chunked_is_infix mh dst))
    =
    ()
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 one)

let chunked_vertex_edge_targets_non_infix_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        chunked_vertex_edge_targets_non_infix mh /\
        ChunkedMajorGraph.chunked_major_edge mh src dst /\
        ChunkedMajorGraph.chunked_major_vertex mh dst)
      (ensures ~(SweepDefs.chunked_is_infix mh dst))
  =
  ()
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_mark_bounded_preserves_vertex_edge_targets_non_infix
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        chunked_vertex_edge_targets_non_infix mh)
      (ensures
        chunked_vertex_edge_targets_non_infix
          (BDefs.chunked_mark_bounded mh cap fuel))
  =
  let mh_mark = BDefs.chunked_mark_bounded mh cap fuel in
  BPres.chunked_mark_bounded_preserves_major_objects mh cap fuel;
  BColor.chunked_mark_bounded_pointer_classification_preserved mh cap fuel;
  let edge_target_non_infix (src dst: obj_addr)
    : Lemma
        (requires
          ChunkedMajorGraph.chunked_major_edge mh_mark src dst /\
          ChunkedMajorGraph.chunked_major_vertex mh_mark dst)
        (ensures ~(SweepDefs.chunked_is_infix mh_mark dst))
    =
    ChunkedMajorGraph.chunked_major_edge_source_vertex mh_mark src dst;
    ChunkedMajorGraph.chunked_major_vertex_elim mh_mark src;
    ChunkedMajorGraph.chunked_major_vertex_elim mh_mark dst;
    ChunkedMajorGraph.chunked_major_vertex_intro mh src;
    ChunkedMajorGraph.chunked_major_vertex_intro mh dst;
    BColor.chunked_mark_bounded_field_preserved mh cap fuel src;
    BMetadata.chunked_mark_bounded_preserves_no_scan_status
      mh cap fuel src;
    ChunkedMajorGraph.chunked_major_successors_preserved_from_fields
      mh mh_mark src;
    ChunkedMajorGraph.chunked_major_successors_preserved_elim
      mh mh_mark src;
    assert (ChunkedMajorGraph.chunked_major_edge mh src dst);
    chunked_vertex_edge_targets_non_infix_elim mh src dst;
    BTag.chunked_mark_bounded_preserves_infix_status mh cap fuel dst
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 edge_target_non_infix);
  chunked_vertex_edge_targets_non_infix_intro mh_mark
#pop-options
