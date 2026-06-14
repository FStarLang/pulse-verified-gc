module GC.Spec.ChunkedMarkBounded.EdgeInvariant

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph

val chunked_vertex_edge_targets_non_infix
  (mh: MH.major_heap)
  : prop

val chunked_vertex_edge_targets_non_infix_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr).
          ChunkedMajorGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGraph.chunked_major_vertex mh dst ==>
          ~(SweepDefs.chunked_is_infix mh dst))
      (ensures chunked_vertex_edge_targets_non_infix mh)

val chunked_vertex_edge_targets_non_infix_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        chunked_vertex_edge_targets_non_infix mh /\
        ChunkedMajorGraph.chunked_major_edge mh src dst /\
        ChunkedMajorGraph.chunked_major_vertex mh dst)
      (ensures ~(SweepDefs.chunked_is_infix mh dst))

val chunked_mark_step_bounded_preserves_vertex_edge_targets_non_infix
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        GC.Spec.ChunkedMarkBounded.TargetReady.chunked_bounded_stack_props
          mh st /\
        chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         chunked_vertex_edge_targets_non_infix mh'))

val chunked_mark_inner_loop_preserves_vertex_edge_targets_non_infix
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        GC.Spec.ChunkedMarkBounded.TargetReady.chunked_bounded_stack_props
          mh st /\
        chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh', _) =
          BDefs.chunked_mark_inner_loop mh st cap fuel in
         chunked_vertex_edge_targets_non_infix mh'))

val chunked_mark_bounded_preserves_vertex_edge_targets_non_infix
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
