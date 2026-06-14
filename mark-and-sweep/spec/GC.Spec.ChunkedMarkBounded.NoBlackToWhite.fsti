module GC.Spec.ChunkedMarkBounded.NoBlackToWhite

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph

val chunked_no_black_to_white_vertex_targets
  (mh: MH.major_heap)
  : prop

val chunked_no_black_to_white_vertex_targets_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr).
          ChunkedMajorGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGraph.chunked_major_vertex mh dst /\
          GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh src ==>
          ~(GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white mh dst))
      (ensures chunked_no_black_to_white_vertex_targets mh)

val chunked_no_black_to_white_vertex_targets_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        chunked_no_black_to_white_vertex_targets mh /\
        ChunkedMajorGraph.chunked_major_edge mh src dst /\
        ChunkedMajorGraph.chunked_major_vertex mh dst /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh src)
      (ensures ~(GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white mh dst))

val chunked_push_children_bounded_field_target_non_white
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  (j: U64.t{U64.v j >= 1})
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        U64.v i <= U64.v j /\
        U64.v j <= U64.v ws /\
        ChunkedMajorGraph.chunked_major_vertex mh target /\
        ChunkedMajorGraph.chunked_major_field_points_to mh obj j target /\
        ~(GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_infix mh target))
      (ensures
        (let (mh', _) =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         ~(GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white mh' target)))

val chunked_mark_step_bounded_preserves_no_black_to_white
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        chunked_no_black_to_white_vertex_targets mh /\
        GC.Spec.ChunkedMarkBounded.EdgeInvariant.chunked_vertex_edge_targets_non_infix
          (fst (BDefs.chunked_mark_step_bounded mh st cap)))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         chunked_no_black_to_white_vertex_targets mh'))
