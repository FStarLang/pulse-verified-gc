module GC.Gen.ChunkedMajorGCBridge

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Gen.Base
open GC.Gen.MinorHeap

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module ChunkedMark = GC.Spec.ChunkedMarkBounded.Defs
module ChunkedMarkPres = GC.Spec.ChunkedMarkBounded.Preservation
module ChunkedMarkLive = GC.Spec.ChunkedMajorGC.MarkLiveness
module ChunkedMarkEdge = GC.Spec.ChunkedMarkBounded.EdgeInvariant
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph
module ChunkedMajorGC = GC.Spec.ChunkedMajorGC.Defs
module ChunkedMajorGCCorr = GC.Spec.ChunkedMajorGC.Correctness
module ChunkedMarkNoBlack = GC.Spec.ChunkedMarkBounded.NoBlackToWhite
module GenInv = GC.Gen.HeapInvariant

val chunked_sweep_black_implies_gen_black
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires SweepDefs.chunked_is_black mh obj)
      (ensures GenInv.chunked_is_black mh obj)

val chunked_no_black_objects_implies_no_black_to_white_vertex_targets
  (mh: MH.major_heap)
  : Lemma
      (requires GenInv.chunked_no_black_objects mh)
      (ensures
        ChunkedMarkNoBlack.chunked_no_black_to_white_vertex_targets mh)

val chunked_collection_heap_shape_implies_no_black_to_white_vertex_targets
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape minor mh fp fuel)
      (ensures
        ChunkedMarkNoBlack.chunked_no_black_to_white_vertex_targets mh)

val chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        mark_fuel > 0 /\
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMark.chunked_count_non_black mh /\
        ChunkedMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMarkLive.chunked_no_pointer_to_blue mh /\
        ChunkedMarkEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
