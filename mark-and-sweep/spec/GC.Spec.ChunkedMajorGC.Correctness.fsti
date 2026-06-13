module GC.Spec.ChunkedMajorGC.Correctness

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Spec.Mark

module HeapGraph = GC.Spec.HeapGraph
module MH = GC.Spec.MajorHeap
module DenseCorrectness = GC.Spec.Correctness
module SweepInv = GC.Spec.SweepInv
module ChunkedMajorGC = GC.Spec.ChunkedMajorGC.Defs
module ChunkedMarkOuter = GC.Spec.ChunkedMarkBounded.OuterCompat

val chunked_no_gray_or_black_objects
  (mh: MH.major_heap)
  : prop

val chunked_gc_postcondition
  (mh: MH.major_heap)
  : prop

val chunked_gc_postcondition_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_no_gray_or_black_objects mh)
      (ensures chunked_gc_postcondition mh)

val chunked_gc_postcondition_elim
  (mh: MH.major_heap)
  : Lemma
      (requires chunked_gc_postcondition mh)
      (ensures
        MH.well_formed_major_heap mh /\
        chunked_no_gray_or_black_objects mh)

val chunked_no_gray_or_black_single_chunk_from_dense
  (g: heap)
  : Lemma
      (requires DenseCorrectness.gc_postcondition g)
      (ensures
        chunked_no_gray_or_black_objects
          (MH.single_chunk_major_heap g))

val chunked_gc_postcondition_single_chunk_from_dense
  (g: heap)
  : Lemma
      (requires DenseCorrectness.gc_postcondition g)
      (ensures
        chunked_gc_postcondition (MH.single_chunk_major_heap g))

val chunked_major_gc_bounded_single_chunk_postcondition
  (h_init: heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        well_formed_heap h_init /\
        Seq.length (objects zero_addr h_init) > 0 /\
        SweepInv.heap_objects_dense h_init /\
        root_props h_init roots /\
        GC.Spec.Sweep.fp_in_heap fp h_init /\
        no_black_objects h_init /\
        no_pointer_to_blue h_init /\
        no_scan_invariant h_init /\
        fuel >= GC.Spec.MarkBounded.count_non_black h_init /\
        ChunkedMarkOuter.mark_bounded_single_chunk_ready h_init cap fuel /\
        (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) /\
          (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
        (let graph = create_graph h_init in
         let roots' = HeapGraph.coerce_to_vertex_list roots in
         graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
      (ensures
        (let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         chunked_gc_postcondition mh_final))
