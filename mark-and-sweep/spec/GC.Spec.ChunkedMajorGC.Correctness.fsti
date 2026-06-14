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

module Obj = GC.Spec.Object
module HeapGraph = GC.Spec.HeapGraph
module MH = GC.Spec.MajorHeap
module DenseCorrectness = GC.Spec.Correctness
module SweepInv = GC.Spec.SweepInv
module DenseFused = GC.Spec.SweepCoalesce.Defs
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module ChunkedMark = GC.Spec.ChunkedMarkBounded.Defs
module ChunkedMarkPres = GC.Spec.ChunkedMarkBounded.Preservation
module ChunkedMarkStackReady = GC.Spec.ChunkedMarkBounded.StackReady
module ChunkedMajorGC = GC.Spec.ChunkedMajorGC.Defs
module ChunkedMarkOuter = GC.Spec.ChunkedMarkBounded.OuterCompat
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph

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

val chunked_major_gc_bounded_mark_phase_preserves_shape
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel)
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         MH.major_objects marked == MH.major_objects mh))

val chunked_major_gc_bounded_mark_phase_preserves_membership
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        Seq.mem obj
          (MH.major_objects (ChunkedMark.chunked_mark_bounded mh cap fuel)))

val chunked_major_gc_bounded_mark_phase_marks_target_black
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        ChunkedMarkPres.chunked_mark_bounded_marks_target_ready
          mh cap fuel target)
      (ensures
        SweepDefs.chunked_is_black
          (ChunkedMark.chunked_mark_bounded mh cap fuel) target)

val chunked_major_gc_bounded_marked_live_subgraph_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_idx: obj_addr -> nat)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         (forall (j: nat). j < Seq.length marked ==>
           forall (o: obj_addr).
           Seq.mem o (MH.objects_in_chunk (Seq.index marked j)) ==>
           U64.v (SweepDefs.chunked_wosize_of_object marked o) ==
           MH.object_wosize_in_chunk (Seq.index marked j) o) /\
         (forall (target: obj_addr).
           live target ==>
           live_idx target < Seq.length marked /\
           Seq.mem target
             (MH.objects_in_chunk (Seq.index marked (live_idx target))) /\
           SweepDefs.chunked_read_header marked target ==
             Some (live_hdr target) /\
           SweepDefs.chunked_is_black marked target /\
           U64.v (Obj.getWosize (live_hdr target)) ==
             MH.object_wosize_in_chunk
               (Seq.index marked (live_idx target)) target)))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))

val chunked_major_gc_bounded_marked_black_live_subgraph_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         (forall (j: nat). j < Seq.length marked ==>
           forall (o: obj_addr).
           Seq.mem o (MH.objects_in_chunk (Seq.index marked j)) ==>
           U64.v (SweepDefs.chunked_wosize_of_object marked o) ==
           MH.object_wosize_in_chunk (Seq.index marked j) o) /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects marked) /\
           SweepDefs.chunked_read_header marked target ==
             Some (live_hdr target) /\
           SweepDefs.chunked_is_black marked target)))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))

val chunked_major_gc_bounded_marked_black_live_subgraph_preserved_from_membership
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects marked) /\
           SweepDefs.chunked_read_header marked target ==
             Some (live_hdr target) /\
           SweepDefs.chunked_is_black marked target)))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))

val chunked_major_gc_bounded_marked_black_live_subgraph_preserved_from_membership_no_header
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects marked) /\
           SweepDefs.chunked_is_black marked target)))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))

val chunked_major_gc_bounded_live_subgraph_preserved_from_target_ready
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap mh /\
         ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects mh) /\
           SweepDefs.chunked_read_header marked target ==
             Some (live_hdr target) /\
           ChunkedMarkPres.chunked_mark_bounded_marks_target_ready
             mh cap fuel target)))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))

val chunked_major_gc_bounded_live_subgraph_preserved_from_target_ready_no_header
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.major_objects mh) /\
          ChunkedMarkPres.chunked_mark_bounded_marks_target_ready
           mh cap fuel target))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))

val chunked_major_gc_bounded_live_subgraph_preserved_from_gray_rescan
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         fuel > 0 /\
         MH.well_formed_major_heap mh /\
         ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
         Seq.length (MH.major_objects mh) <= cap /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects mh) /\
           ChunkedMark.chunked_is_gray mh target /\
           SweepDefs.chunked_read_header marked target ==
            Some (live_hdr target))))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))

val chunked_major_gc_bounded_live_subgraph_preserved_from_gray_rescan_no_header
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.major_objects mh) /\
          ChunkedMark.chunked_is_gray mh target))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))

val chunked_major_gc_bounded_live_subgraph_preserved_from_gray_or_black_rescan
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         fuel > 0 /\
         MH.well_formed_major_heap mh /\
         ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
         Seq.length (MH.major_objects mh) <= cap /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects mh) /\
           (ChunkedMark.chunked_is_gray mh target \/
            SweepDefs.chunked_is_black mh target) /\
           SweepDefs.chunked_read_header marked target ==
            Some (live_hdr target))))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))

val chunked_major_gc_bounded_live_subgraph_preserved_from_gray_or_black_rescan_no_header
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.major_objects mh) /\
          (ChunkedMark.chunked_is_gray mh target \/
           SweepDefs.chunked_is_black mh target)))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))

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

val chunked_major_gc_bounded_single_chunk_full_correctness
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
        (let h_mark = GC.Spec.MarkBounded.mark_bounded h_init cap fuel in
         let (h_final, dense_fp_final) =
           DenseFused.fused_sweep_coalesce h_mark in
         let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         mh_final == MH.single_chunk_major_heap h_final /\
         DenseCorrectness.full_gc_correctness h_init h_final roots /\
         chunked_gc_postcondition mh_final))

val chunked_major_gc_bounded_single_chunk_dense_graph_pillars
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
        (let h_mark = GC.Spec.MarkBounded.mark_bounded h_init cap fuel in
         let (h_final, dense_fp_final) =
           DenseFused.fused_sweep_coalesce h_mark in
         let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         mh_final == MH.single_chunk_major_heap h_final /\
         DenseCorrectness.major_gc_live_subgraph_isomorphism
           h_init h_final roots /\
         DenseCorrectness.major_gc_unreachable_final_blue
           h_init h_final roots))

val chunked_major_gc_bounded_single_chunk_live_field_data_preserved
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
        (let (mh_final, chunked_fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (MH.single_chunk_major_heap h_init) cap fuel in
         forall (x: obj_addr).
          DenseCorrectness.heap_reachable h_init roots x ==>
          ChunkedMajorGraph.chunked_major_field_data_preserved
            (MH.single_chunk_major_heap h_init)
            mh_final
            x))

val chunked_major_gc_bounded_single_chunk_live_field_preserved
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
        (let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         forall (x: obj_addr).
           DenseCorrectness.heap_reachable h_init roots x ==>
           ChunkedMajorGraph.chunked_major_field_preserved
             (MH.single_chunk_major_heap h_init)
             mh_final
             x))

val chunked_major_gc_bounded_single_chunk_live_successors_preserved
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
        (let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         forall (x: obj_addr).
           DenseCorrectness.heap_reachable h_init roots x ==>
           ChunkedMajorGraph.chunked_major_successors_preserved
             (MH.single_chunk_major_heap h_init)
             mh_final
             x))

val chunked_major_gc_bounded_single_chunk_live_edges_preserved
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
        (let (mh_final, chunked_fp_final) =
            ChunkedMajorGC.chunked_major_gc_bounded
              (MH.single_chunk_major_heap h_init) cap fuel in
         forall (x: obj_addr).
            DenseCorrectness.heap_reachable h_init roots x ==>
            forall (y: obj_addr).
              ChunkedMajorGraph.chunked_major_edge
                (MH.single_chunk_major_heap h_init) x y <==>
              ChunkedMajorGraph.chunked_major_edge mh_final x y))

val chunked_major_gc_bounded_single_chunk_live_subgraph_preserved
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
        (let (mh_final, chunked_fp_final) =
            ChunkedMajorGC.chunked_major_gc_bounded
              (MH.single_chunk_major_heap h_init) cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           (MH.single_chunk_major_heap h_init)
           mh_final
           (fun (x: obj_addr) -> DenseCorrectness.heap_reachable h_init roots x)))
