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
module Fields = GC.Spec.Fields
module HeapGraph = GC.Spec.HeapGraph
module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module DenseCorrectness = GC.Spec.Correctness
module SweepInv = GC.Spec.SweepInv
module BMark = GC.Spec.MarkBounded
module BMarkCorr = GC.Spec.MarkBoundedCorrectness
module SpecSweepCoalesce = GC.Spec.SweepCoalesce
module DenseFused = GC.Spec.SweepCoalesce.Defs
module ChunkedMajorGC = GC.Spec.ChunkedMajorGC.Defs
module ChunkedMarkOuter = GC.Spec.ChunkedMarkBounded.OuterCompat

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let chunked_no_gray_or_black_objects (mh: MH.major_heap) : prop =
  forall (x: obj_addr). Seq.mem x (MH.major_objects mh) ==>
    SweepDefs.chunked_is_white mh x \/ SweepDefs.chunked_is_blue mh x

let chunked_gc_postcondition (mh: MH.major_heap) : prop =
  MH.well_formed_major_heap mh /\
  chunked_no_gray_or_black_objects mh

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let fields_object_after_zero_addr (g: heap) (x: obj_addr)
  : Lemma
      (requires Seq.mem x (Fields.objects zero_addr g))
      (ensures U64.v x >= U64.v zero_addr + U64.v mword)
  =
  Fields.objects_addresses_gt_start zero_addr g x
#pop-options

let chunked_gc_postcondition_intro (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_no_gray_or_black_objects mh)
      (ensures chunked_gc_postcondition mh)
  = ()

let chunked_gc_postcondition_elim (mh: MH.major_heap)
  : Lemma
      (requires chunked_gc_postcondition mh)
      (ensures
        MH.well_formed_major_heap mh /\
        chunked_no_gray_or_black_objects mh)
  = ()

let chunked_no_gray_or_black_single_chunk_from_dense (g: heap)
  : Lemma
      (requires DenseCorrectness.gc_postcondition g)
      (ensures
        chunked_no_gray_or_black_objects
          (MH.single_chunk_major_heap g))
  =
  DenseCorrectness.gc_postcondition_elim g;
  MH.single_chunk_major_objects_compat g;
  let aux (x: obj_addr)
    : Lemma
        (requires Seq.mem x (MH.major_objects (MH.single_chunk_major_heap g)))
        (ensures
          SweepDefs.chunked_is_white (MH.single_chunk_major_heap g) x \/
          SweepDefs.chunked_is_blue (MH.single_chunk_major_heap g) x)
    =
    assert (Seq.mem x (Fields.objects zero_addr g));
    fields_object_after_zero_addr g x;
    SweepDefs.chunked_is_white_single_chunk_compat g x;
    SweepDefs.chunked_is_blue_single_chunk_compat g x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let chunked_gc_postcondition_single_chunk_from_dense (g: heap)
  : Lemma
      (requires DenseCorrectness.gc_postcondition g)
      (ensures
        chunked_gc_postcondition (MH.single_chunk_major_heap g))
  =
  DenseCorrectness.gc_postcondition_elim g;
  MH.single_chunk_major_heap_wf g;
  chunked_no_gray_or_black_single_chunk_from_dense g

let bounded_mark_no_gray_for_fused
    (h_init: heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        well_formed_heap h_init /\
        Seq.length (objects zero_addr h_init) > 0 /\
        SweepInv.heap_objects_dense h_init /\
        fuel >= BMark.count_non_black h_init)
      (ensures
        (let h_mark = BMark.mark_bounded h_init cap fuel in
         forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr h_mark) ==>
           ~(Obj.is_gray x h_mark)))
  =
  let h_mark = BMark.mark_bounded h_init cap fuel in
  BMark.mark_bounded_completes h_init cap fuel;
  let no_gray (x: obj_addr)
    : Lemma
        (requires Seq.mem x (Fields.objects zero_addr h_mark))
        (ensures ~(Obj.is_gray x h_mark))
    =
    SweepInv.no_gray_elim x h_mark
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires no_gray)

let chunked_major_gc_bounded_single_chunk_postcondition
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
        fuel >= BMark.count_non_black h_init /\
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
  =
  let h_mark = BMark.mark_bounded h_init cap fuel in
  BMarkCorr.mark_bounded_satisfies_mark_post h_init roots fp cap fuel;
  DenseCorrectness.mark_post_elim_wfh h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_density h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_fp h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_no_grey h_init h_mark roots fp;
  bounded_mark_no_gray_for_fused h_init cap fuel;
  assert (forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr h_mark) ==>
    ~(Obj.is_gray x h_mark));
  SpecSweepCoalesce.fused_eq_sweep_coalesce h_mark fp;
  DenseCorrectness.gc_postcondition_gen h_init h_mark roots fp;
  ChunkedMajorGC.chunked_major_gc_bounded_single_chunk_compat
    h_init cap fuel;
  let (h_final, fp_final) = DenseFused.fused_sweep_coalesce h_mark in
  assert (DenseCorrectness.gc_postcondition h_final);
  chunked_gc_postcondition_single_chunk_from_dense h_final

let chunked_major_gc_bounded_single_chunk_full_correctness
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
        fuel >= BMark.count_non_black h_init /\
        ChunkedMarkOuter.mark_bounded_single_chunk_ready h_init cap fuel /\
        (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) /\
          (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
        (let graph = create_graph h_init in
         let roots' = HeapGraph.coerce_to_vertex_list roots in
         graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
      (ensures
        (let h_mark = BMark.mark_bounded h_init cap fuel in
         let (h_final, dense_fp_final) =
           DenseFused.fused_sweep_coalesce h_mark in
         let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         mh_final == MH.single_chunk_major_heap h_final /\
         DenseCorrectness.full_gc_correctness h_init h_final roots /\
         chunked_gc_postcondition mh_final))
  =
  let h_mark = BMark.mark_bounded h_init cap fuel in
  BMarkCorr.mark_bounded_satisfies_mark_post h_init roots fp cap fuel;
  DenseCorrectness.mark_post_elim_wfh h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_density h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_fp h_init h_mark roots fp;
  bounded_mark_no_gray_for_fused h_init cap fuel;
  assert (forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr h_mark) ==>
    ~(Obj.is_gray x h_mark));
  SpecSweepCoalesce.fused_eq_sweep_coalesce h_mark fp;
  DenseCorrectness.full_gc_correctness_through_coalesce_gen
    h_init h_mark roots fp;
  ChunkedMajorGC.chunked_major_gc_bounded_single_chunk_compat
    h_init cap fuel;
  let (h_final, dense_fp_final) =
    DenseFused.fused_sweep_coalesce h_mark in
  assert (DenseCorrectness.full_gc_correctness h_init h_final roots);
  chunked_major_gc_bounded_single_chunk_postcondition
    h_init roots fp cap fuel
