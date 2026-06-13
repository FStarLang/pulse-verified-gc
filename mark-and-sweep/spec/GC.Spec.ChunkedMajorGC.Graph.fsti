module GC.Spec.ChunkedMajorGC.Graph

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module HeapGraph = GC.Spec.HeapGraph
module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs
module MarkCompat = GC.Spec.ChunkedMark.Compat
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs

val chunked_major_vertex
  (mh: MH.major_heap)
  (x: obj_addr)
  : prop

val chunked_major_vertex_intro
  (mh: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires Seq.mem x (MH.major_objects mh))
      (ensures chunked_major_vertex mh x)

val chunked_major_vertex_from_chunk
  (mh: MH.major_heap)
  (idx: nat)
  (x: obj_addr)
  : Lemma
      (requires
        idx < Seq.length mh /\
        Seq.mem x (MH.objects_in_chunk (Seq.index mh idx)))
      (ensures chunked_major_vertex mh x)

val chunked_major_field_preserved
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (x: obj_addr)
  : prop

val chunked_major_field_data_preserved
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (x: obj_addr)
  : prop

val chunked_major_field_points_to
  (mh: MH.major_heap)
  (x: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (y: obj_addr)
  : prop

val chunked_major_edge
  (mh: MH.major_heap)
  (x: obj_addr)
  (y: obj_addr)
  : prop

val chunked_major_pointer_classification_preserved
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  : prop

val chunked_major_pointer_classification_preserved_intro
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  : Lemma
      (requires
        (forall (v: U64.t).
          MarkDefs.chunked_is_pointer_field mh_init v ==
          MarkDefs.chunked_is_pointer_field mh_final v))
      (ensures
        chunked_major_pointer_classification_preserved mh_init mh_final)

val chunked_major_successors_preserved
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (x: obj_addr)
  : prop

val chunked_major_live_subgraph_preserved
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (live: obj_addr -> prop)
  : prop

val chunked_major_successors_preserved_elim
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires chunked_major_successors_preserved mh_init mh_final x)
      (ensures
        forall (y: obj_addr).
          chunked_major_edge mh_init x y <==>
          chunked_major_edge mh_final x y)

val chunked_major_live_subgraph_preserved_intro
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        (forall (x: obj_addr).
          live x ==>
          chunked_major_vertex mh_init x /\
          chunked_major_vertex mh_final x) /\
        (forall (x: obj_addr).
          live x ==>
          forall (y: obj_addr).
          (chunked_major_edge mh_init x y <==>
           chunked_major_edge mh_final x y)))
      (ensures chunked_major_live_subgraph_preserved mh_init mh_final live)

val chunked_major_field_preserved_intro
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires
       chunked_major_vertex mh_init x /\
       chunked_major_vertex mh_final x /\
       SweepDefs.chunked_wosize_of_object mh_init x ==
         SweepDefs.chunked_wosize_of_object mh_final x /\
       (forall (i: U64.t). U64.v i >= 1 /\
         U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh_init x) ==>
         MarkDefs.chunked_get_field mh_init x i ==
           MarkDefs.chunked_get_field mh_final x i))
      (ensures chunked_major_field_preserved mh_init mh_final x)

val chunked_major_field_data_preserved_intro
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires
        chunked_major_vertex mh_init x /\
        chunked_major_vertex mh_final x /\
        (forall (i: U64.t). U64.v i >= 1 /\
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh_init x) ==>
          MarkDefs.chunked_get_field mh_init x i ==
            MarkDefs.chunked_get_field mh_final x i))
      (ensures chunked_major_field_data_preserved mh_init mh_final x)

val chunked_major_field_data_preserved_elim
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires chunked_major_field_data_preserved mh_init mh_final x)
      (ensures
       chunked_major_vertex mh_init x /\
       chunked_major_vertex mh_final x /\
       (forall (i: U64.t). U64.v i >= 1 /\
         U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh_init x) ==>
         MarkDefs.chunked_get_field mh_init x i ==
           MarkDefs.chunked_get_field mh_final x i))

val chunked_major_live_subgraph_vertices_elim
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (live: obj_addr -> prop)
  : Lemma
      (requires chunked_major_live_subgraph_preserved mh_init mh_final live)
      (ensures
        forall (x: obj_addr).
          live x ==>
          chunked_major_vertex mh_init x /\
          chunked_major_vertex mh_final x)

val chunked_major_live_subgraph_edges_elim
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (live: obj_addr -> prop)
  : Lemma
      (requires chunked_major_live_subgraph_preserved mh_init mh_final live)
      (ensures
        forall (x: obj_addr).
          live x ==>
          forall (y: obj_addr).
          (chunked_major_edge mh_init x y <==>
           chunked_major_edge mh_final x y))

val chunked_major_vertex_single_chunk_compat
  (g: heap)
  (x: obj_addr)
  : Lemma
      (ensures
        (chunked_major_vertex (MH.single_chunk_major_heap g) x <==>
         Seq.mem x (objects zero_addr g)))

val chunked_major_field_preserved_single_chunk_from_dense
  (g_init: heap)
  (g_final: heap)
  (x: obj_addr)
  : Lemma
      (requires
        Seq.mem x (objects zero_addr g_init) /\
        Seq.mem x (objects zero_addr g_final) /\
        U64.v x >= U64.v zero_addr + U64.v mword /\
        wosize_of_object x g_init == wosize_of_object x g_final /\
        (forall (i: U64.t). U64.v i >= 1 /\
          U64.v i <= U64.v (wosize_of_object x g_init) ==>
          HeapGraph.get_field g_init x i == HeapGraph.get_field g_final x i))
      (ensures
        chunked_major_field_preserved
          (MH.single_chunk_major_heap g_init)
          (MH.single_chunk_major_heap g_final)
          x)

val chunked_major_field_data_preserved_single_chunk_from_dense
  (g_init: heap)
  (g_final: heap)
  (x: obj_addr)
  : Lemma
      (requires
        Seq.mem x (objects zero_addr g_init) /\
        Seq.mem x (objects zero_addr g_final) /\
        U64.v x >= U64.v zero_addr + U64.v mword /\
        (forall (i: U64.t). U64.v i >= 1 /\
          U64.v i <= U64.v (wosize_of_object x g_init) ==>
          HeapGraph.get_field g_init x i == HeapGraph.get_field g_final x i))
      (ensures
        chunked_major_field_data_preserved
          (MH.single_chunk_major_heap g_init)
          (MH.single_chunk_major_heap g_final)
          x)

val chunked_major_pointer_classification_preserved_single_chunk
  (g_init: heap)
  (g_final: heap)
  : Lemma
      (ensures
        chunked_major_pointer_classification_preserved
          (MH.single_chunk_major_heap g_init)
          (MH.single_chunk_major_heap g_final))

val chunked_major_successors_preserved_from_fields
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires
        chunked_major_field_preserved mh_init mh_final x /\
        chunked_major_pointer_classification_preserved mh_init mh_final)
      (ensures
        chunked_major_successors_preserved mh_init mh_final x)

val chunked_major_live_subgraph_preserved_from_fields
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        (forall (x: obj_addr).
          live x ==>
          chunked_major_field_preserved mh_init mh_final x) /\
        chunked_major_pointer_classification_preserved mh_init mh_final)
      (ensures
        chunked_major_live_subgraph_preserved mh_init mh_final live)
