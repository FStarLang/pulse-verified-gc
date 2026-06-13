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

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let chunked_major_vertex (mh: MH.major_heap) (x: obj_addr) : prop =
  Seq.mem x (MH.major_objects mh)

let chunked_major_field_preserved
    (mh_init: MH.major_heap)
    (mh_final: MH.major_heap)
    (x: obj_addr)
  : prop
  =
  chunked_major_vertex mh_init x /\
  chunked_major_vertex mh_final x /\
  SweepDefs.chunked_wosize_of_object mh_init x ==
    SweepDefs.chunked_wosize_of_object mh_final x /\
  (forall (i: U64.t). U64.v i >= 1 /\
    U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh_init x) ==>
    MarkDefs.chunked_get_field mh_init x i ==
      MarkDefs.chunked_get_field mh_final x i)

let chunked_major_field_points_to
    (mh: MH.major_heap)
    (x: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (y: obj_addr)
  : prop
  =
  chunked_major_vertex mh x /\
  U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh x) /\
  (let v = MarkDefs.chunked_get_field mh x i in
   MarkDefs.chunked_is_pointer_field mh v /\
   MarkDefs.chunked_pointer_field_as_obj_addr mh v == y)

let chunked_major_edge
    (mh: MH.major_heap)
    (x: obj_addr)
    (y: obj_addr)
  : prop
  =
  exists (i: U64.t{U64.v i >= 1}). chunked_major_field_points_to mh x i y

let chunked_major_pointer_classification_preserved
    (mh_init: MH.major_heap)
    (mh_final: MH.major_heap)
  : prop
  =
  forall (v: U64.t).
    MarkDefs.chunked_is_pointer_field mh_init v ==
    MarkDefs.chunked_is_pointer_field mh_final v

let chunked_major_successors_preserved
    (mh_init: MH.major_heap)
    (mh_final: MH.major_heap)
    (x: obj_addr)
  : prop
  =
  forall (y: obj_addr).
    chunked_major_edge mh_init x y <==>
    chunked_major_edge mh_final x y

let chunked_major_vertex_single_chunk_compat (g: heap) (x: obj_addr)
  : Lemma
      (ensures
        (chunked_major_vertex (MH.single_chunk_major_heap g) x <==>
         Seq.mem x (objects zero_addr g)))
  =
  MH.single_chunk_major_objects_compat g

let chunked_major_field_preserved_single_chunk_from_dense
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
  =
  chunked_major_vertex_single_chunk_compat g_init x;
  chunked_major_vertex_single_chunk_compat g_final x;
  SweepDefs.chunked_wosize_of_object_single_chunk_compat g_init x;
  SweepDefs.chunked_wosize_of_object_single_chunk_compat g_final x;
  let field_eq (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object
            (MH.single_chunk_major_heap g_init) x))
        (ensures
          MarkDefs.chunked_get_field
            (MH.single_chunk_major_heap g_init) x i ==
          MarkDefs.chunked_get_field
            (MH.single_chunk_major_heap g_final) x i)
    =
    MarkCompat.chunked_get_field_single_chunk_compat g_init x i;
    MarkCompat.chunked_get_field_single_chunk_compat g_final x i
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires field_eq)

let chunked_major_field_points_to_preserved_forward
    (mh_init: MH.major_heap)
    (mh_final: MH.major_heap)
    (x: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (y: obj_addr)
  : Lemma
      (requires
        chunked_major_field_preserved mh_init mh_final x /\
        chunked_major_pointer_classification_preserved mh_init mh_final /\
        chunked_major_field_points_to mh_init x i y)
      (ensures
        chunked_major_field_points_to mh_final x i y)
  =
  let v = MarkDefs.chunked_get_field mh_init x i in
  assert (MarkDefs.chunked_get_field mh_final x i == v);
  assert (MarkDefs.chunked_is_pointer_field mh_final v);
  MarkDefs.chunked_pointer_field_as_obj_addr_step mh_init v;
  MarkDefs.chunked_pointer_field_as_obj_addr_step mh_final v

let chunked_major_field_points_to_preserved_backward
    (mh_init: MH.major_heap)
    (mh_final: MH.major_heap)
    (x: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (y: obj_addr)
  : Lemma
      (requires
        chunked_major_field_preserved mh_init mh_final x /\
        chunked_major_pointer_classification_preserved mh_init mh_final /\
        chunked_major_field_points_to mh_final x i y)
      (ensures
        chunked_major_field_points_to mh_init x i y)
  =
  let v = MarkDefs.chunked_get_field mh_final x i in
  assert (MarkDefs.chunked_get_field mh_init x i == v);
  assert (MarkDefs.chunked_is_pointer_field mh_init v);
  MarkDefs.chunked_pointer_field_as_obj_addr_step mh_final v;
  MarkDefs.chunked_pointer_field_as_obj_addr_step mh_init v

let chunked_major_successors_preserved_from_fields
    (mh_init: MH.major_heap)
    (mh_final: MH.major_heap)
    (x: obj_addr)
  : Lemma
      (requires
        chunked_major_field_preserved mh_init mh_final x /\
        chunked_major_pointer_classification_preserved mh_init mh_final)
      (ensures
        chunked_major_successors_preserved mh_init mh_final x)
  =
  let forward (y: obj_addr)
    : Lemma
        (requires chunked_major_edge mh_init x y)
        (ensures chunked_major_edge mh_final x y)
    =
    FStar.Classical.exists_elim
      (chunked_major_edge mh_final x y)
      #_
      #(fun (i: U64.t{U64.v i >= 1}) ->
        chunked_major_field_points_to mh_init x i y)
      ()
      (fun i ->
        chunked_major_field_points_to_preserved_forward
          mh_init mh_final x i y;
        FStar.Classical.exists_intro
          (fun i -> chunked_major_field_points_to mh_final x i y) i)
  in
  let backward (y: obj_addr)
    : Lemma
        (requires chunked_major_edge mh_final x y)
        (ensures chunked_major_edge mh_init x y)
    =
    FStar.Classical.exists_elim
      (chunked_major_edge mh_init x y)
      #_
      #(fun (i: U64.t{U64.v i >= 1}) ->
        chunked_major_field_points_to mh_final x i y)
      ()
      (fun i ->
        chunked_major_field_points_to_preserved_backward
          mh_init mh_final x i y;
        FStar.Classical.exists_intro
          (fun i -> chunked_major_field_points_to mh_init x i y) i)
  in
  let eqv (y: obj_addr)
    : Lemma
        (chunked_major_edge mh_init x y <==>
         chunked_major_edge mh_final x y)
    =
    FStar.Classical.forall_intro (FStar.Classical.move_requires forward);
    FStar.Classical.forall_intro (FStar.Classical.move_requires backward)
  in
  FStar.Classical.forall_intro eqv
