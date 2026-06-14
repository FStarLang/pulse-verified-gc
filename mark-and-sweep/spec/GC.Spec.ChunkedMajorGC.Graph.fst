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

let chunked_major_vertex_intro
    (mh: MH.major_heap)
    (x: obj_addr)
    : Lemma
        (requires Seq.mem x (MH.major_objects mh))
        (ensures chunked_major_vertex mh x)
    = ()

let chunked_major_vertex_elim
    (mh: MH.major_heap)
    (x: obj_addr)
    : Lemma
        (requires chunked_major_vertex mh x)
        (ensures Seq.mem x (MH.major_objects mh))
    = ()

let chunked_major_vertex_from_chunk
    (mh: MH.major_heap)
    (idx: nat)
    (x: obj_addr)
  : Lemma
      (requires
        idx < Seq.length mh /\
        Seq.mem x (MH.objects_in_chunk (Seq.index mh idx)))
      (ensures chunked_major_vertex mh x)
  =
  MH.major_objects_member_at_index mh idx x

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

let chunked_major_field_data_preserved
    (mh_init: MH.major_heap)
    (mh_final: MH.major_heap)
    (x: obj_addr)
  : prop
  =
  chunked_major_vertex mh_init x /\
  chunked_major_vertex mh_final x /\
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

let chunked_major_field_points_to_intro
  (mh: MH.major_heap)
  (x: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (y: obj_addr)
  : Lemma
      (requires
        chunked_major_vertex mh x /\
        U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh x) /\
        (let v = MarkDefs.chunked_get_field mh x i in
         MarkDefs.chunked_is_pointer_field mh v /\
         MarkDefs.chunked_pointer_field_as_obj_addr mh v == y))
      (ensures chunked_major_field_points_to mh x i y)
  = ()

let chunked_major_edge_intro
  (mh: MH.major_heap)
  (x y: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires chunked_major_field_points_to mh x i y)
      (ensures chunked_major_edge mh x y)
  =
  FStar.Classical.exists_intro
    (fun (j: U64.t{U64.v j >= 1}) ->
      chunked_major_field_points_to mh x j y)
    i

let chunked_major_pointer_classification_preserved
    (mh_init: MH.major_heap)
    (mh_final: MH.major_heap)
  : prop
  =
  forall (v: U64.t).
    MarkDefs.chunked_is_pointer_field mh_init v ==
    MarkDefs.chunked_is_pointer_field mh_final v

let chunked_major_pointer_classification_preserved_intro
    (mh_init: MH.major_heap)
    (mh_final: MH.major_heap)
  : Lemma
      (requires
        (forall (v: U64.t).
          MarkDefs.chunked_is_pointer_field mh_init v ==
          MarkDefs.chunked_is_pointer_field mh_final v))
      (ensures
        chunked_major_pointer_classification_preserved mh_init mh_final)
  =
  ()

let chunked_major_successors_preserved
    (mh_init: MH.major_heap)
    (mh_final: MH.major_heap)
    (x: obj_addr)
  : prop
  =
  forall (y: obj_addr).
    chunked_major_edge mh_init x y <==>
    chunked_major_edge mh_final x y

let chunked_major_live_subgraph_preserved
    (mh_init: MH.major_heap)
    (mh_final: MH.major_heap)
    (live: obj_addr -> prop)
  : prop
  =
  (forall (x: obj_addr).
    live x ==>
    chunked_major_vertex mh_init x /\
    chunked_major_vertex mh_final x) /\
  (forall (x: obj_addr).
    live x ==>
    forall (y: obj_addr).
    (chunked_major_edge mh_init x y <==>
     chunked_major_edge mh_final x y))

let chunked_major_successors_preserved_elim
    (mh_init: MH.major_heap)
    (mh_final: MH.major_heap)
    (x: obj_addr)
  : Lemma
      (requires chunked_major_successors_preserved mh_init mh_final x)
      (ensures
        forall (y: obj_addr).
          chunked_major_edge mh_init x y <==>
          chunked_major_edge mh_final x y)
  = ()

let chunked_major_live_subgraph_preserved_intro
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
  = ()

let chunked_major_field_preserved_intro
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
    = ()

let chunked_major_field_data_preserved_intro
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
    = ()

let chunked_major_field_data_preserved_elim
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
  = ()

let chunked_major_live_subgraph_vertices_elim
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
  = ()

let chunked_major_live_subgraph_edges_elim
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
  = ()

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_live_subgraph_preserved_trans
    (mh0 mh1 mh2: MH.major_heap)
    (live: obj_addr -> prop)
  : Lemma
      (requires
        chunked_major_live_subgraph_preserved mh0 mh1 live /\
        chunked_major_live_subgraph_preserved mh1 mh2 live)
      (ensures
        chunked_major_live_subgraph_preserved mh0 mh2 live)
  =
  chunked_major_live_subgraph_vertices_elim mh0 mh1 live;
  chunked_major_live_subgraph_vertices_elim mh1 mh2 live;
  chunked_major_live_subgraph_edges_elim mh0 mh1 live;
  chunked_major_live_subgraph_edges_elim mh1 mh2 live;
  let vertices (x: obj_addr)
    : Lemma
        (requires live x)
        (ensures chunked_major_vertex mh0 x /\ chunked_major_vertex mh2 x)
    =
    assert (chunked_major_vertex mh0 x /\ chunked_major_vertex mh1 x);
    assert (chunked_major_vertex mh1 x /\ chunked_major_vertex mh2 x)
  in
  let edges (x: obj_addr)
    : Lemma
        (requires live x)
        (ensures
          forall (y: obj_addr).
            (chunked_major_edge mh0 x y <==>
             chunked_major_edge mh2 x y))
    =
    let edge_y (y: obj_addr)
      : Lemma
          (ensures
            (chunked_major_edge mh0 x y <==>
             chunked_major_edge mh2 x y))
      =
      assert (chunked_major_edge mh0 x y <==>
              chunked_major_edge mh1 x y);
      assert (chunked_major_edge mh1 x y <==>
              chunked_major_edge mh2 x y)
    in
    FStar.Classical.forall_intro edge_y
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires vertices);
  FStar.Classical.forall_intro (FStar.Classical.move_requires edges);
  chunked_major_live_subgraph_preserved_intro mh0 mh2 live
#pop-options

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

let chunked_major_field_data_preserved_single_chunk_from_dense
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
  =
  chunked_major_vertex_single_chunk_compat g_init x;
  chunked_major_vertex_single_chunk_compat g_final x;
  SweepDefs.chunked_wosize_of_object_single_chunk_compat g_init x;
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

let chunked_major_pointer_classification_preserved_single_chunk
    (g_init: heap)
    (g_final: heap)
  : Lemma
      (ensures
        chunked_major_pointer_classification_preserved
          (MH.single_chunk_major_heap g_init)
          (MH.single_chunk_major_heap g_final))
  =
  let aux (v: U64.t)
    : Lemma
        (ensures
          MarkDefs.chunked_is_pointer_field (MH.single_chunk_major_heap g_init) v ==
          MarkDefs.chunked_is_pointer_field (MH.single_chunk_major_heap g_final) v)
    =
    MarkDefs.chunked_is_pointer_field_step
      (MH.single_chunk_major_heap g_init) v;
    MarkDefs.chunked_is_pointer_field_step
      (MH.single_chunk_major_heap g_final) v;
    MH.single_chunk_major_pointer_compat g_init v;
    MH.single_chunk_major_pointer_compat g_final v
  in
  FStar.Classical.forall_intro aux

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

let chunked_major_live_subgraph_preserved_from_fields
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
  =
  let vertices (x: obj_addr)
    : Lemma
        (requires live x)
        (ensures
          chunked_major_vertex mh_init x /\
          chunked_major_vertex mh_final x)
    =
    assert (chunked_major_field_preserved mh_init mh_final x)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires vertices);
  let edges (x: obj_addr)
    : Lemma
        (requires live x)
        (ensures
          forall (y: obj_addr).
            chunked_major_edge mh_init x y <==>
            chunked_major_edge mh_final x y)
    =
    assert (chunked_major_field_preserved mh_init mh_final x);
    chunked_major_successors_preserved_from_fields mh_init mh_final x;
    chunked_major_successors_preserved_elim mh_init mh_final x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires edges);
  chunked_major_live_subgraph_preserved_intro mh_init mh_final live
