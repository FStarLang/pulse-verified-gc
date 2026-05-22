/// ---------------------------------------------------------------------------
/// GC.Gen.HeapInvariant -- Central generational heap-shape invariant
/// ---------------------------------------------------------------------------

module GC.Gen.HeapInvariant

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module Sweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module HeapModel = GC.Spec.HeapModel
module HeapGraph = GC.Spec.HeapGraph
module Graph = GC.Spec.Graph
module FreeListShape = GC.Gen.FreeListShape

[@@"opaque_to_smt"]
let major_heap_shape (major: heap) (fp: U64.t) : prop =
  well_formed_heap major /\
  AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
  AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
  FreeListShape.fp_pointer_or_zero fp /\
  FreeListShape.blue_link_fields_valid major /\
  heap_objects_dense major /\
  chain_objects_blue major fp /\
  Seq.length (objects zero_addr major) > 0 /\
  SweepInv.fp_valid fp major /\
  Sweep.fp_in_heap fp major /\
  Mark.no_black_objects major /\
  Mark.no_pointer_to_blue major /\
  no_scan_invariant major

[@@"opaque_to_smt"]
let minor_major_fields_no_blue (minor: minor_state) (major: heap) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    j < minor_wosize minor obj /\
    is_pointer_field (minor_read_field minor obj j) ==>
    Seq.mem ((minor_read_field minor obj j) <: obj_addr)
            (objects zero_addr major) /\
    ~(is_blue ((minor_read_field minor obj j) <: obj_addr) major)

[@@"opaque_to_smt"]
let minor_fields_no_infix_targets (minor: minor_state) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    j < minor_wosize minor obj /\
    is_minor_pointer (to_minor_offset (minor_read_field minor obj j)) ==>
    ~(is_infix_in_minor minor (to_minor_offset (minor_read_field minor obj j)))

[@@"opaque_to_smt"]
let major_minor_fields_no_infix_targets (minor: minor_state) (major: heap) : prop =
  forall (obj: obj_addr) (j: nat).
    Seq.mem obj (objects zero_addr major) /\
    ~(is_blue obj major) /\
    ~(is_no_scan obj major) /\
    j < U64.v (wosize_of_object obj major) /\
    U64.v obj + j * 8 + 8 <= heap_size /\
    (U64.v obj + j * 8) % 8 == 0 ==>
    (let v = to_minor_offset
       (read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
     is_minor_pointer v ==> ~(is_infix_in_minor minor v))

[@@"opaque_to_smt"]
let minor_heap_shape (minor: minor_state) : prop =
  minor_wf minor /\
  minor_guards_complete minor /\
  minor_infix_wf minor /\
  minor_no_scan_invariant minor /\
  minor_fields_no_infix_targets minor

let gray_black_objects_on_stack (major: heap) (st: seq obj_addr) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (objects zero_addr major) /\
    (is_gray obj major \/ is_black obj major) ==> Seq.mem obj st

[@@"opaque_to_smt"]
let major_stack_shape (major: heap) (st: seq obj_addr) (cap: nat) : prop =
  MarkBoundedInv.bounded_mark_inv major st cap /\
  Mark.root_props major st /\
  gray_black_objects_on_stack major st /\
  (let graph = HeapModel.create_graph major in
   let roots' = HeapGraph.coerce_to_vertex_list st in
   Graph.graph_wf graph /\ Graph.is_vertex_set roots' /\
   Graph.subset_vertices roots' graph.vertices)

[@@"opaque_to_smt"]
let collection_heap_shape (minor: minor_state) (major: heap) (fp: U64.t) : prop =
  major_heap_shape major fp /\
  minor_heap_shape minor /\
  minor_major_fields_no_blue minor major /\
  major_minor_fields_no_infix_targets minor major

[@@"opaque_to_smt"]
let full_heap_shape (minor: minor_state) (major: heap) (fp: U64.t)
                    (st: seq obj_addr) (cap: nat) : prop =
  collection_heap_shape minor major fp /\
  major_stack_shape major st cap

let major_heap_shape_elim (major: heap) (fp: U64.t)
  : Lemma (requires major_heap_shape major fp)
          (ensures well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    FreeListShape.fp_pointer_or_zero fp /\
                    FreeListShape.blue_link_fields_valid major /\
                    heap_objects_dense major /\
                   chain_objects_blue major fp /\
                   Seq.length (objects zero_addr major) > 0 /\
                   SweepInv.fp_valid fp major /\
                   Sweep.fp_in_heap fp major /\
                   Mark.no_black_objects major /\
                   Mark.no_pointer_to_blue major /\
                   no_scan_invariant major)
  = reveal_opaque (`%major_heap_shape) (major_heap_shape major fp)

let minor_heap_shape_elim (minor: minor_state)
  : Lemma (requires minor_heap_shape minor)
          (ensures minor_wf minor /\
                   minor_guards_complete minor /\
                   minor_infix_wf minor /\
                   minor_no_scan_invariant minor /\
                   minor_fields_no_infix_targets minor)
  = reveal_opaque (`%minor_heap_shape) (minor_heap_shape minor)

let minor_major_fields_no_blue_elim (minor: minor_state) (major: heap)
  (obj: U64.t) (j: nat)
  : Lemma (requires minor_major_fields_no_blue minor major /\
                     Seq.mem obj (minor_objects minor) /\
                     j < minor_wosize minor obj /\
                     is_pointer_field (minor_read_field minor obj j))
          (ensures Seq.mem ((minor_read_field minor obj j) <: obj_addr)
                            (objects zero_addr major) /\
                   ~(is_blue ((minor_read_field minor obj j) <: obj_addr) major))
  = reveal_opaque (`%minor_major_fields_no_blue)
      (minor_major_fields_no_blue minor major)

let minor_fields_no_infix_targets_elim (minor: minor_state)
  (obj: U64.t) (j: nat)
  : Lemma (requires minor_fields_no_infix_targets minor /\
                     Seq.mem obj (minor_objects minor) /\
                     j < minor_wosize minor obj /\
                     is_minor_pointer (to_minor_offset (minor_read_field minor obj j)))
          (ensures ~(is_infix_in_minor minor
                      (to_minor_offset (minor_read_field minor obj j))))
  = reveal_opaque (`%minor_fields_no_infix_targets)
      (minor_fields_no_infix_targets minor)

let major_minor_fields_no_infix_targets_elim
  (minor: minor_state) (major: heap) (obj: obj_addr) (j: nat)
  : Lemma (requires major_minor_fields_no_infix_targets minor major /\
                     Seq.mem obj (objects zero_addr major) /\
                     ~(is_blue obj major) /\
                     ~(is_no_scan obj major) /\
                     j < U64.v (wosize_of_object obj major) /\
                     U64.v obj + j * 8 + 8 <= heap_size /\
                     (U64.v obj + j * 8) % 8 == 0 /\
                     (let v = to_minor_offset
                        (read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
                      is_minor_pointer v))
          (ensures (let v = to_minor_offset
                        (read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
                    ~(is_infix_in_minor minor v)))
  = reveal_opaque (`%major_minor_fields_no_infix_targets)
      (major_minor_fields_no_infix_targets minor major)

let major_stack_shape_elim (major: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires major_stack_shape major st cap)
          (ensures MarkBoundedInv.bounded_mark_inv major st cap /\
                   Mark.root_props major st /\
                   gray_black_objects_on_stack major st /\
                   (let graph = HeapModel.create_graph major in
                    let roots' = HeapGraph.coerce_to_vertex_list st in
                    Graph.graph_wf graph /\ Graph.is_vertex_set roots' /\
                    Graph.subset_vertices roots' graph.vertices))
  = reveal_opaque (`%major_stack_shape) (major_stack_shape major st cap)

let collection_heap_shape_elim (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires collection_heap_shape minor major fp)
          (ensures major_heap_shape major fp /\
                   minor_heap_shape minor /\
                   minor_major_fields_no_blue minor major /\
                   major_minor_fields_no_infix_targets minor major)
  = reveal_opaque (`%collection_heap_shape)
      (collection_heap_shape minor major fp)

let full_heap_shape_elim (minor: minor_state) (major: heap) (fp: U64.t)
                         (st: seq obj_addr) (cap: nat)
  : Lemma (requires full_heap_shape minor major fp st cap)
          (ensures collection_heap_shape minor major fp /\
                   major_stack_shape major st cap)
  = reveal_opaque (`%full_heap_shape)
      (full_heap_shape minor major fp st cap)
