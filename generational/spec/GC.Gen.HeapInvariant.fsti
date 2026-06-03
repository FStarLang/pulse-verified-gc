/// ---------------------------------------------------------------------------
/// GC.Gen.HeapInvariant -- Central generational heap-shape invariant
/// ---------------------------------------------------------------------------
///
/// This module is the single summary point for the full generational heap shape.
/// It names the major-heap layout/free-list/color invariants, the minor-heap
/// layout invariants, and the cross-generation condition needed when minor
/// objects are promoted into the major heap.

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
module MH = GC.Spec.MajorHeap
module SpecMajorAlloc = GC.Spec.MajorAllocator

/// Major-heap shape needed by both minor collection and the following major GC:
/// object layout/infix well-formedness, free-list validity, color invariants,
/// and the no-scan/no-pointer-to-blue safety conditions.
[@@"opaque_to_smt"]
val major_heap_shape (major: heap) (fp: U64.t) : prop

/// Chunked allocator-facing major-heap shape. This is the growable-heap
/// counterpart of the free-list portion of `major_heap_shape`; color/mark/sweep
/// invariants are lifted separately as the collector is ported to chunked
/// object enumeration.
[@@"opaque_to_smt"]
val chunked_major_alloc_shape
  : mh:MH.major_heap -> fp:U64.t -> fuel:nat -> Tot prop

/// Read the color of an object header through the chunked-major heap, if the
/// header word is currently in an active chunk.
val chunked_color_of_object
  : mh:MH.major_heap -> obj:obj_addr -> GTot (option color)

val chunked_is_blue
  : mh:MH.major_heap -> obj:obj_addr -> GTot bool

/// Chunked-major counterpart of `minor_major_fields_no_blue`: any minor field
/// that looks like a major pointer must target an active non-blue major object.
[@@"opaque_to_smt"]
val chunked_minor_major_fields_no_blue
  : minor:minor_state -> mh:MH.major_heap -> Tot prop

/// Cross-generation safety: any field of an allocated minor object that already
/// looks like a major-heap pointer must target a live non-blue major object.
/// This is what lets promotion preserve `Mark.no_pointer_to_blue`.
[@@"opaque_to_smt"]
val minor_major_fields_no_blue (minor: minor_state) (major: heap) : prop

/// Minor object fields that contain minor-heap pointers must not point at
/// minor infix sub-objects.  Forwarding an infix sub-object produces an interior
/// major pointer, which is valid for roots but not for major object fields under
/// the current `well_formed_heap_part2` model.
[@@"opaque_to_smt"]
val minor_fields_no_infix_targets (minor: minor_state) : prop

/// Existing major-heap fields that temporarily contain minor pointers (e.g. via
/// write barriers) also must not point at minor infix sub-objects, for the same
/// reason as `minor_fields_no_infix_targets`.
[@@"opaque_to_smt"]
val major_minor_fields_no_infix_targets (minor: minor_state) (major: heap) : prop

/// Minor-heap shape: bump/layout validity, runtime guard completeness, infix
/// validity, the minor analogue of the no-scan raw-data invariant, and the
/// field-level restriction that prevents storing forwarded infix pointers in
/// major object bodies.
[@@"opaque_to_smt"]
val minor_heap_shape (minor: minor_state) : prop

/// Named form of the gray/black stack condition, centralized here so clients do
/// not have to rediscover the color-stack conjunct of the major GC precondition.
let gray_black_objects_on_stack (major: heap) (st: seq obj_addr) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (objects zero_addr major) /\
    (is_gray obj major \/ is_black obj major) ==> Seq.mem obj st

/// Stack-coupled major-GC facts: bounded mark invariant, root validity, the
/// gray/black stack condition, and graph/root well-formedness.
[@@"opaque_to_smt"]
val major_stack_shape (major: heap) (st: seq obj_addr) (cap: nat) : prop

/// Non-stack combined heap shape used by minor collection.
[@@"opaque_to_smt"]
val collection_heap_shape (minor: minor_state) (major: heap) (fp: U64.t) : prop

/// Full combined heap shape used by `gen_gc`.
[@@"opaque_to_smt"]
val full_heap_shape (minor: minor_state) (major: heap) (fp: U64.t)
                    (st: seq obj_addr) (cap: nat) : prop

val major_heap_shape_intro (major: heap) (fp: U64.t)
  : Lemma (requires well_formed_heap major /\
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
          (ensures major_heap_shape major fp)

val major_heap_shape_elim (major: heap) (fp: U64.t)
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

val chunked_major_alloc_shape_intro
  : mh:MH.major_heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires MH.well_formed_major_heap mh /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit mh fp fuel)
      (ensures chunked_major_alloc_shape mh fp fuel)

val chunked_major_alloc_shape_elim
  : mh:MH.major_heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires chunked_major_alloc_shape mh fp fuel)
      (ensures MH.well_formed_major_heap mh /\
               SpecMajorAlloc.major_fl_valid mh fp fuel /\
               SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
               SpecMajorAlloc.major_fl_blocks_fit mh fp fuel)

val chunked_major_alloc_shape_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:obj_addr -> fuel:nat ->
    Lemma
      (requires chunked_major_alloc_shape mh fp fuel /\
                MH.chunk_disjoint_from_all fresh mh /\
                fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                U64.v fresh.base >= U64.v zero_addr)
      (ensures (
        let r = SpecMajorAlloc.expand_major_heap mh fresh fp in
        chunked_major_alloc_shape r.major_out r.fp_out (fuel + 1)))

val chunked_major_alloc_shape_ensure_capacity
  : mh:MH.major_heap -> fp:obj_addr -> fuel:nat -> needed:nat ->
    fresh:MH.heap_chunk ->
    Lemma
      (requires chunked_major_alloc_shape mh fp fuel /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh +
                   SpecMajorAlloc.major_fl_capacity mh fp fuel >= needed))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh in
        chunked_major_alloc_shape
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_capacity
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out >= needed))

val chunked_minor_major_fields_no_blue_intro
  : minor:minor_state -> mh:MH.major_heap ->
    Lemma
      (requires
        (forall (obj: U64.t) (j: nat).
          Seq.mem obj (minor_objects minor) /\
          j < minor_wosize minor obj /\
          is_pointer_field (minor_read_field minor obj j) ==>
          Seq.mem ((minor_read_field minor obj j) <: obj_addr)
                  (MH.major_objects mh) /\
          ~(chunked_is_blue mh
              ((minor_read_field minor obj j) <: obj_addr))))
      (ensures chunked_minor_major_fields_no_blue minor mh)

val chunked_minor_major_fields_no_blue_no_pointer_fields
  : minor:minor_state -> mh:MH.major_heap ->
    Lemma
      (requires
        (forall (obj:U64.t) (j:nat).
          Seq.mem obj (minor_objects minor) /\
          j < minor_wosize minor obj ==>
          ~(is_pointer_field (minor_read_field minor obj j))))
      (ensures chunked_minor_major_fields_no_blue minor mh)

val chunked_minor_major_fields_no_blue_elim
  : minor:minor_state -> mh:MH.major_heap ->
    obj:U64.t -> j:nat ->
    Lemma
      (requires chunked_minor_major_fields_no_blue minor mh /\
                Seq.mem obj (minor_objects minor) /\
                j < minor_wosize minor obj /\
                is_pointer_field (minor_read_field minor obj j))
      (ensures
        Seq.mem ((minor_read_field minor obj j) <: obj_addr)
                (MH.major_objects mh) /\
        ~(chunked_is_blue mh
            ((minor_read_field minor obj j) <: obj_addr)))

val chunked_is_blue_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    obj:obj_addr ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                Seq.mem obj (MH.major_objects mh))
      (ensures
        chunked_is_blue
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        chunked_is_blue mh obj)

val chunked_minor_major_fields_no_blue_preserved_by_expansion
  : minor:minor_state -> mh:MH.major_heap ->
    fresh:MH.heap_chunk -> fp:U64.t ->
    Lemma
      (requires chunked_minor_major_fields_no_blue minor mh /\
                MH.chunk_disjoint_from_all fresh mh)
      (ensures
        chunked_minor_major_fields_no_blue minor
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)

val chunked_minor_major_fields_no_blue_ensure_capacity
  : minor:minor_state -> mh:MH.major_heap ->
    fp:obj_addr -> fuel:nat -> needed:nat -> fresh:MH.heap_chunk ->
    Lemma
      (requires chunked_minor_major_fields_no_blue minor mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh))
      (ensures
        chunked_minor_major_fields_no_blue minor
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)

val minor_heap_shape_elim (minor: minor_state)
  : Lemma (requires minor_heap_shape minor)
           (ensures minor_wf minor /\
                    minor_guards_complete minor /\
                    minor_infix_wf minor /\
                    minor_no_scan_invariant minor /\
                    minor_fields_no_infix_targets minor)

val minor_fields_no_infix_targets_intro (minor: minor_state)
  : Lemma (requires
            (forall (obj: U64.t) (j: nat).
              Seq.mem obj (minor_objects minor) /\
              j < minor_wosize minor obj /\
              is_minor_pointer (to_minor_offset (minor_read_field minor obj j)) ==>
              ~(is_infix_in_minor minor
                  (to_minor_offset (minor_read_field minor obj j)))))
          (ensures minor_fields_no_infix_targets minor)

val minor_heap_shape_intro (minor: minor_state)
  : Lemma (requires minor_wf minor /\
                    minor_guards_complete minor /\
                    minor_infix_wf minor /\
                    minor_no_scan_invariant minor /\
                    minor_fields_no_infix_targets minor)
          (ensures minor_heap_shape minor)

val minor_major_fields_no_blue_intro (minor: minor_state) (major: heap)
  : Lemma (requires
            (forall (obj: U64.t) (j: nat).
              Seq.mem obj (minor_objects minor) /\
              j < minor_wosize minor obj /\
              is_pointer_field (minor_read_field minor obj j) ==>
              Seq.mem ((minor_read_field minor obj j) <: obj_addr)
                     (objects zero_addr major) /\
              ~(is_blue ((minor_read_field minor obj j) <: obj_addr) major)))
          (ensures minor_major_fields_no_blue minor major)

val minor_major_fields_no_blue_no_pointer_fields
  : minor:minor_state -> major:heap ->
    Lemma
      (requires
        (forall (obj:U64.t) (j:nat).
          Seq.mem obj (minor_objects minor) /\
          j < minor_wosize minor obj ==>
          ~(is_pointer_field (minor_read_field minor obj j))))
      (ensures minor_major_fields_no_blue minor major)

val minor_major_fields_no_blue_elim (minor: minor_state) (major: heap)
  (obj: U64.t) (j: nat)
  : Lemma (requires minor_major_fields_no_blue minor major /\
                     Seq.mem obj (minor_objects minor) /\
                     j < minor_wosize minor obj /\
                     is_pointer_field (minor_read_field minor obj j))
           (ensures Seq.mem ((minor_read_field minor obj j) <: obj_addr)
                             (objects zero_addr major) /\
                    ~(is_blue ((minor_read_field minor obj j) <: obj_addr) major))

val minor_fields_no_infix_targets_elim (minor: minor_state)
  (obj: U64.t) (j: nat)
  : Lemma (requires minor_fields_no_infix_targets minor /\
                     Seq.mem obj (minor_objects minor) /\
                     j < minor_wosize minor obj /\
                     is_minor_pointer (to_minor_offset (minor_read_field minor obj j)))
          (ensures ~(is_infix_in_minor minor
                      (to_minor_offset (minor_read_field minor obj j))))

val major_minor_fields_no_infix_targets_elim
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

val major_minor_fields_no_infix_targets_intro
  (minor: minor_state) (major: heap)
  : Lemma (requires
            (forall (obj: obj_addr) (j: nat).
              Seq.mem obj (objects zero_addr major) /\
              ~(is_blue obj major) /\
              ~(is_no_scan obj major) /\
              j < U64.v (wosize_of_object obj major) /\
              U64.v obj + j * 8 + 8 <= heap_size /\
              (U64.v obj + j * 8) % 8 == 0 ==>
              (let v = to_minor_offset
                 (read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
               is_minor_pointer v ==> ~(is_infix_in_minor minor v))))
          (ensures major_minor_fields_no_infix_targets minor major)

val major_stack_shape_elim (major: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires major_stack_shape major st cap)
          (ensures MarkBoundedInv.bounded_mark_inv major st cap /\
                   Mark.root_props major st /\
                   gray_black_objects_on_stack major st /\
                   (let graph = HeapModel.create_graph major in
                    let roots' = HeapGraph.coerce_to_vertex_list st in
                    Graph.graph_wf graph /\ Graph.is_vertex_set roots' /\
                    Graph.subset_vertices roots' graph.vertices))

val major_stack_shape_intro (major: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires MarkBoundedInv.bounded_mark_inv major st cap /\
                    Mark.root_props major st /\
                    gray_black_objects_on_stack major st /\
                    (let graph = HeapModel.create_graph major in
                     let roots' = HeapGraph.coerce_to_vertex_list st in
                     Graph.graph_wf graph /\ Graph.is_vertex_set roots' /\
                     Graph.subset_vertices roots' graph.vertices))
          (ensures major_stack_shape major st cap)

val collection_heap_shape_elim (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires collection_heap_shape minor major fp)
           (ensures major_heap_shape major fp /\
                     minor_heap_shape minor /\
                     minor_major_fields_no_blue minor major /\
                    major_minor_fields_no_infix_targets minor major)

val collection_heap_shape_intro (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires major_heap_shape major fp /\
                    minor_heap_shape minor /\
                    minor_major_fields_no_blue minor major /\
                    major_minor_fields_no_infix_targets minor major)
          (ensures collection_heap_shape minor major fp)

val full_heap_shape_elim (minor: minor_state) (major: heap) (fp: U64.t)
                          (st: seq obj_addr) (cap: nat)
  : Lemma (requires full_heap_shape minor major fp st cap)
          (ensures collection_heap_shape minor major fp /\
                    major_stack_shape major st cap)

val full_heap_shape_intro (minor: minor_state) (major: heap) (fp: U64.t)
                          (st: seq obj_addr) (cap: nat)
  : Lemma (requires collection_heap_shape minor major fp /\
                    major_stack_shape major st cap)
          (ensures full_heap_shape minor major fp st cap)

/// Resetting the nursery clears stale headers and makes all minor-side shape
/// and cross-generation minor-pointer obligations vacuous.
val minor_reset_heap_shape (minor: minor_state)
  : Lemma (ensures minor_heap_shape (minor_reset minor))

val minor_reset_minor_major_fields_no_blue (minor: minor_state) (major: heap)
  : Lemma (ensures minor_major_fields_no_blue (minor_reset minor) major)

val minor_reset_major_minor_fields_no_infix_targets
  (minor: minor_state) (major: heap)
  : Lemma (ensures major_minor_fields_no_infix_targets (minor_reset minor) major)

val collection_heap_shape_after_minor_reset
  (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires major_heap_shape major fp)
          (ensures collection_heap_shape (minor_reset minor) major fp)

/// Helper lemma: when there are no minor objects, minor_major_fields_no_blue holds vacuously
val minor_major_fields_no_blue_empty (minor: minor_state) (major: heap)
  : Lemma (requires minor_objects minor == Seq.empty)
          (ensures minor_major_fields_no_blue minor major)
