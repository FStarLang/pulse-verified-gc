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
module SpecMajorAllocMultiAlloc = GC.Spec.MajorAllocator.MultiAlloc
module PromotionDemand = GC.Gen.PromotionDemand
module CG = GC.Gen.CombinedGraph

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

val chunked_is_blue_header
  : mh:MH.major_heap -> obj:obj_addr -> hdr:U64.t ->
    Lemma
      (requires MH.read_word_in_major mh (hd_address obj) == Some hdr)
      (ensures chunked_is_blue mh obj == (getColor hdr = GC.Lib.Header.Blue))

val chunked_is_black
  : mh:MH.major_heap -> obj:obj_addr -> GTot bool

val chunked_is_black_header
  : mh:MH.major_heap -> obj:obj_addr -> hdr:U64.t ->
    Lemma
      (requires MH.read_word_in_major mh (hd_address obj) == Some hdr)
      (ensures chunked_is_black mh obj == (getColor hdr = GC.Lib.Header.Black))

/// Chunked-major counterpart of `Mark.no_black_objects`: no active major object
/// is black at the start of collection/promotion.
[@@"opaque_to_smt"]
val chunked_no_black_objects
  : mh:MH.major_heap -> Tot prop

/// Chunked-major counterpart of `no_scan_invariant`: non-blue no-scan major
/// objects contain no pointer-looking field words.
[@@"opaque_to_smt"]
val chunked_no_scan_invariant
  : mh:MH.major_heap -> Tot prop

/// Chunked-major counterpart of `Mark.no_pointer_to_blue`: a field of a
/// non-blue active major object cannot point to an active blue major object.
[@@"opaque_to_smt"]
val chunked_no_pointer_to_blue
  : mh:MH.major_heap -> Tot prop

/// Chunked-major counterpart of `chain_objects_blue`: every active non-blue
/// object is avoided by the free-list chain. This is kept separate from
/// `chunked_major_alloc_shape` until all update/collection preservation lemmas
/// are ported to the chunked heap.
[@@"opaque_to_smt"]
val chunked_chain_objects_blue
  : mh:MH.major_heap -> fp:U64.t -> fuel:nat -> Tot prop

/// Chunked-major counterpart of `minor_major_fields_no_blue`: any minor field
/// that looks like a major pointer must target an active non-blue major object.
[@@"opaque_to_smt"]
val chunked_minor_major_fields_no_blue
  : minor:minor_state -> mh:MH.major_heap -> Tot prop

/// Chunked-major counterpart of `major_minor_fields_no_infix_targets`: fields
/// of active, non-blue, scannable major objects that still hold minor pointers
/// must not point at minor infix sub-objects.
[@@"opaque_to_smt"]
val chunked_major_minor_fields_no_infix_targets
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

/// Chunked non-stack combined heap shape for preflight minor collection:
/// allocator/free-list facts over the chunked major heap, dense minor-heap
/// facts, and the chunked cross-generation field restrictions.
[@@"opaque_to_smt"]
val chunked_collection_heap_shape
  : minor:minor_state -> mh:MH.major_heap -> fp:U64.t -> fuel:nat ->
    Tot prop

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

val chunked_major_alloc_shape_ensure_head_capacity
  : mh:MH.major_heap -> fp:U64.t -> fuel:nat -> needed:nat{needed > 0} ->
    fresh:MH.heap_chunk ->
    Lemma
      (requires chunked_major_alloc_shape mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= needed))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        chunked_major_alloc_shape
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed))

val chunked_major_alloc_shape_active_head_split
  : mh:MH.major_heap -> fp:U64.t ->
    requested_wz:nat -> fuel:nat ->
    Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                requested_wz > 0 /\
                chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  requested_wz + 2)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             mh fp requested_wz fuel in
         r.major_obj_out == fp /\
         r.major_fp_out <> 0UL /\
         SpecMajorAlloc.major_alloc_result_fp_in_objects r /\
         chunked_major_alloc_shape
           r.major_alloc_out r.major_fp_out fuel))

val chunked_major_alloc_shape_alloc_list_head_split
  : mh:MH.major_heap -> fp:U64.t -> fuel:nat ->
    requests:list nat ->
    Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  SpecMajorAllocMultiAlloc.allocation_list_demand requests + 1)
      (ensures
        (let r =
           SpecMajorAllocMultiAlloc.major_alloc_list_spec
             mh fp fuel requests in
         r.list_fp_out <> 0UL /\
         chunked_major_alloc_shape r.list_major_out r.list_fp_out fuel /\
         SpecMajorAlloc.major_fl_head_wosize
           r.list_major_out r.list_fp_out >= 1 /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.list_objs_out))

val chunked_major_alloc_shape_alloc_list_head_split_with_budget
  : mh:MH.major_heap -> fp:U64.t -> fuel:nat ->
    requests:list nat -> budget:nat ->
    Lemma
      (requires fuel > 1 /\
               fp <> 0UL /\
               chunked_major_alloc_shape mh fp fuel /\
               SpecMajorAllocMultiAlloc.all_requests_positive requests /\
               SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                 budget /\
               SpecMajorAlloc.major_fl_head_wosize mh fp >= budget + 1)
      (ensures
        (let r =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            mh fp fuel requests in
         r.list_fp_out <> 0UL /\
         chunked_major_alloc_shape r.list_major_out r.list_fp_out fuel /\
         SpecMajorAlloc.major_fl_head_wosize
          r.list_major_out r.list_fp_out >= 1 /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          r.list_objs_out))

val chunked_major_alloc_shape_alloc_minor_objects_head_split
  : minor:minor_state -> mh:MH.major_heap -> fp:U64.t ->
    fuel:nat ->
    Lemma
      (requires fuel > 1 /\
                minor_wf minor /\
                fp <> 0UL /\
                chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let requests = PromotionDemand.minor_promotion_requests minor in
         let r =
           SpecMajorAllocMultiAlloc.major_alloc_list_spec
             mh fp fuel requests in
         r.list_fp_out <> 0UL /\
         chunked_major_alloc_shape r.list_major_out r.list_fp_out fuel /\
         SpecMajorAlloc.major_fl_head_wosize
           r.list_major_out r.list_fp_out >= 1 /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.list_objs_out))

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

val chunked_no_black_objects_intro
  : mh:MH.major_heap ->
    Lemma
      (requires
        (forall (obj:obj_addr).
          Seq.mem obj (MH.major_objects mh) ==>
          ~(chunked_is_black mh obj)))
      (ensures chunked_no_black_objects mh)

val chunked_no_black_objects_elim
  : mh:MH.major_heap -> obj:obj_addr ->
    Lemma
      (requires chunked_no_black_objects mh /\
                Seq.mem obj (MH.major_objects mh))
      (ensures ~(chunked_is_black mh obj))

val chunked_is_black_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    obj:obj_addr ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                Seq.mem obj (MH.major_objects mh))
      (ensures
        chunked_is_black
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        chunked_is_black mh obj)

val chunked_no_black_objects_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    Lemma
      (requires chunked_no_black_objects mh /\
                MH.chunk_disjoint_from_all fresh mh)
      (ensures
        chunked_no_black_objects
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)

val chunked_no_black_objects_ensure_capacity
  : mh:MH.major_heap ->
    fp:obj_addr -> fuel:nat -> needed:nat -> fresh:MH.heap_chunk ->
    Lemma
      (requires chunked_no_black_objects mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh))
      (ensures
        chunked_no_black_objects
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)

val chunked_major_minor_fields_no_infix_targets_intro
  : minor:minor_state -> mh:MH.major_heap ->
    Lemma
      (requires
        (forall (obj:obj_addr) (j:nat) (field_addr:hp_addr) (raw:U64.t).
          Seq.mem obj (MH.major_objects mh) /\
          ~(chunked_is_blue mh obj) /\
          ~(CG.chunked_is_no_scan mh obj) /\
          j < CG.chunked_wosize_nat_of_object mh obj /\
          CG.chunked_major_field_slot obj j == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw /\
          is_minor_pointer (to_minor_offset raw) ==>
          ~(is_infix_in_minor minor (to_minor_offset raw))))
      (ensures chunked_major_minor_fields_no_infix_targets minor mh)

val chunked_major_minor_fields_no_infix_targets_elim
  : minor:minor_state -> mh:MH.major_heap ->
    obj:obj_addr -> j:nat -> field_addr:hp_addr -> raw:U64.t ->
    Lemma
      (requires
        chunked_major_minor_fields_no_infix_targets minor mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ~(chunked_is_blue mh obj) /\
        ~(CG.chunked_is_no_scan mh obj) /\
        j < CG.chunked_wosize_nat_of_object mh obj /\
        CG.chunked_major_field_slot obj j == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw /\
        is_minor_pointer (to_minor_offset raw))
      (ensures ~(is_infix_in_minor minor (to_minor_offset raw)))

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

val chunked_major_minor_fields_no_infix_targets_preserved_by_expansion
  : minor:minor_state -> mh:MH.major_heap ->
    fresh:MH.heap_chunk -> fp:U64.t ->
    Lemma
      (requires chunked_major_minor_fields_no_infix_targets minor mh /\
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures
        chunked_major_minor_fields_no_infix_targets minor
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

val chunked_major_minor_fields_no_infix_targets_ensure_capacity
  : minor:minor_state -> mh:MH.major_heap ->
    fp:obj_addr -> fuel:nat -> needed:nat -> fresh:MH.heap_chunk ->
    Lemma
      (requires chunked_major_minor_fields_no_infix_targets minor mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        chunked_major_minor_fields_no_infix_targets minor
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)

val chunked_no_scan_invariant_intro
  : mh:MH.major_heap ->
    Lemma
      (requires
        (forall (src:obj_addr) (idx:nat) (field_addr:hp_addr) (raw:U64.t).
          Seq.mem src (MH.major_objects mh) /\
          CG.chunked_is_no_scan mh src /\
          ~(chunked_is_blue mh src) /\
          idx < CG.chunked_wosize_nat_of_object mh src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw ==>
          ~(is_pointer_field raw)))
      (ensures chunked_no_scan_invariant mh)

val chunked_no_scan_invariant_elim
  : mh:MH.major_heap ->
    src:obj_addr -> idx:nat -> field_addr:hp_addr -> raw:U64.t ->
    Lemma
      (requires chunked_no_scan_invariant mh /\
                Seq.mem src (MH.major_objects mh) /\
                CG.chunked_is_no_scan mh src /\
                ~(chunked_is_blue mh src) /\
                idx < CG.chunked_wosize_nat_of_object mh src /\
                CG.chunked_major_field_slot src idx == Some field_addr /\
                MH.read_word_in_major mh field_addr == Some raw)
      (ensures ~(is_pointer_field raw))

val chunked_no_scan_invariant_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    Lemma
      (requires chunked_no_scan_invariant mh /\
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures
        chunked_no_scan_invariant
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)

val chunked_no_scan_invariant_ensure_capacity
  : mh:MH.major_heap ->
    fp:obj_addr -> fuel:nat -> needed:nat -> fresh:MH.heap_chunk ->
    Lemma
      (requires chunked_no_scan_invariant mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        chunked_no_scan_invariant
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)

val chunked_no_pointer_to_blue_intro
  : mh:MH.major_heap ->
    Lemma
      (requires
        (forall (src:obj_addr) (dst:obj_addr) (idx:nat)
                (field_addr:hp_addr) (raw:U64.t).
          Seq.mem src (MH.major_objects mh) /\
          ~(chunked_is_blue mh src) /\
          idx < CG.chunked_wosize_nat_of_object mh src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw /\
          Seq.mem dst (MH.major_objects mh) /\
          is_pointer_to raw dst ==>
          ~(chunked_is_blue mh dst)))
      (ensures chunked_no_pointer_to_blue mh)

val chunked_no_pointer_to_blue_elim
  : mh:MH.major_heap ->
    src:obj_addr -> dst:obj_addr -> idx:nat ->
    field_addr:hp_addr -> raw:U64.t ->
    Lemma
      (requires chunked_no_pointer_to_blue mh /\
                Seq.mem src (MH.major_objects mh) /\
                ~(chunked_is_blue mh src) /\
                idx < CG.chunked_wosize_nat_of_object mh src /\
                CG.chunked_major_field_slot src idx == Some field_addr /\
                MH.read_word_in_major mh field_addr == Some raw /\
                Seq.mem dst (MH.major_objects mh) /\
                is_pointer_to raw dst)
      (ensures ~(chunked_is_blue mh dst))

val chunked_chain_objects_blue_intro
  : mh:MH.major_heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires
        (forall (obj:obj_addr).
          Seq.mem obj (MH.major_objects mh) /\
          ~(chunked_is_blue mh obj) ==>
          SpecMajorAlloc.major_fl_chain_avoids mh fp obj fuel = true))
      (ensures chunked_chain_objects_blue mh fp fuel)

val chunked_chain_objects_blue_elim
  : mh:MH.major_heap -> fp:U64.t -> fuel:nat -> obj:obj_addr ->
    Lemma
      (requires chunked_chain_objects_blue mh fp fuel /\
                Seq.mem obj (MH.major_objects mh) /\
                ~(chunked_is_blue mh obj))
      (ensures
        SpecMajorAlloc.major_fl_chain_avoids mh fp obj fuel = true)

val chunked_chain_objects_blue_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires chunked_chain_objects_blue mh fp fuel /\
                MH.well_formed_major_heap mh /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                MH.chunk_disjoint_from_all fresh mh)
      (ensures
        (let r = SpecMajorAlloc.expand_major_heap mh fresh fp in
         chunked_chain_objects_blue r.major_out r.fp_out (fuel + 1)))

val chunked_chain_objects_blue_ensure_head_capacity
  : mh:MH.major_heap -> fp:U64.t -> fuel:nat ->
    needed:nat{needed > 0} -> fresh:MH.heap_chunk ->
    Lemma
      (requires chunked_chain_objects_blue mh fp fuel /\
                MH.well_formed_major_heap mh /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh))
      (ensures
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
         chunked_chain_objects_blue
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))

val chunked_no_pointer_to_blue_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    Lemma
      (requires chunked_no_pointer_to_blue mh /\
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures
        chunked_no_pointer_to_blue
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)

val chunked_no_pointer_to_blue_ensure_capacity
  : mh:MH.major_heap ->
    fp:obj_addr -> fuel:nat -> needed:nat -> fresh:MH.heap_chunk ->
    Lemma
      (requires chunked_no_pointer_to_blue mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        chunked_no_pointer_to_blue
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)

val chunked_collection_heap_shape_intro
  : minor:minor_state -> mh:MH.major_heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires chunked_major_alloc_shape mh fp fuel /\
                chunked_no_black_objects mh /\
                chunked_no_scan_invariant mh /\
                chunked_no_pointer_to_blue mh /\
                minor_heap_shape minor /\
                chunked_minor_major_fields_no_blue minor mh /\
                chunked_major_minor_fields_no_infix_targets minor mh)
      (ensures chunked_collection_heap_shape minor mh fp fuel)

val chunked_collection_heap_shape_elim
  : minor:minor_state -> mh:MH.major_heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires chunked_collection_heap_shape minor mh fp fuel)
      (ensures chunked_major_alloc_shape mh fp fuel /\
               chunked_no_black_objects mh /\
               chunked_no_scan_invariant mh /\
               chunked_no_pointer_to_blue mh /\
               minor_heap_shape minor /\
               chunked_minor_major_fields_no_blue minor mh /\
               chunked_major_minor_fields_no_infix_targets minor mh)

val chunked_collection_heap_shape_preserved_by_expansion
  : minor:minor_state -> mh:MH.major_heap ->
    fresh:MH.heap_chunk -> fp:obj_addr -> fuel:nat ->
    Lemma
      (requires chunked_collection_heap_shape minor mh fp fuel /\
                MH.chunk_disjoint_from_all fresh mh /\
                fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                U64.v fresh.base >= U64.v zero_addr /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures (
        let r = SpecMajorAlloc.expand_major_heap mh fresh fp in
        chunked_collection_heap_shape minor r.major_out r.fp_out (fuel + 1)))

val chunked_collection_heap_shape_ensure_capacity
  : minor:minor_state -> mh:MH.major_heap ->
    fp:obj_addr -> fuel:nat -> needed:nat -> fresh:MH.heap_chunk ->
    Lemma
      (requires chunked_collection_heap_shape minor mh fp fuel /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh +
                   SpecMajorAlloc.major_fl_capacity mh fp fuel >= needed /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh in
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_capacity
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out >= needed))

val chunked_collection_heap_shape_ensure_head_capacity
  : minor:minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> needed:nat{needed > 0} -> fresh:MH.heap_chunk ->
    Lemma
      (requires chunked_collection_heap_shape minor mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed))

val chunked_collection_heap_shape_ensure_head_capacity_with_chain
  : minor:minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> needed:nat{needed > 0} -> fresh:MH.heap_chunk ->
    Lemma
      (requires chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        SpecMajorAlloc.major_fl_chain_terminates
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out = true))

val chunked_collection_heap_shape_ensure_head_capacity_with_chain_blue
  : minor:minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> needed:nat{needed > 0} -> fresh:MH.heap_chunk ->
    Lemma
      (requires chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
                chunked_chain_objects_blue mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        SpecMajorAlloc.major_fl_chain_terminates
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out = true /\
        chunked_chain_objects_blue
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))

val chunked_collection_heap_shape_ensure_head_capacity_with_chain_blue_value_safety
  : minor:minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> needed:nat{needed > 0} -> fresh:MH.heap_chunk ->
    Lemma
      (requires chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
                chunked_chain_objects_blue mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
                 (forall (obj:obj_addr).
                  Seq.mem obj (MH.major_objects mh) ==>
                    CG.chunked_major_field_values_miss_fresh
                      mh fresh obj (CG.chunked_wosize_nat_of_object mh obj) 0)))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        SpecMajorAlloc.major_fl_chain_terminates
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out = true /\
        chunked_chain_objects_blue
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))

val chunked_collection_heap_shape_ensure_head_capacity_alloc_no_oom
  : minor:minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> requested_wz:nat -> fresh:MH.heap_chunk ->
    Lemma
      (requires fuel > 0 /\
                chunked_collection_heap_shape minor mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   SpecMajorAlloc.major_alloc_demand_wosize requested_wz ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   SpecMajorAlloc.major_alloc_demand_wosize requested_wz /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let needed = SpecMajorAlloc.major_alloc_demand_wosize requested_wz in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let a =
          SpecMajorAlloc.major_alloc_spec_with_fuel
            r.capacity_major_out r.capacity_fp_out requested_wz
            r.capacity_fuel_out in
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.major_obj_out == r.capacity_fp_out /\
        a.major_obj_out <> 0UL))

val chunked_collection_heap_shape_ensure_head_capacity_alloc_list_with_budget
  : minor:minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> fresh:MH.heap_chunk ->
    requests:list nat -> budget:nat ->
    Lemma
      (requires fuel > 1 /\
                chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  budget /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < budget + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= budget + 1 /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let needed = budget + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))

val chunked_collection_heap_shape_ensure_head_capacity_alloc_list_with_budget_value_safety
  : minor:minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> fresh:MH.heap_chunk ->
    requests:list nat -> budget:nat ->
    Lemma
      (requires fuel > 1 /\
                chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  budget /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < budget + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= budget + 1 /\
                 (forall (obj:obj_addr).
                  Seq.mem obj (MH.major_objects mh) ==>
                    CG.chunked_major_field_values_miss_fresh
                      mh fresh obj (CG.chunked_wosize_nat_of_object mh obj) 0)))
      (ensures (
        let needed = budget + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))

val chunked_collection_heap_shape_ensure_minor_promotion_budget_alloc_list
  : minor:minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> fresh:MH.heap_chunk ->
    requests:list nat ->
    Lemma
      (requires fuel > 1 /\
                chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  PromotionDemand.minor_promotion_demand minor /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   PromotionDemand.minor_promotion_demand minor + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   PromotionDemand.minor_promotion_demand minor + 1 /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let needed = PromotionDemand.minor_promotion_demand minor + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))

val chunked_collection_heap_shape_ensure_minor_promotion_budget_alloc_list_value_safety
  : minor:minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> fresh:MH.heap_chunk ->
    requests:list nat ->
    Lemma
      (requires fuel > 1 /\
                chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  PromotionDemand.minor_promotion_demand minor /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   PromotionDemand.minor_promotion_demand minor + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   PromotionDemand.minor_promotion_demand minor + 1 /\
                 (forall (obj:obj_addr).
                  Seq.mem obj (MH.major_objects mh) ==>
                    CG.chunked_major_field_values_miss_fresh
                      mh fresh obj (CG.chunked_wosize_nat_of_object mh obj) 0)))
      (ensures (
        let needed = PromotionDemand.minor_promotion_demand minor + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))

val chunked_collection_heap_shape_ensure_minor_promotion_head_capacity_allocs
  : minor:minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> fresh:MH.heap_chunk ->
    Lemma
      (requires fuel > 1 /\
                chunked_collection_heap_shape minor mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   PromotionDemand.minor_promotion_demand minor + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   PromotionDemand.minor_promotion_demand minor + 1 /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let needed = PromotionDemand.minor_promotion_demand minor + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let requests = PromotionDemand.minor_promotion_requests minor in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))

val chunked_collection_heap_shape_ensure_minor_promotion_head_capacity_allocs_value_safety
  : minor:minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> fresh:MH.heap_chunk ->
    Lemma
      (requires fuel > 1 /\
                chunked_collection_heap_shape minor mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   PromotionDemand.minor_promotion_demand minor + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   PromotionDemand.minor_promotion_demand minor + 1 /\
                 (forall (obj:obj_addr).
                  Seq.mem obj (MH.major_objects mh) ==>
                    CG.chunked_major_field_values_miss_fresh
                      mh fresh obj (CG.chunked_wosize_nat_of_object mh obj) 0)))
      (ensures (
        let needed = PromotionDemand.minor_promotion_demand minor + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let requests = PromotionDemand.minor_promotion_requests minor in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))

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
