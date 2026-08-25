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

/// Major-heap shape needed by both minor collection and the following major GC:
/// object layout/infix well-formedness, free-list validity, color invariants,
/// and the no-scan/no-pointer-to-blue safety conditions.
///
/// Interior (infix) pointers in *live* major fields are allowed.  A white, gray
/// or black object may hold a pointer into the middle of a closure, which is how
/// OCaml represents mutually recursive functions; parts 2 and 3 of
/// `well_formed_heap` are stated on the resolved target and
/// `GC.Gen.CombinedGraph.classify_major_field` resolves, so such an edge is
/// carried by the combined graph rather than silently dropped.
///
/// The one place interior pointers are still ruled out is `blue_fields_non_infix`:
/// a *free-list cell* may not hold one.  That is not a statement about the
/// mutator's data; it is what makes `GC.Gen.Promote.blue_fields_closed` --- which
/// is stated on the raw field value --- derivable from the resolved part 2, via
/// `GC.Gen.PromoteUpdate.BlueAlloc.wfh_part2_implies_blue_fields_closed`.  It is
/// re-established for free after every collection: the Cheney machinery proves
/// raw part 2 for blue objects, which `blue_fields_non_infix_from_raw` turns
/// straight back into this clause.
///
/// Free cells are already idealised by the surrounding model --- part 2 requires
/// every pointer-shaped word in them to resolve to an enumerated object, garbage
/// or not --- so this adds nothing to what a heap must already satisfy there.
///
/// The nursery side keeps its own restrictions (`minor_fields_no_infix_targets`,
/// `major_minor_fields_no_infix_targets`): a pointer *into the nursery* may not
/// be interior.  Cheney's forwarding map is keyed by whole minor objects, so
/// lifting that is a separate change.
[@@"opaque_to_smt"]
val major_heap_shape (major: heap) (fp: U64.t) : prop

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
/// Non-stack combined heap shape used by minor collection.
[@@"opaque_to_smt"]
val collection_heap_shape (minor: minor_state) (major: heap) (fp: U64.t) : prop
val major_heap_shape_intro (major: heap) (fp: U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    FreeListShape.fp_pointer_or_zero fp /\
                    FreeListShape.blue_link_fields_valid major /\
                    heap_objects_dense major /\
                    chain_objects_blue major fp /\
                    Seq.length (objects zero_addr major) > 0 /\
                    SweepInv.fp_valid fp major /\
                    Sweep.fp_in_heap fp major /\
                    Mark.no_black_objects major /\
                    SweepInv.no_gray_objects major /\
                    Mark.no_pointer_to_blue major /\
                    no_scan_invariant major /\
                    blue_fields_non_infix major)
          (ensures major_heap_shape major fp)

val major_heap_shape_elim (major: heap) (fp: U64.t)
  : Lemma (requires major_heap_shape major fp)
          (ensures well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    FreeListShape.fp_pointer_or_zero fp /\
                    FreeListShape.blue_link_fields_valid major /\
                    heap_objects_dense major /\
                    chain_objects_blue major fp /\
                   Seq.length (objects zero_addr major) > 0 /\
                   SweepInv.fp_valid fp major /\
                   Sweep.fp_in_heap fp major /\
                   Mark.no_black_objects major /\
                   SweepInv.no_gray_objects major /\
                   Mark.no_pointer_to_blue major /\
                   no_scan_invariant major /\
                   blue_fields_non_infix major)

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
