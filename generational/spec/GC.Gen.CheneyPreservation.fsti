/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation — Additional Cheney BFS preservation lemmas
/// ---------------------------------------------------------------------------
///
/// Separated from GC.Gen.Cheney to avoid Z3 context pollution: adding val
/// declarations to Cheney.fsti causes GC.Gen.Impl.Cheney.fst to fail verification.
/// This module is imported only by CheneyEnd2End, not by the Pulse implementation.

module GC.Gen.CheneyPreservation

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark

/// Cheney promotion preserves no_black_objects.
///
/// Promoted objects get white_bits headers; pre-existing objects' colors are
/// unchanged (alloc_spec and copy_fields only modify the allocated block and
/// free-list headers, never coloring an object black).
val cheney_promote_preserves_no_black
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects major /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_promote minor major fp roots in
                    Mark.no_black_objects res.major_final))

/// ---------------------------------------------------------------------------
/// Forwarding targets classification: in objects or infix
/// ---------------------------------------------------------------------------

/// Every non-zero forwarding target produced by cheney_promote is either
/// an object in the objects list (normal forwarding) or an infix sub-object
/// in the major heap (interior pointer with tag=249).
///
/// Proof sketch (BFS induction):
///   - Normal forwarding via cheney_forward_normal: alloc_spec puts the target
///     in objects (alloc_spec_obj_in_objects_part1). Subsequent allocs preserve
///     membership (cheney_forward_one_preserves_objects).
///   - Infix forwarding: target = parent_fwd + delta. After promote_object
///     copies parent's fields, the infix header at (parent_fwd + delta - 8)
///     has tag=249. Frame: subsequent allocs write to disjoint memory
///     (promote_object_frame_old_field), preserving the infix header.
let fwd_valid_or_infix (fwd: forwarding_map) (g: heap) : prop =
  forall (x: U64.t). fwd x <> 0UL ==>
    (U64.v (fwd x) >= U64.v mword /\
     U64.v (fwd x) < heap_size /\
     U64.v (fwd x) % U64.v mword == 0 /\
     (Seq.mem ((fwd x) <: obj_addr) (objects zero_addr g) \/
      is_infix (fwd x) g))

val cheney_promote_fwd_valid_or_infix
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_valid_or_infix (cheney_promote minor major fp roots).fwd_map
                                      (cheney_promote minor major fp roots).major_final)

/// ---------------------------------------------------------------------------
/// Frame property: cheney_promote preserves fields of pre-existing non-blue objects
/// ---------------------------------------------------------------------------

/// For any non-blue object in the original major heap, its body fields are
/// unchanged after cheney_promote. This is because:
///   - Cheney BFS only writes to newly allocated regions (from the free-list)
///   - Pre-existing non-blue objects are not on the free-list
///   - promote_object_frame_old_field gives per-step field preservation
///   - BFS induction carries this through all promotion steps
val cheney_promote_frame_old_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    Seq.mem obj (objects zero_addr major) /\
                    is_blue obj major = false /\
                    j < U64.v (wosize_of_object obj major) /\
                    U64.v obj + j * 8 + 8 <= heap_size)
          (ensures (let res = cheney_promote minor major fp roots in
                    read_word res.major_final (U64.uint_to_t (U64.v obj + j * 8))
                    == read_word major (U64.uint_to_t (U64.v obj + j * 8))))
