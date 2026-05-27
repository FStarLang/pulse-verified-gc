module GC.SPOT.EmptyHeapLemmas

/// Lemmas proving GC preconditions for empty heaps
///
/// These lemmas show that all 11 GC preconditions hold for:
/// - Empty minor heap (bump = 0)
/// - Major heap = init_heap output (single blue block)
/// - Empty roots array
/// - Empty slots array

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq
module SZ = FStar.SizeT

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Allocator
module SpecAlloc = GC.Spec.Allocator
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.HeapInvariant
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module MinorFwd = GC.Gen.MinorCollectForwarding
module RBridge = GC.Gen.ReachabilityBridge
module MinorZero = GC.SPOT.MinorObjectsZero

/// Precondition 7: Empty slots are pairwise distinct
let empty_slots_distinct
  (slots: Seq.seq U64.t) (nslots: nat)
  : Lemma (requires nslots == 0 /\ Seq.length slots == 0)
          (ensures UpdatePtrs.slots_pairwise_distinct slots nslots)
  = // Unfold definition: pairwise distinct means for all i,j < nslots, i <> j ==> slots[i] <> slots[j]
    // Since nslots == 0, there are no i,j to check, so it's vacuously true
    // Let's check if Z3 proves this automatically
    ()

/// Precondition 10: Empty roots are valid non-blue
let empty_roots_valid_nonblue
  (roots: Seq.seq U64.t) (major: heap)
  : Lemma (requires Seq.length roots == 0)
          (ensures RBridge.roots_valid_nonblue roots major)
  = // Definition: for all i < length roots, roots[i] is valid and non-blue
    // Since length == 0, vacuously true
    ()

/// Precondition 11: Empty roots valid for minor collection
let empty_roots_valid_for_collection
  (minor: minor_state) (major: heap) (roots: Seq.seq U64.t)
  : Lemma (requires Seq.length roots == 0 /\ U64.v minor.bump == 0)
          (ensures MinorFwd.roots_valid_for_minor_collection minor major roots)
  = // Definition involves checking each root - vacuous for empty
    ()

/// Precondition 5: Empty ref table is sound
let empty_ref_table_sound
  (major: heap) (slots: Seq.seq U64.t) (nslots: nat)
  : Lemma (requires nslots == 0 /\ Seq.length slots == 0)
          (ensures UpdatePtrs.ref_table_sound major slots nslots)
  = // Definition: slots correctly describe major→minor pointers
    // Empty slots make no claims, so vacuously sound
    ()

/// Precondition 6: Empty ref table covers all minor ptrs
let empty_ref_table_covers
  (major: heap) (slots: Seq.seq U64.t) (nslots: nat)
  : Lemma (requires nslots == 0)
          (ensures UpdatePtrs.ref_table_covers_minor_ptrs major slots nslots)
  = // Definition: all major→minor pointers are in slots
    // Need to prove: for any major→minor pointer, it's in slots
    // Since slots is empty, we need to show there ARE no major→minor pointers
    // in the init_heap case (single blue block with no fields)
    admit() // TODO: Not automatic - need to unfold definition

/// Precondition 8: Empty remembered set targets in roots
let empty_remembered_targets
  (major: heap) (roots: Seq.seq U64.t) (slots: Seq.seq U64.t) (nslots: nat)
  : Lemma (requires nslots == 0)
          (ensures MinorFwd.remembered_targets_in_roots major roots slots nslots)
  = // Definition: targets of slots pointers are in roots
    // Since nslots == 0, vacuously true
    admit() // TODO: Not automatic - need to unfold

/// Precondition 9: Major fields satisfy constraints
/// For init_heap (single blue block), need to check field constraints
let init_heap_major_field_zero_no_minor
  (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires (major, fp) == SpecAlloc.init_heap_spec (Seq.create heap_size 0uy) /\
                     U64.v minor.bump == 0)
          (ensures RBridge.major_field_zero_no_minor minor major)
  = // Definition: major heap fields satisfy constraints
    // init_heap creates single blue block - need to check its fields
    admit() // TODO: Reason about init_heap structure

/// Precondition 1 components for empty minor heap
let empty_minor_heap_shape
  (minor: minor_state)
  : Lemma (requires U64.v minor.bump == 0)
          (ensures minor_heap_shape minor)
  = // Empty minor heap should satisfy shape invariant
    admit() // TODO: Unfold definition

let empty_minor_major_fields_no_blue
  (minor: minor_state) (major: heap)
  : Lemma (requires U64.v minor.bump == 0)
          (ensures minor_major_fields_no_blue minor major)
  = // No minor objects = no fields to check
    // Use lemma proving bump==0 implies minor_objects is empty
    MinorZero.minor_objects_zero minor;
    assert (minor_objects minor == Seq.empty);
    ()

let empty_major_minor_fields_no_infix
  (minor: minor_state) (major: heap)
  : Lemma (requires U64.v minor.bump == 0)
          (ensures major_minor_fields_no_infix_targets minor major)
  = // No minor objects = no infix targets to check
    admit() // TODO: Should be automatic

/// Master lemma combining all preconditions for empty case
let all_preconditions_empty
  (minor_state_val: minor_state)
  (major_data: heap) (fp: U64.t)
  (roots_seq: Seq.seq U64.t) (nroots: SZ.t)
  (slots_seq: Seq.seq U64.t) (nslots: SZ.t)
  (fwd_seq: Seq.seq U64.t)
  : Lemma (requires
            // Construction facts
            (major_data, fp) == SpecAlloc.init_heap_spec (Seq.create heap_size 0uy) /\
            U64.v minor_state_val.bump == 0 /\
            SZ.v nroots == 0 /\ Seq.length roots_seq == 0 /\
            SZ.v nslots == 0 /\ Seq.length slots_seq == 0 /\
            Seq.length fwd_seq == UpdatePtrs.fwd_array_size /\
            (forall (i: nat). i < Seq.length fwd_seq ==> Seq.index fwd_seq i == 0UL))
          (ensures
            // All 11 GC preconditions
            collection_heap_shape minor_state_val major_data fp /\
            SZ.v nroots == Seq.length roots_seq /\
            Seq.length fwd_seq == UpdatePtrs.fwd_array_size /\
            (forall (i: nat). i < Seq.length fwd_seq ==> Seq.index fwd_seq i == 0UL) /\
            UpdatePtrs.ref_table_sound major_data slots_seq (SZ.v nslots) /\
            UpdatePtrs.ref_table_covers_minor_ptrs major_data slots_seq (SZ.v nslots) /\
            UpdatePtrs.slots_pairwise_distinct slots_seq (SZ.v nslots) /\
            MinorFwd.remembered_targets_in_roots major_data roots_seq slots_seq (SZ.v nslots) /\
            RBridge.major_field_zero_no_minor minor_state_val major_data /\
            RBridge.roots_valid_nonblue roots_seq major_data /\
            MinorFwd.roots_valid_for_minor_collection minor_state_val major_data roots_seq)
  = // Prove each precondition
    empty_slots_distinct slots_seq (SZ.v nslots);
    empty_roots_valid_nonblue roots_seq major_data;
    empty_roots_valid_for_collection minor_state_val major_data roots_seq;
    empty_ref_table_sound major_data slots_seq (SZ.v nslots);
    empty_ref_table_covers major_data slots_seq (SZ.v nslots);
    empty_remembered_targets major_data roots_seq slots_seq (SZ.v nslots);
    init_heap_major_field_zero_no_minor minor_state_val major_data fp;
    empty_minor_heap_shape minor_state_val;
    empty_minor_major_fields_no_blue minor_state_val major_data;
    empty_major_minor_fields_no_infix minor_state_val major_data;
    // TODO: Prove major_heap_shape
    admit()
