module GC.SPOT.PreconditionProofs

/// Proofs that GC preconditions hold for a simple 3-object heap
///
/// This module provides lemmas to prove each of the 11 preconditions
/// required by minor_collect_full, starting from heap construction facts.

open FStar.SizeT
open FStar.UInt64
open FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Allocator
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.HeapInvariant
module GenInv = GC.Gen.HeapInvariant
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module MinorFwd = GC.Gen.MinorCollectForwarding
module RBridge = GC.Gen.ReachabilityBridge

/// Precondition 1: collection_heap_shape
/// Proves that the major and minor heaps are well-formed, disjoint, etc.
let prove_collection_heap_shape
  (minor_data: Seq.seq U8.t) (minor_bump: U64.t)
  (major_data: heap_state) (fp: U64.t)
  : Lemma (GenInv.collection_heap_shape
            ({ data = minor_data; bump = minor_bump } <: minor_state) major_data fp)
  = admit() // TODO: Prove from init_heap and allocator postconditions

/// Precondition 2: nroots matches roots array length
/// Trivial from construction
let prove_nroots_length
  (nroots: SZ.t) (roots_seq: Seq.seq U64.t)
  : Lemma (requires SZ.v nroots == 1 /\ Seq.length roots_seq == 1)
          (ensures SZ.v nroots == Seq.length roots_seq)
  = ()

/// Precondition 3: fwd array size
/// Trivial from alloc
let prove_fwd_array_size
  (fwd_seq: Seq.seq U64.t)
  : Lemma (requires Seq.length fwd_seq == UpdatePtrs.fwd_array_size)
          (ensures Seq.length fwd_seq == UpdatePtrs.fwd_array_size)
  = ()

/// Precondition 4: fwd array all zeros
/// Trivial from A.alloc 0uL
let prove_fwd_array_zeros
  (fwd_seq: Seq.seq U64.t)
  : Lemma (requires (forall (i: nat). i < Seq.length fwd_seq ==> Seq.index fwd_seq i == 0UL))
          (ensures (forall (i: nat). i < Seq.length fwd_seq ==> Seq.index fwd_seq i == 0UL))
  = ()

/// Precondition 5: ref_table_sound
/// Slots array correctly describes major→minor pointers
let prove_ref_table_sound
  (major_data: heap_state) (slots_seq: Seq.seq U64.t) (nslots: nat)
  (obj_C: U64.t) (obj_A: U64.t)
  : Lemma (requires
            nslots == 1 /\
            Seq.length slots_seq == 1 /\
            Seq.index slots_seq 0 == U64.add obj_C 8UL /\  // C's field 0 address
            // TODO: Need to state that C's field 0 actually points to A in major_data
            true)
          (ensures UpdatePtrs.ref_table_sound major_data slots_seq nslots)
  = admit() // TODO: Prove by unfolding ref_table_sound definition

/// Precondition 6: ref_table_covers_minor_ptrs
/// All major→minor pointers are in slots array
let prove_ref_table_covers_minor_ptrs
  (major_data: heap_state) (slots_seq: Seq.seq U64.t) (nslots: nat)
  : Lemma (ensures UpdatePtrs.ref_table_covers_minor_ptrs major_data slots_seq nslots)
  = admit() // TODO: Prove that C's field 0 is the ONLY major→minor pointer

/// Precondition 7: slots_pairwise_distinct
/// No duplicate slot addresses
let prove_slots_pairwise_distinct
  (slots_seq: Seq.seq U64.t) (nslots: nat)
  : Lemma (requires nslots == 1 /\ Seq.length slots_seq == 1)
          (ensures UpdatePtrs.slots_pairwise_distinct slots_seq nslots)
  = admit() // TODO: Trivial for single slot - unfold definition

/// Precondition 8: remembered_targets_in_roots
/// Targets of remembered pointers (A) are in roots
let prove_remembered_targets_in_roots
  (major_data: heap_state) (roots_seq: Seq.seq U64.t)
  (slots_seq: Seq.seq U64.t) (nslots: nat)
  (obj_A: U64.t)
  : Lemma (requires
            nslots == 1 /\
            Seq.length roots_seq == 1 /\
            Seq.index roots_seq 0 == obj_A /\
            // TODO: Need that C's field 0 points to A
            true)
          (ensures MinorFwd.remembered_targets_in_roots major_data roots_seq slots_seq nslots)
  = admit() // TODO: Unfold definition and prove A is in roots

/// Precondition 9: major_field_zero_no_minor
/// Major heap fields don't point into minor heap before collection
let prove_major_field_zero_no_minor
  (minor_data: Seq.seq U8.t) (minor_bump: U64.t) (major_data: heap_state)
  : Lemma (ensures RBridge.major_field_zero_no_minor
                     ({ data = minor_data; bump = minor_bump } <: minor_state) major_data)
  = admit() // TODO: Prove that all major fields satisfy constraints

/// Precondition 10: roots_valid_nonblue
/// Root addresses point to valid non-blue objects
let prove_roots_valid_nonblue
  (roots_seq: Seq.seq U64.t) (major_data: heap_state)
  (obj_A: U64.t)
  : Lemma (requires
            Seq.length roots_seq == 1 /\
            Seq.index roots_seq 0 == obj_A
            // TODO: Need that A is a valid object in minor heap (not major)
            )
          (ensures RBridge.roots_valid_nonblue roots_seq major_data)
  = admit() // TODO: Unfold definition

/// Precondition 11: roots_valid_for_minor_collection
/// Roots are valid for minor GC
let prove_roots_valid_for_minor_collection
  (minor_data: Seq.seq U8.t) (minor_bump: U64.t)
  (major_data: heap_state) (roots_seq: Seq.seq U64.t)
  (obj_A: U64.t)
  : Lemma (requires
            Seq.length roots_seq == 1 /\
            Seq.index roots_seq 0 == obj_A
            // TODO: Need that A is valid in minor heap
            )
          (ensures MinorFwd.roots_valid_for_minor_collection
                     ({ data = minor_data; bump = minor_bump } <: minor_state) major_data roots_seq)
  = admit() // TODO: Unfold definition and prove

/// Master lemma: All preconditions hold
let all_preconditions_hold
  (minor_data: Seq.seq U8.t) (minor_bump: U64.t)
  (major_data: heap_state) (fp: U64.t)
  (roots_seq: Seq.seq U64.t) (nroots: SZ.t)
  (slots_seq: Seq.seq U64.t) (nslots: SZ.t)
  (fwd_seq: Seq.seq U64.t)
  (obj_C obj_A obj_B: U64.t)
  : Lemma (requires
            SZ.v nroots == 1 /\ SZ.v nslots == 1 /\
            Seq.length roots_seq == 1 /\ Seq.index roots_seq 0 == obj_A /\
            Seq.length slots_seq == 1 /\ Seq.index slots_seq 0 == U64.add obj_C 8UL /\
            Seq.length fwd_seq == UpdatePtrs.fwd_array_size /\
            (forall (i: nat). i < Seq.length fwd_seq ==> Seq.index fwd_seq i == 0UL)
            // TODO: Add heap construction facts
            )
          (ensures
            GenInv.collection_heap_shape
              ({ data = minor_data; bump = minor_bump } <: minor_state) major_data fp /\
            SZ.v nroots == Seq.length roots_seq /\
            Seq.length fwd_seq == UpdatePtrs.fwd_array_size /\
            (forall (i: nat). i < Seq.length fwd_seq ==> Seq.index fwd_seq i == 0UL) /\
            UpdatePtrs.ref_table_sound major_data slots_seq (SZ.v nslots) /\
            UpdatePtrs.ref_table_covers_minor_ptrs major_data slots_seq (SZ.v nslots) /\
            UpdatePtrs.slots_pairwise_distinct slots_seq (SZ.v nslots) /\
            MinorFwd.remembered_targets_in_roots major_data roots_seq slots_seq (SZ.v nslots) /\
            RBridge.major_field_zero_no_minor
              ({ data = minor_data; bump = minor_bump } <: minor_state) major_data /\
            RBridge.roots_valid_nonblue roots_seq major_data /\
            MinorFwd.roots_valid_for_minor_collection
              ({ data = minor_data; bump = minor_bump } <: minor_state) major_data roots_seq)
  = prove_collection_heap_shape minor_data minor_bump major_data fp;
    prove_nroots_length nroots roots_seq;
    prove_fwd_array_size fwd_seq;
    prove_fwd_array_zeros fwd_seq;
    prove_ref_table_sound major_data slots_seq (SZ.v nslots) obj_C obj_A;
    prove_ref_table_covers_minor_ptrs major_data slots_seq (SZ.v nslots);
    prove_slots_pairwise_distinct slots_seq (SZ.v nslots);
    prove_remembered_targets_in_roots major_data roots_seq slots_seq (SZ.v nslots) obj_A;
    prove_major_field_zero_no_minor minor_data minor_bump major_data;
    prove_roots_valid_nonblue roots_seq major_data obj_A;
    prove_roots_valid_for_minor_collection minor_data minor_bump major_data roots_seq obj_A
