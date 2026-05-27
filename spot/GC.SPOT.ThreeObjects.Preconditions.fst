module GC.SPOT.ThreeObjects.Preconditions

/// Precondition lemmas for 3-object SPOT
/// Reuses infrastructure from empty case where possible

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq
module SZ = FStar.SizeT

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.HeapInvariant
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module MinorFwd = GC.Gen.MinorCollectForwarding
module RBridge = GC.Gen.ReachabilityBridge
module PromoteSpec = GC.Gen.Promote

/// Precondition 2: nroots == length
let nroots_eq_length (nroots: nat) (roots: Seq.seq U64.t)
  : Lemma (requires nroots == Seq.length roots)
          (ensures nroots == Seq.length roots)
  = ()

/// Precondition 3: fwd array size
let fwd_array_size_ok (fwd: Seq.seq U64.t)
  : Lemma (requires Seq.length fwd == UpdatePtrs.fwd_array_size)
          (ensures Seq.length fwd == UpdatePtrs.fwd_array_size)
  = ()

/// Precondition 4: fwd array zeros
let fwd_array_zeros (fwd: Seq.seq U64.t)
  : Lemma (requires forall (i: nat). i < Seq.length fwd ==> Seq.index fwd i == 0UL)
          (ensures forall (i: nat). i < Seq.length fwd ==> Seq.index fwd i == 0UL)
  = ()

/// Precondition 7: One slot is pairwise distinct
let one_slot_pairwise_distinct (slot: U64.t)
  : Lemma (ensures (forall (i j: nat). 
                     i < 1 /\ j < 1 /\ i <> j ==>
                     Seq.index (Seq.create 1 slot) i <> Seq.index (Seq.create 1 slot) j))
  = () // Vacuous - no pairs with i <> j when length is 1

/// Precondition 10: One root valid nonblue
let one_root_valid_nonblue 
  (root: U64.t) (major: heap)
  : Lemma (requires is_val_addr root /\
                     Seq.mem (root <: obj_addr) (objects zero_addr major) /\
                     ~(is_blue (root <: obj_addr) major))
          (ensures (forall (r: U64.t).
                     Seq.mem r (Seq.create 1 root) ==>
                     (~(is_val_addr r) \/
                      (Seq.mem (r <: obj_addr) (objects zero_addr major) /\
                       ~(is_blue (r <: obj_addr) major)))))
  = ()

/// Precondition 11: One root valid for minor collection
let one_root_valid_for_collection
  (root: U64.t) (minor: minor_state) (major: heap)
  : Lemma (requires 
             ((PromoteSpec.is_minor_pointer root ==>
               Seq.mem root (minor_objects minor) /\ minor_wosize minor root > 0) /\
              (~(PromoteSpec.is_minor_pointer root) ==>
               is_val_addr root /\ 
               Seq.mem (root <: obj_addr) (objects zero_addr major) /\
               ~(is_blue (root <: obj_addr) major))))
          (ensures (forall (r: U64.t).
                     Seq.mem r (Seq.create 1 root) ==>
                     ((PromoteSpec.is_minor_pointer r ==>
                       Seq.mem r (minor_objects minor) /\ minor_wosize minor r > 0) /\
                      (~(PromoteSpec.is_minor_pointer r) ==>
                       is_val_addr r /\ Seq.mem (r <: obj_addr) (objects zero_addr major) /\
                       ~(is_blue (r <: obj_addr) major)))))
  = ()

/// Precondition 5: ref_table_sound for one slot
/// UpdatePtrs.ref_table_sound has signature: heap -> Seq.seq U64.t -> nat -> prop
let one_slot_ref_table_sound
  (slot: U64.t) (obj: obj_addr) (j: nat) (major: heap)
  : Lemma (requires U64.v slot < heap_size /\
                     U64.v slot % 8 == 0 /\
                     is_val_addr obj /\
                     j < wosize obj major)
          (ensures UpdatePtrs.ref_table_sound major (Seq.create 1 slot) 1)
  = () // TODO: Need to show exists witness

/// Precondition 8: remembered_targets_in_roots for one slot
let one_slot_remembered_targets
  (slot: U64.t) (root: U64.t) (major: heap)
  : Lemma (requires 
             U64.v slot < heap_size /\
             U64.v slot % 8 == 0 /\
             (let field_val = PromoteSpec.to_minor_offset (read_word major (slot <: hp_addr)) in
              PromoteSpec.is_minor_pointer field_val ==> field_val == root))
          (ensures MinorFwd.remembered_targets_in_roots major (Seq.create 1 root) (Seq.create 1 slot) 1)
  = // The remembered_slot_targets will contain at most one element (the field value if it's a minor pointer)
    // We need to prove that element is in roots
    // TODO: Need to reason about remembered_slot_targets_from for single element
    admit()
