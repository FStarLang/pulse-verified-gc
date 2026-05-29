module GC.SPOT.Preconditions

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module GenInv = GC.Gen.HeapInvariant
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module MinorFwd = GC.Gen.MinorCollectForwarding
module RBridge = GC.Gen.ReachabilityBridge
module Cheney = GC.Gen.Cheney
module GenImpl = GC.Gen.Impl

let zero_forwarding_array (farr: seq U64.t) : prop =
  Seq.length farr == UpdatePtrs.fwd_array_size /\
  (forall (i:nat). i < Seq.length farr ==> Seq.index farr i == 0UL)

let minor_collect_full_pre
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots farr slots: seq U64.t) (nslots: nat) : prop =
  GenInv.collection_heap_shape minor major fp /\
  zero_forwarding_array farr /\
  UpdatePtrs.ref_table_sound major slots nslots /\
  UpdatePtrs.ref_table_covers_minor_ptrs major slots nslots /\
  UpdatePtrs.slots_pairwise_distinct slots nslots /\
  MinorFwd.remembered_targets_in_roots major roots slots nslots /\
  RBridge.major_field_zero_no_minor minor major /\
  RBridge.roots_valid_nonblue roots major /\
  MinorFwd.roots_valid_for_minor_collection minor major roots

let gen_gc_pre
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots farr slots: seq U64.t) (nslots: nat)
  (st: seq obj_addr) (cap: nat) : prop =
  let result = Cheney.cheney_collect_spec minor major fp roots in
  minor_collect_full_pre minor major fp roots farr slots nslots /\
  GenInv.major_stack_shape result.mc_major st cap /\
  GenImpl.roots_match_stack result.mc_roots st

let zero_forwarding_array_elim (farr: seq U64.t)
  : Lemma (requires zero_forwarding_array farr)
          (ensures Seq.length farr == UpdatePtrs.fwd_array_size /\
                   (forall (i:nat). i < Seq.length farr ==> Seq.index farr i == 0UL))
  = ()

let singleton_slots_pairwise_distinct (slots: seq U64.t) (n: nat)
  : Lemma (requires n <= 1 /\ n <= Seq.length slots)
          (ensures UpdatePtrs.slots_pairwise_distinct slots n)
  = ()

let minor_collect_full_pre_elim
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots farr slots: seq U64.t) (nslots: nat)
  : Lemma (requires minor_collect_full_pre minor major fp roots farr slots nslots)
          (ensures
            GenInv.collection_heap_shape minor major fp /\
            Seq.length farr == UpdatePtrs.fwd_array_size /\
            (forall (i:nat). i < Seq.length farr ==> Seq.index farr i == 0UL) /\
            UpdatePtrs.ref_table_sound major slots nslots /\
            UpdatePtrs.ref_table_covers_minor_ptrs major slots nslots /\
            UpdatePtrs.slots_pairwise_distinct slots nslots /\
            MinorFwd.remembered_targets_in_roots major roots slots nslots /\
            RBridge.major_field_zero_no_minor minor major /\
            RBridge.roots_valid_nonblue roots major /\
            MinorFwd.roots_valid_for_minor_collection minor major roots)
  = zero_forwarding_array_elim farr

let gen_gc_pre_elim
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots farr slots: seq U64.t) (nslots: nat)
  (st: seq obj_addr) (cap: nat)
  : Lemma (requires gen_gc_pre minor major fp roots farr slots nslots st cap)
          (ensures
            minor_collect_full_pre minor major fp roots farr slots nslots /\
            (let result = Cheney.cheney_collect_spec minor major fp roots in
             GenInv.major_stack_shape result.mc_major st cap /\
             GenImpl.roots_match_stack result.mc_roots st))
  = ()
