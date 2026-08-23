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
  MinorFwd.roots_valid_for_minor_collection minor major roots

let gen_gc_pre
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots farr slots: seq U64.t) (nslots: nat)
  (st: seq obj_addr) (cap: nat) : prop =
  minor_collect_full_pre minor major fp roots farr slots nslots /\
  Seq.length st <= cap /\
  GenImpl.gen_gc_major_precondition minor major fp roots st cap

let zero_forwarding_array_elim (farr: seq U64.t)
  = ()

let zero_forwarding_array_intro (farr: seq U64.t)
  = ()

let singleton_slots_pairwise_distinct (slots: seq U64.t) (n: nat)
  = ()

let minor_collect_full_pre_elim
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots farr slots: seq U64.t) (nslots: nat)
  = zero_forwarding_array_elim farr

let minor_collect_full_pre_intro
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots farr slots: seq U64.t) (nslots: nat)
  = ()

let gen_gc_pre_elim
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots farr slots: seq U64.t) (nslots: nat)
  (st: seq obj_addr) (cap: nat)
  = ()

let gen_gc_pre_intro
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots farr slots: seq U64.t) (nslots: nat)
  (st: seq obj_addr) (cap: nat)
  = ()
