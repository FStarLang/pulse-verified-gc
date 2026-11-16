module GC.Gen.ForwardingArray

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.RefTable
module PromoteSpec = GC.Gen.Promote
module SpecObj = GC.Spec.Object
module SpecHeap = GC.Spec.Heap

let rewrite_root_arr_spec farr fwd v = ()

let rewrite_slots_iter_done major fwd slots n idx = ()

let rewrite_slots_iter_step major fwd slots n idx = ()

let rec rewrite_slots_iter_snoc (major: heap) (fwd: PromoteSpec.forwarding_map)
                                (slots: Seq.seq U64.t) (n: nat) (idx: nat)
  : Lemma (requires n < Seq.length slots /\ valid_slot_addrs slots (n + 1) /\ idx <= n)
          (ensures rewrite_slots_iter major fwd slots (n + 1) idx ==
                   rewrite_one_slot_spec (rewrite_slots_iter major fwd slots n idx)
                                        fwd (Seq.index slots n))
          (decreases (n - idx))
  = if idx >= n then ()
    else begin
      rewrite_slots_iter_step major fwd slots (n + 1) idx;
      rewrite_slots_iter_step major fwd slots n idx;
      rewrite_slots_iter_snoc (rewrite_one_slot_spec major fwd (Seq.index slots idx))
                              fwd slots n (idx + 1)
    end

let update_promoted_iter_zero major farr fwd idx = ()

let update_promoted_iter_scan major farr fwd idx = ()

let update_promoted_iter_skip major farr fwd idx = ()

let update_promoted_iter_done major farr fwd idx = ()

let hdr_addr_wf obj = ()
