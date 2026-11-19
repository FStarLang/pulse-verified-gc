/// What the remembered set hands a minor collection: the young values of the
/// valid remembered slots (`GC.Gen.MinorCollectForwarding.Helpers.
/// remembered_slot_targets`), both directions.  Used by the hoisted-run
/// corollary (`GC.Gen.Run.Hoisted.Minor`).
module GC.Gen.Run.RememberedTargets

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap

module U64 = FStar.UInt64
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module GBase = GC.Gen.Base
module Promote = GC.Gen.Promote

let slot_target (major: heap) (slots: seq U64.t) (n: nat) (i: nat) (t: U64.t) : prop =
  i < n /\ i < Seq.length slots /\ U64.v (Seq.index slots i) < heap_size /\
  U64.v (Seq.index slots i) % 8 == 0 /\
  t == GBase.to_minor_offset (read_word major (Seq.index slots i <: hp_addr)) /\ Promote.is_minor_pointer t

val remembered_mem (major: heap) (slots: seq U64.t) (n: nat) (t: U64.t)
  : Lemma (Seq.mem t (MCFH.remembered_slot_targets major slots n) <==>
           (exists (i: nat). slot_target major slots n i t))
