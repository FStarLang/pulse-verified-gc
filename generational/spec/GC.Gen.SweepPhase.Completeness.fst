module GC.Gen.SweepPhase.Completeness

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.SweepPhase.Intrinsic
open GC.Spec.SweepPhase.Completeness
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module GenInv = GC.Gen.HeapInvariant
module Ph = GC.Spec.Phase
module Cheney = GC.Gen.Cheney
module Promote = GC.Gen.Promote
module SPM = GC.Gen.SweepPhase.Minor

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

let survivor_or_new_minor g0 since minor g fp c roots =
  FStar.Classical.forall_intro (SPM.minor_keeps_blocks minor g fp c roots)

let nothing_promoted_after_reset c m g fp roots x =
  FStar.Classical.forall_intro (minor_reset_objects_not_mem m)
