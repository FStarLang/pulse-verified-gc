module GC.Gen.SweepPhase.Cycle

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Intrinsic
open GC.Spec.SweepPhase.Completeness
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Mark = GC.Spec.Mark
module Mut = GC.Spec.SweepPhase.Mutator
module SL = GC.Spec.SweepPhase.Slice
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Corr = GC.Spec.Correctness
module Ph = GC.Spec.Phase
module LL = GC.Spec.FusedSweep.Lossless
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module SPM = GC.Gen.SweepPhase.Minor
module SPC = GC.Gen.SweepPhase.Completeness

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

let rec cycle_account (#g0 #g: heap) (#fp: U64.t) (#ph: Ph.gc_phase) (#since: obj_addr -> prop)
                      (r: cycle g0 g fp ph since)
  : Lemma (ensures cycle_inv g0 since g ph) (decreases r)
  =
  match r with
  | Start fp0 _ ->
      phase_account_start g0 fp0
  | Slice #_ #g1 #fp1 #c1 #_ r1 budget g' fp' ph' _ ->
      cycle_account r1;
      phase_account_slice g0 since g1 fp1 (Ph.Sweeping c1) budget
  | Alloc #_ #g1 #fp1 #c1 #since1 r1 wz tag g' fp' obj _ ->
      cycle_account r1;
      survivor_or_new_alloc g0 since1 g1 fp1 c1 wz tag;
      reclaimed_was_dead_alloc g0 since1 g1 fp1 c1 wz tag
  | Write #_ #g1 #fp1 #c1 #since1 r1 x a v g' _ ->
      cycle_account r1;
      survivor_or_new_body_write g0 since1 g1 fp1 c1 x a v;
      reclaimed_was_dead_body_write g0 since1 g1 fp1 c1 x a v
  | Minor #_ #g1 #fp1 #c1 #since1 r1 minor roots g' fp' _ ->
      cycle_account r1;
      SPC.survivor_or_new_minor_made g0 since1 minor g1 fp1 c1 roots;
      SPC.reclaimed_was_dead_minor g0 since1 minor g1 fp1 c1 roots

let cycle_lossless #g0 #g #fp #since r =
  cycle_account r;
  lossless_at_idle g0 since g

let cycle_covered #g0 #g #fp #since r =
  cycle_account r;
  covered_at_idle g0 since g

let cycle_unreachable_covered h_init roots fp0 #h_mark #g #fp #since r =
  cycle_account r;
  unreachable_covered_at_idle h_init h_mark roots fp0 since g
