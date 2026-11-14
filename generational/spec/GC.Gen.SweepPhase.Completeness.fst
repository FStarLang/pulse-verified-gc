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
  SPM.minor_keeps_walk_end minor g fp c roots;
  let g' = (SPM.collect_at c minor g fp roots).Promote.mc_major in
  let one (x: obj_addr)
    : Lemma (requires in_use (free_incremental c) g' x)
            (ensures survivor g0 g' x \/ with_promoted since c minor g fp roots x)
    = SPM.minor_keeps_blocks minor g fp c roots x;
      colour_of g x; colour_of g' x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)

let nothing_promoted_after_reset c m g fp roots x =
  FStar.Classical.forall_intro (minor_reset_objects_not_mem m)

let made_by_minor_promoted minor g fp c roots x =
  SPM.minor_keeps_blocks minor g fp c roots x

let survivor_or_new_minor_made g0 since minor g fp c roots =
  SPM.minor_keeps_walk_end minor g fp c roots;
  let g' = (SPM.collect_at c minor g fp roots).Promote.mc_major in
  let one (x: obj_addr)
    : Lemma (requires in_use (free_incremental c) g' x)
            (ensures survivor g0 g' x \/ with_made since c g g' x)
    = SPM.minor_keeps_blocks minor g fp c roots x;
      colour_of g x; colour_of g' x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)

let reclaimed_was_dead_minor g0 since minor g fp c roots =
  SPM.minor_keeps_walk_end minor g fp c roots;
  SPM.minor_keeps_sweep_phase minor g fp c roots;
  let res = SPM.collect_at c minor g fp roots in
  let g' = res.Promote.mc_major in
  sweep_inv_incremental_elim g' res.Promote.mc_fp c;
  let fwd (x: obj_addr)
    : Lemma (in_use (free_incremental c) g x ==>
             in_use (free_incremental c) g' x /\ ~(made_by c g g' x) /\
             wosize_of_object x g' == wosize_of_object x g)
    = SPM.minor_keeps_blocks minor g fp c roots x;
      colour_of g x; colour_of g' x
  in
  FStar.Classical.forall_intro fwd;
  reclaimed_was_dead_transfer g0 g g' since (with_made since c g g') (free_incremental c)
    (free_incremental c) (made_by c g g')
