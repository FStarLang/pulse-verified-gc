module GC.Spec.SweepPhase.Completeness

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Intrinsic

module U64 = FStar.UInt64
module Mark = GC.Spec.Mark
module Mut = GC.Spec.SweepPhase.Mutator
module SL = GC.Spec.SweepPhase.Slice
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Corr = GC.Spec.Correctness
module HeapModel = GC.Spec.HeapModel
module HeapGraph = GC.Spec.HeapGraph
module Graph = GC.Spec.Graph
module Ph = GC.Spec.Phase
module Step = GC.Spec.FusedSweep.Step
module SPE = GC.Spec.SweepPhase.Intrinsic.End

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

let survivor_or_new_weaken g0 since since' g c = ()

let survivor_or_new_start g0 =
  let one (x: obj_addr)
    : Lemma (requires in_use (free_incremental sweep_start.cursor) g0 x)
            (ensures survived_mark g0 x)
    = objects_addresses_gt_start zero_addr g0 x;
      Mark.color_exhaustive x g0
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)

let survivor_or_new_steps g0 since g fp c k =
  Step.sweep_inv_incremental_steps g fp c k

let survivor_or_new_slice g0 since g fp c budget =
  SL.sweep_slice_phase g fp c budget

let survivor_or_new_alloc g0 since g fp c wz tag =
  FStar.Classical.forall_intro (Mut.alloc_in_use g fp c wz tag)

let survivor_or_new_body_write g0 since g fp c x a v =
  Mut.body_write_shape g fp c x a v;
  same_heads_facts g (write_word g a v);
  free_incremental_ok c

let freed_by_end g0 since g fp c =
  SPE.sweep_inv_incremental_end g fp c;
  let dead (x: obj_addr)
    : Lemma (requires white_after_mark g0 x) (ensures freed g x \/ since x)
    = Mark.colors_exclusive x g0
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires dead)

let dead_at_mark_white h_init h_mark roots fp x =
  Mark.colors_exclusive x h_mark;
  if FStar.IndefiniteDescription.strong_excluded_middle
       (Seq.mem x (objects zero_addr h_mark) /\ ~(is_blue x h_mark))
  then Corr.mark_post_white_iff_unreachable h_init h_mark roots fp x

let unreachable_freed_by_end h_init h_mark roots fp0 since g fp c =
  freed_by_end h_mark since g fp c;
  FStar.Classical.forall_intro (dead_at_mark_white h_init h_mark roots fp0)

let phase_account_start g0 fp =
  sweep_inv_incremental_start g0 fp;
  survivor_or_new_start g0

let phase_account_slice g0 since g fp ph budget =
  match ph with
  | Ph.Idle -> ()
  | Ph.Sweeping c ->
      SL.sweep_slice_phase g fp c budget;
      survivor_or_new_slice g0 since g fp c budget;
      let (g', fp', st') = SL.sweep_slice g fp (state_at g c) budget in
      if sweep_done st'.cursor then freed_by_end g0 since g' fp' st'.cursor

let phase_account_idle g0 since g fp =
  let dead (x: obj_addr)
    : Lemma (requires white_after_mark g0 x) (ensures freed g x \/ since x)
    = Mark.colors_exclusive x g0
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires dead)
