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
module W = GC.Spec.Walk
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
module LL = GC.Spec.FusedSweep.Lossless
module Step = GC.Spec.FusedSweep.Step
module SPE = GC.Spec.SweepPhase.Intrinsic.End

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

let survivor_or_new_weaken g0 since since' g c = ()

let survivor_or_new_start g0 =
  let one (x: obj_addr)
    : Lemma (requires in_use (free_incremental sweep_start.cursor) g0 x)
            (ensures survivor g0 g0 x)
    = objects_addresses_gt_start zero_addr g0 x;
      Mark.color_exhaustive x g0
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// A block keeping its header position, size and tag keeps its size as an
/// object.
let same_block_wosize (g g': heap) (x: obj_addr)
  : Lemma (requires same_block g g' (hd_address x))
          (ensures wosize_of_object x g' == wosize_of_object x g)
  = colour_of g x; colour_of g' x

/// A non-free block before and after, with the same block, is a survivor
/// after if it was before.
let survivor_same_block (g0 g g': heap) (x: obj_addr)
  : Lemma (requires survivor g0 g x /\ same_block g g' (hd_address x))
          (ensures survivor g0 g' x)
  = same_block_wosize g g' x

let survivor_or_new_steps g0 since g fp c k =
  Step.sweep_inv_incremental_steps g fp c k;
  Step.sweep_steps_walk_end g fp c k;
  let (g', fp', st') = sweep_steps g fp (state_at g c) k in
  let one (x: obj_addr)
    : Lemma (requires in_use (free_incremental st'.cursor) g' x)
            (ensures survivor g0 g' x \/ since x)
    = if FStar.IndefiniteDescription.strong_excluded_middle (survivor g0 g x)
      then survivor_same_block g0 g g' x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)

let survivor_or_new_slice g0 since g fp c budget =
  let st = state_at g c in
  SL.slice_is_steps g fp st c budget;
  survivor_or_new_steps g0 since g fp c (SL.slice_count g fp st c budget)

let survivor_or_new_alloc g0 since g fp c wz tag =
  Mut.alloc_walk_end g fp c wz tag;
  Mut.alloc_sweep_shape g fp c wz tag;
  let r = AC.alloc_phase g fp (SA.Sweeping c) wz tag in
  let one (y: obj_addr)
    : Lemma (requires in_use (free_incremental c) r.SA.heap_out y)
            (ensures survivor g0 r.SA.heap_out y \/ with_new since r.SA.obj_out y)
    = Mut.alloc_in_use g fp c wz tag y;
      if r.SA.obj_out <> 0UL && y <> r.SA.obj_out then begin
        Mut.alloc_keeps g fp c wz tag y;
        if FStar.IndefiniteDescription.strong_excluded_middle (survivor g0 g y)
        then survivor_same_block g0 g r.SA.heap_out y
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)

let survivor_or_new_body_write g0 since g fp c x a v =
  Mut.body_write_shape g fp c x a v;
  sweep_shape_elim g fp c;
  Mut.same_heads_walk_end g (write_word g a v);
  same_heads_facts g (write_word g a v);
  free_incremental_ok c;
  let g' = write_word g a v in
  let one (y: obj_addr)
    : Lemma (requires in_use (free_incremental c) g' y)
            (ensures survivor g0 g' y \/ since y)
    = colour_of g y; colour_of g' y
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// ---------------------------------------------------------------------------
/// Coverage
/// ---------------------------------------------------------------------------

/// The extent of an object of the walk is its block.
let extent_block (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g))
          (ensures (let q = hd_address x in
                    W.reaches g zero_addr (U64.v q) /\ W.can_step g q /\
                    LL.next_pos g x == W.bnext g q))
  = W.objects_mem_iff g zero_addr x;
    W.hd_address_pos x;
    colour_of g x

/// Two different objects of a walk have disjoint extents.
let extents_disjoint (g: heap) (x y: obj_addr) (p: nat)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\ x <> y /\
                    LL.in_extent g x p)
          (ensures ~(LL.in_extent g y p))
  = extent_block g x; extent_block g y;
    let qx = hd_address x in
    let qy = hd_address y in
    W.hd_address_pos x; W.hd_address_pos y;
    if U64.v qx < U64.v qy then W.reaches_block_before g zero_addr qx (U64.v qy)
    else if U64.v qy < U64.v qx then W.reaches_block_before g zero_addr qy (U64.v qx)

/// The extent of an object of a dense walk lies below the walk's end.
let extent_below_end (g: heap) (x: obj_addr) (p: nat)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ LL.in_extent g x p /\
                    W.walk_end g zero_addr + 8 >= heap_size)
          (ensures p < W.walk_end g zero_addr /\ U64.v zero_addr <= p)
  = extent_block g x;
    let q = hd_address x in
    let e = W.walk_end g zero_addr in
    W.reaches_walk_end g zero_addr;
    W.reaches_stuck g zero_addr e (U64.v q);
    W.reaches_bounds g zero_addr (U64.v q);
    W.reaches_block_before g zero_addr q e

/// A word of the walk lies in the extent of an object of the walk.
let block_over (g: heap) (p: nat)
  : Ghost obj_addr
      (requires U64.v zero_addr <= p /\ p < W.walk_end g zero_addr)
      (ensures fun y -> Seq.mem y (objects zero_addr g) /\ LL.in_extent g y p)
  = W.reaches_walk_end g zero_addr;
    let q = W.block_at g zero_addr (W.walk_end g zero_addr) p in
    W.reaches_bounds g zero_addr (U64.v q);
    let y = obj_of q in
    obj_of_facts q;
    W.hd_address_pos y;
    W.objects_mem_iff g zero_addr y;
    extent_block g y;
    y

let covered_word (g0: heap) (since: obj_addr -> prop) (g: heap) (x: obj_addr) (p: nat)
  : Lemma (requires idle_account g0 since g /\ white_after_mark g0 x /\ LL.in_extent g0 x p)
          (ensures free_or_new_at g since p)
  = W.reaches_end_of_dense g;
    extent_below_end g0 x p;
    let y = block_over g p in
    if is_blue y g then ()
    else if FStar.IndefiniteDescription.strong_excluded_middle (since y) then ()
    else begin
      assert (survivor g0 g y);
      extent_block g y; extent_block g0 y;
      Mark.colors_exclusive x g0;
      extents_disjoint g0 x y p
    end

let covered_at_idle g0 since g =
  let one (x: obj_addr) (p: nat)
    : Lemma (white_after_mark g0 x /\ LL.in_extent g0 x p ==> free_or_new_at g since p)
    = FStar.Classical.move_requires (covered_word g0 since g x) p
  in
  FStar.Classical.forall_intro_2 one

let freed_by_end g0 since g fp c =
  SPE.sweep_inv_incremental_end g fp c;
  sweep_inv_incremental_elim g fp c;
  let dead (x: obj_addr)
    : Lemma (requires white_after_mark g0 x) (ensures freed g x \/ since x)
    = Mark.colors_exclusive x g0
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires dead)

let covered_by_end g0 since g fp c =
  freed_by_end g0 since g fp c;
  covered_at_idle g0 since g

let dead_at_mark_white h_init h_mark roots fp x =
  Mark.colors_exclusive x h_mark;
  if FStar.IndefiniteDescription.strong_excluded_middle
       (Seq.mem x (objects zero_addr h_mark) /\ ~(is_blue x h_mark))
  then Corr.mark_post_white_iff_unreachable h_init h_mark roots fp x

let unreachable_freed_by_end h_init h_mark roots fp0 since g fp c =
  freed_by_end h_mark since g fp c;
  FStar.Classical.forall_intro (dead_at_mark_white h_init h_mark roots fp0)

let unreachable_covered_at_idle h_init h_mark roots fp0 since g =
  covered_at_idle h_mark since g;
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
  covered_at_idle g0 since g;
  let dead (x: obj_addr)
    : Lemma (requires white_after_mark g0 x) (ensures freed g x \/ since x)
    = Mark.colors_exclusive x g0
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires dead)
