/// ---------------------------------------------------------------------------
/// GC.SPOT.IncrementalCycle - the incremental entry points compose
/// ---------------------------------------------------------------------------
///
/// A caller holding only `full_gc`'s precondition runs one incremental major
/// collection -- `minor_collect`, `start_cycle` (which darkens the roots and
/// enters `Marking`), one mark slice of 64 words, then two slices with an
/// unbounded budget -- with no fact supplied in between: each entry point's
/// postcondition is the next one's precondition (`gc_state` at whatever
/// phase it leaves), and the cycle ends idle in the stop-the-world shape
/// `full_gc` demands.
///
/// Two unbounded slices always suffice after a slice from `Marking`: the
/// 64-word slice leaves `Marking` or, if no grey object is left, the start of
/// the sweep (`Sweeping zero_addr`); an unbounded slice from `Marking`
/// finishes marking (`Sweeping zero_addr`), one from a sweep finishes the
/// sweep (`Idle`), and at `Idle` a slice does nothing.
///
/// On success, the sweep's completeness applies to the cycle
/// (`cycle_frees_dead_post`).  The marked heap `s1` -- the heap at the moment
/// marking ended (the phase became `Sweeping zero_addr`) -- is reached from
/// the darkened heap by mark moves (`GC.Spec.MarkPhase.Slice.mark_steps`),
/// has nothing grey, and is the stop-the-world marked heap of the darkened
/// one (`Corr.mark_post` from `gen_gc_prepared_major` and its root objects
/// `gen_gc_prepared_roots`); at the end every object white in `s1` --
/// exactly the objects unreachable from the root objects in the darkened
/// heap -- is freed.  The mark postcondition is not part of the incremental
/// entry points' contracts (a slice only promises mark moves); it holds here
/// because no program runs between the slices, so marking keeps the
/// stop-the-world strengthening of its invariant
/// (`GC.Spec.MarkPhase.Stw.marking_inv_stw`), as inside `full_gc`.

module GC.SPOT.IncrementalCycle

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Phase
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.Impl
open GC.Impl.Heap

module CheneyImpl = GC.Gen.Impl.Cheney
module Ph = GC.Spec.Phase
module SL = GC.Spec.SweepPhase.Slice
module GenInv = GC.Gen.HeapInvariant
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module RT = GC.Gen.RefTable
module MinorFwd = GC.Gen.MinorCollectForwarding
module GI = GC.Gen.Incremental
module Corr = GC.Spec.Correctness
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPC = GC.Spec.SweepPhase.Completeness
module GMP = GC.Gen.MajorPrecondition
module CheneySpec = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module PromoteSpec = GC.Gen.Promote
module S = GC.Spec.MarkPhase.Slice
module Stw = GC.Spec.MarkPhase.Stw
module Mark = GC.Spec.Mark
module MBI = GC.Spec.MarkBoundedInv
module FL = GC.Spec.FreeList

/// The unbounded budget is more words than the heap has.
let unbounded_budget () : Lemma (U64.v 0xFFFFFFFFFFFFFFFFUL > GC.Spec.Base.heap_words /\
                                 GI.unbounded (U64.v 0xFFFFFFFFFFFFFFFFUL))
  = assert_norm (pow2 57 < U64.v 0xFFFFFFFFFFFFFFFFUL);
    assert_norm (U64.v 0xFFFFFFFFFFFFFFFFUL == pow2 64 - 1)

/// ---------------------------------------------------------------------------
/// Where the cycle is
/// ---------------------------------------------------------------------------

/// The marked heap `s1`: reached from the darkened heap `g0` by mark moves,
/// nothing grey, and the stop-the-world marked heap of `g0` from the root
/// objects `droots`.
let marked (g0: heap) (droots: Seq.seq obj_addr) (fp0: U64.t) (s1: heap) : prop =
  S.mark_steps g0 s1 /\ Mark.noGreyObjects s1 /\ Corr.mark_post g0 s1 droots fp0

/// Where the cycle started from `g0` is, at the heap `s`, the free-list head
/// `fp` and the phase `ph`, with `s1` the marked heap once marking is over:
/// marking, with the stop-the-world strengthening of the marking invariant;
/// or past marking, with the sweep's account from `s1` (`SPC.phase_account`:
/// every block not free is a survivor of marking; nothing is allocated).
let cycle_at (g0: heap) (droots: Seq.seq obj_addr) (fp0: U64.t)
    (s: heap) (fp: U64.t) (ph: Ph.gc_phase) (s1: heap) : prop =
  (Ph.Marking? ph ==> fp == fp0 /\ S.mark_steps g0 s /\ Stw.marking_inv_stw g0 s droots) /\
  (~(Ph.Marking? ph) ==> marked g0 droots fp0 s1 /\ SPC.phase_account s1 SPC.nothing_new s fp ph)

/// The marked heap after a slice from `ph` to `ph'` that left `s'`: `s'` if
/// the slice ended marking, else the one before.
let marked_after (ph ph': Ph.gc_phase) (s1 s': heap) : heap =
  if Ph.Marking? ph && not (Ph.Marking? ph') then s' else s1

/// How far the cycle has to go: mark, then sweep.
let rank (ph: Ph.gc_phase) : nat =
  match ph with
  | Ph.Idle -> 0
  | Ph.Sweeping _ -> 1
  | Ph.Marking -> 2

/// **The start of the cycle**, from the minor collection's result: the
/// darkened heap `start_cycle` leaves is `gen_gc_prepared_major`, the
/// stop-the-world marking starts from it, and the cycle is at its start.
#push-options "--fuel 0 --ifuel 0"
let cycle_start (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
    (s_dark: heap)
  : Lemma
    (requires
      (let result = CheneySpec.cheney_collect_spec minor major fp roots in
       GenInv.collection_heap_shape minor major fp /\
       MinorFwd.roots_valid_for_minor_collection minor major roots /\
       CheneyBFS.cheney_no_oom Idle minor major fp roots /\
       start_cycle_post result.mc_major result.mc_roots s_dark))
    (ensures
      (let result = CheneySpec.cheney_collect_spec minor major fp roots in
       let g0 = gen_gc_prepared_major minor major fp roots in
       let droots = gen_gc_prepared_roots minor major fp roots in
       s_dark == g0 /\
       Stw.stw_start g0 droots /\ FL.fp_in_heap result.mc_fp g0 /\
       cycle_at g0 droots result.mc_fp s_dark result.mc_fp Ph.Marking s_dark))
  = let result = CheneySpec.cheney_collect_spec minor major fp roots in
    let g0 = gen_gc_prepared_major minor major fp roots in
    let droots = gen_gc_prepared_roots minor major fp roots in
    let cap = prepared_cap result.mc_roots in
    gen_gc_major_precondition_elim minor major fp roots;
    MBI.bounded_mark_inv_elim_wfh g0 droots cap;
    MBI.bounded_mark_inv_elim_objects g0 droots cap;
    MBI.bounded_mark_inv_elim_density g0 droots cap;
    Stw.marking_inv_stw_start g0 droots;
    S.mark_steps_refl g0
#pop-options

/// **A slice from `Marking`**: mark moves keep the stop-the-world invariant;
/// if marking ended, the heap it left is the marked heap and the sweep's
/// account starts from it.
#push-options "--fuel 0 --ifuel 1"
let mark_slice_step (minor: minor_state) (g0: heap) (droots: Seq.seq obj_addr) (fp0: U64.t)
    (s: heap) (fp: U64.t) (s1: heap) (budget: nat) (s': heap) (fp': U64.t) (ph': Ph.gc_phase)
  : Lemma (requires GI.phase_shape minor s fp Ph.Marking /\
                    cycle_at g0 droots fp0 s fp Ph.Marking s1 /\
                    Stw.stw_start g0 droots /\ FL.fp_in_heap fp0 g0 /\
                    GI.mark_slice_post s fp budget s' fp' ph')
          (ensures cycle_at g0 droots fp0 s' fp' ph' (marked_after Ph.Marking ph' s1 s'))
  = Stw.marking_inv_stw_steps g0 s s' droots;
    S.mark_steps_trans g0 s s';
    GI.mark_slice_shape minor s fp budget s' fp' ph';
    if Ph.Sweeping? ph' then begin
      Stw.marking_inv_stw_done g0 s' droots fp0;
      GI.phase_shape_sweeping minor s' fp' zero_addr;
      SPC.survivor_or_new_start s'
    end
#pop-options

/// **A slice at any phase** keeps where the cycle is; an unbounded one from
/// a phase that is not idle moves it on (`rank`).
#push-options "--fuel 0 --ifuel 1"
let slice_step (minor: minor_state) (g0: heap) (droots: Seq.seq obj_addr) (fp0: U64.t)
    (s: heap) (fp: U64.t) (ph: Ph.gc_phase) (s1: heap)
    (budget: nat) (s': heap) (fp': U64.t) (ph': Ph.gc_phase)
  : Lemma (requires GI.phase_shape minor s fp ph /\ cycle_at g0 droots fp0 s fp ph s1 /\
                    Stw.stw_start g0 droots /\ FL.fp_in_heap fp0 g0 /\
                    GI.major_slice_post s fp ph budget s' fp' ph')
          (ensures cycle_at g0 droots fp0 s' fp' ph' (marked_after ph ph' s1 s') /\
                   (budget > heap_words /\ GI.unbounded budget ==>
                      (Ph.Idle? ph /\ Ph.Idle? ph') \/ rank ph' < rank ph))
  = match ph with
    | Ph.Marking -> mark_slice_step minor g0 droots fp0 s fp s1 budget s' fp' ph'
    | Ph.Idle -> ()
    | Ph.Sweeping c ->
        SPC.phase_account_slice s1 SPC.nothing_new s fp ph budget;
        if budget > heap_words then GI.phase_slice_finishes minor s fp ph budget
#pop-options

/// **The cycle frees what marking left dead**: with the marked heap `s1`,
/// every object white in it -- exactly the objects unreachable from the root
/// objects in the darkened heap `g0` (`SPC.dead_at_mark`) -- is freed in the
/// heap `s3` the cycle ends with.  Nothing is allocated in between, so no
/// address is new.
let cycle_frees_dead_post (g0: heap) (droots: Seq.seq obj_addr) (fp0: U64.t) (s1 s3: heap) : prop =
  marked g0 droots fp0 s1 /\
  (forall (x: obj_addr). SPI.white_after_mark s1 x ==> SPC.freed s3 x) /\
  (forall (x: obj_addr). SPC.dead_at_mark g0 s1 droots x ==> SPC.freed s3 x)

let cycle_frees_dead (g0: heap) (droots: Seq.seq obj_addr) (fp0: U64.t)
                     (s1: heap) (s3: heap) (fp3: U64.t)
  : Lemma (requires Stw.stw_start g0 droots /\ cycle_at g0 droots fp0 s3 fp3 Ph.Idle s1)
          (ensures cycle_frees_dead_post g0 droots fp0 s1 s3)
  = SPC.phase_account_idle s1 SPC.nothing_new s3 fp3;
    FStar.Classical.forall_intro (FStar.Classical.move_requires
      (SPC.dead_at_mark_white g0 s1 droots fp0))

/// ---------------------------------------------------------------------------
/// The composition
/// ---------------------------------------------------------------------------

/// One major slice from where the cycle is, and where it leaves it.
#push-options "--fuel 0 --ifuel 0"
fn cycle_slice
  (gh: gen_heap_t) (budget: U64.t)
  (g0: erased heap) (droots: erased (Seq.seq obj_addr)) (fp0: erased U64.t)
  (s1: erased heap)
  (#d: erased minor_heap) (#b: erased U64.t)
  (#s: erased heap) (#fp: erased U64.t) (#ph: erased Ph.gc_phase)
  requires gc_state gh d b s fp ph **
           pure (cycle_at g0 droots fp0 s fp ph s1 /\
                 Stw.stw_start g0 droots /\ FL.fp_in_heap fp0 g0)
  ensures exists* s' fp' ph'.
    gc_state gh d b s' fp' ph' **
    pure (cycle_at g0 droots fp0 s' fp' ph' (marked_after ph ph' s1 s') /\
          (U64.v budget > heap_words /\ GI.unbounded (U64.v budget) ==>
             (Ph.Idle? ph /\ Ph.Idle? ph') \/ rank ph' < rank ph))
{
  unfold gc_state;
  let shape = Ghost.hide (GI.phase_shape ({ data = d; bump = b } <: minor_state) s fp ph);
  assert (pure (Ghost.reveal shape));
  fold (gc_state gh d b s fp ph);
  let _idle = major_slice gh budget;
  with s' fp' ph'. assert (gc_state gh d b s' fp' ph');
  slice_step ({ data = d; bump = b } <: minor_state) g0 droots fp0 s fp ph s1
    (U64.v budget) s' fp' ph';
  assert (pure (cycle_at g0 droots fp0 s' fp' ph' (marked_after ph ph' s1 s')));
  assert (pure (U64.v budget > heap_words /\ GI.unbounded (U64.v budget) ==>
             (Ph.Idle? ph /\ Ph.Idle? ph') \/ rank ph' < rank ph));
}
#pop-options

#push-options "--fuel 0 --ifuel 0"
fn incremental_cycle_spot
  (gh: gen_heap_t)
  (roots: array U64.t) (nroots: SZ.t)
  (fwd_arr: array U64.t)
  (queue: larray U64.t GC.Gen.ForwardingArray.queue_size)
  (slots: array U64.t) (nslots: SZ.t)
  requires gc_state gh 'd 'b 's 'fp Ph.Idle **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           pure (SZ.v nroots == Seq.length 'rs /\
                 Seq.length 'farr == GC.Gen.ForwardingArray.fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
                 RT.ref_table_sound 's 'sl (SZ.v nslots) /\
                 RT.ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
                 MinorFwd.remembered_targets_in_roots 's 'rs 'sl (SZ.v nslots) /\
                 MinorFwd.roots_valid_for_minor_collection
                   ({ data = 'd; bump = 'b } <: minor_state) 's 'rs)
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2.
    gc_state gh d2 b2 s2 fp2 Ph.Idle **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    pure (GenInv.collection_heap_shape ({ data = d2; bump = b2 } <: minor_state) s2 fp2 /\
          ({ data = d2; bump = b2 } <: minor_state) == minor_reset ({ data = 'd; bump = 'b } <: minor_state))
{
  unfold gc_state;
  GI.phase_shape_idle ({ data = 'd; bump = 'b } <: minor_state) 's 'fp;
  minor_collect_idle_pre ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs 'farr 'sl
    (SZ.v nslots);
  GI.phase_free_idle ();
  fold (gc_state gh 'd 'b 's 'fp Ph.Idle);
  let ok = minor_collect gh roots nroots fwd_arr queue slots nslots;
  with d1 b1 s0 fp1. assert (gc_state gh d1 b1 s0 fp1 Ph.Idle);
  with rs1. assert (pts_to roots rs1);
  minor_collect_idle_post ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs 'farr 'sl
    (SZ.v nslots) ok d1 b1 s0 fp1 rs1;
  PromoteSpec.rewrite_roots_length 'rs
    (CheneySpec.cheney_promote Idle ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs).fwd_map;
  if ok {
    GMP.post_minor_roots_valid_for_darkening ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs;
    assert (pure (start_cycle_pre s0 rs1));
    assert (pure (nursery_empty d1 b1));
    start_cycle gh roots nroots;
    // the collector is marking the darkened heap
    with s_dark. assert (gc_state gh d1 b1 s_dark fp1 Ph.Marking);
    let g0 = Ghost.hide (gen_gc_prepared_major ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs);
    let droots = Ghost.hide (gen_gc_prepared_roots ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs);
    cycle_start ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs s_dark;
    // a mark slice of 64 words: still marking, or the start of the sweep
    cycle_slice gh 64UL g0 droots fp1 s_dark;
    with s_a fp_a ph_a. assert (gc_state gh d1 b1 s_a fp_a ph_a);
    let s1a = Ghost.hide (marked_after Ph.Marking ph_a s_dark s_a);
    // the rest of the cycle: two slices with an unbounded budget (the first
    // finishes marking if it is not finished, the last the sweep)
    unbounded_budget ();
    cycle_slice gh 0xFFFFFFFFFFFFFFFFUL g0 droots fp1 s1a;
    with s_b fp_b ph_b. assert (gc_state gh d1 b1 s_b fp_b ph_b);
    let s1 = Ghost.hide (marked_after ph_a ph_b s1a s_b);
    cycle_slice gh 0xFFFFFFFFFFFFFFFFUL g0 droots fp1 s1;
    with s3 fp3 ph3. assert (gc_state gh d1 b1 s3 fp3 ph3);
    assert (pure (Ph.Idle? ph3 /\ marked_after ph_b ph3 s1 s3 == Ghost.reveal s1));
    rewrite (gc_state gh d1 b1 s3 fp3 ph3) as (gc_state gh d1 b1 s3 fp3 Ph.Idle);
    unfold (gc_state gh d1 b1 s3 fp3 Ph.Idle);
    GI.phase_shape_idle ({ data = d1; bump = b1 } <: minor_state) s3 fp3;
    fold (gc_state gh d1 b1 s3 fp3 Ph.Idle);
    // everything marking left dead is freed by the end of the sweep
    cycle_frees_dead g0 droots fp1 s1 s3 fp3;
    assert (pure (S.mark_steps s_dark s1 /\
                  cycle_frees_dead_post g0 droots fp1 s1 s3))
  } else {
    // out of memory: the cycle is not started, and the collector stays idle
    unfold (gc_state gh d1 b1 s0 fp1 Ph.Idle);
    GI.phase_shape_idle ({ data = d1; bump = b1 } <: minor_state) s0 fp1;
    fold (gc_state gh d1 b1 s0 fp1 Ph.Idle);
  }
}
#pop-options
