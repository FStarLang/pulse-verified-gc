(*
   Pulse GC (Generational) - the incremental sweep's entry points
*)

module GC.Gen.Impl.Incremental

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Impl.Heap
open GC.Impl.Stack
open GC.Gen.Impl
module SpecFields = GC.Spec.Fields
module CheneySpec = GC.Gen.Cheney
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module SpecGCPost = GC.Spec.Correctness
module Cheney = GC.Gen.Impl.Cheney
module GenInv = GC.Gen.HeapInvariant
module MinorFwd = GC.Gen.MinorCollectForwarding
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module CheneyBFS = GC.Gen.CheneyBFS
module RT = GC.Gen.RefTable
module Alloc = GC.Impl.Allocator
module Ph = GC.Spec.Phase
module FS = GC.Spec.FusedSweep
module SPI = GC.Spec.SweepPhase.Intrinsic
module SL = GC.Spec.SweepPhase.Slice
module GI = GC.Gen.Incremental
module GSP = GC.Gen.SweepPhase
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module FSC = GC.Impl.FusedSweepCoalesce
module CA = GC.Gen.CheneyAt
module CV = GC.Gen.CheneyWith
module CheneyPres = GC.Gen.CheneyPreservation
module PromoteSpec = GC.Gen.Promote
module SPM = GC.Gen.SweepPhase.Minor

/// ---------------------------------------------------------------------------
/// Sweeping
/// ---------------------------------------------------------------------------

/// The phase record a slice leaves.
inline_for_extraction noextract
let slice_record (fin: bool) (c t f: U64.t) : Alloc.phase_state =
  { Alloc.ps_kind = (if fin then 0UL else 1UL);
    Alloc.ps_cursor = c; Alloc.ps_swept_tail = t; Alloc.ps_last_fragment = f }

/// The slice in the spec, from the implementation's.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let slice_result (minor: minor_state) (g: heap) (fp: U64.t) (v: Alloc.phase_state)
    (budget: U64.t) (g': heap) (c' t' f' fp': U64.t)
  : Lemma (requires v.Alloc.ps_kind <> 0UL /\
                    GI.phase_shape minor g fp (Alloc.phase_of v) /\
                    FSC.slice_matches g fp v.Alloc.ps_cursor v.Alloc.ps_swept_tail
                      v.Alloc.ps_last_fragment budget g' (c', t', f', fp'))
          (ensures (let fin = not (U64.v c' + 8 < heap_size) in
                    U64.v c' <= heap_size /\
                    (g', fp', Alloc.phase_of (slice_record fin c' t' f')) ==
                      SL.phase_slice g fp (Alloc.phase_of v) (U64.v budget) /\
                    GI.phase_shape minor g' fp' (Alloc.phase_of (slice_record fin c' t' f'))))
  = GI.phase_slice_shape minor g fp (Alloc.phase_of v) (U64.v budget);
    let st = FSC.mk_st v.Alloc.ps_cursor v.Alloc.ps_swept_tail v.Alloc.ps_last_fragment in
    GI.phase_shape_sweeping minor g fp st;
    SL.sweep_slice_phase g fp st (U64.v budget);
    let (g1, fp1, st1) = SL.sweep_slice g fp st (U64.v budget) in
    SPI.sweep_phase_inv_elim g1 fp1 st1
#pop-options

let bounds () : Lemma (heap_size == GC.Spec.Base.heap_size /\ heap_size < pow2 57 /\
                       U64.v mword == 8 /\ pow2 57 * 2 <= pow2 64)
  = assert_norm (pow2 57 * 2 <= pow2 64)

/// The phase as the sweep state a record holds.
let sweeping_of (v: Alloc.phase_state)
  : Lemma (requires v.Alloc.ps_kind <> 0UL)
          (ensures Alloc.phase_of v ==
                   Ph.Sweeping (FSC.mk_st v.Alloc.ps_cursor v.Alloc.ps_swept_tail v.Alloc.ps_last_fragment))
  = ()

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
fn sweep_slice (gh: gen_heap_t) (budget: U64.t)
  requires gc_state gh 'd 'b 's 'fp 'ph
  returns fin: bool
  ensures exists* s2 fp2 ph2.
    gc_state gh 'd 'b s2 fp2 ph2 **
    pure ((s2, fp2, ph2) == SL.phase_slice 's 'fp 'ph (U64.v budget) /\
          fin == Ph.Idle? ph2)
{
  unfold gc_state;
  unfold is_gen_heap;
  unfold gen_phase;
  unfold Alloc.is_phase;
  let v = R.op_Bang gh.phase_ref;
  if (U64.eq v.Alloc.ps_kind 0UL) {
    fold (Alloc.is_phase gh.phase_ref 'ph);
    fold (gen_phase gh 'ph);
    fold (is_gen_heap gh 'd 'b 's 'fp);
    fold (gc_state gh 'd 'b 's 'fp 'ph);
    true
  } else {
    sweeping_of v;
    GI.phase_shape_sweeping ({ data = 'd; bump = 'b } <: minor_state) 's 'fp
      (FSC.mk_st v.Alloc.ps_cursor v.Alloc.ps_swept_tail v.Alloc.ps_last_fragment);
    let fp = R.op_Bang gh.fp_ref;
    let r = FSC.sweep_slice_impl gh.major v.Alloc.ps_cursor v.Alloc.ps_swept_tail
              v.Alloc.ps_last_fragment fp budget;
    with s2. assert (is_heap gh.major s2);
    bounds ();
    match r {
      (c', t', f', fp') -> {
        slice_result ({ data = 'd; bump = 'b } <: minor_state) 's 'fp v budget s2 c' t' f' fp';
        let fin = not (U64.lt (U64.add c' mword) heap_size_u64);
        R.op_Colon_Equals gh.phase_ref (slice_record fin c' t' f');
        R.op_Colon_Equals gh.fp_ref fp';
        fold (Alloc.is_phase gh.phase_ref (Alloc.phase_of (slice_record fin c' t' f')));
        fold (gen_phase gh (Alloc.phase_of (slice_record fin c' t' f')));
        fold (is_gen_heap gh 'd 'b s2 fp');
        fold (gc_state gh 'd 'b s2 fp' (Alloc.phase_of (slice_record fin c' t' f')));
        fin
      }
    }
  }
}
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
fn finish_sweep (gh: gen_heap_t)
  requires gc_state gh 'd 'b 's 'fp 'ph
  ensures exists* s2 fp2.
    gc_state gh 'd 'b s2 fp2 Ph.Idle **
    pure ((s2, fp2, Ph.Idle) == SL.phase_slice 's 'fp 'ph (pow2 64 - 1) /\
          GenInv.collection_heap_shape ({ data = 'd; bump = 'b } <: minor_state) s2 fp2)
{
  unfold gc_state;
  GI.phase_slice_finishes ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'ph (pow2 64 - 1);
  fold (gc_state gh 'd 'b 's 'fp 'ph);
  let fin = sweep_slice gh 0xFFFFFFFFFFFFFFFFUL;
  with s2 fp2 ph2. assert (gc_state gh 'd 'b s2 fp2 ph2);
  unfold gc_state;
  GI.phase_shape_idle ({ data = 'd; bump = 'b } <: minor_state) s2 fp2;
  rewrite (gen_phase gh ph2) as (gen_phase gh Ph.Idle);
  fold (gc_state gh 'd 'b s2 fp2 Ph.Idle);
}
#pop-options

/// ---------------------------------------------------------------------------
/// A minor collection at either phase
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let any_phase_pre (minor: minor_state) (s: heap) (fp: U64.t) (ph: Ph.gc_phase)
    (rs farr sl: Seq.seq U64.t) (n: nat)
  : Lemma (requires GI.phase_shape minor s fp ph /\ minor_slots_ok ph minor s rs farr sl n)
          (ensures minor_collect_pre_with (GI.phase_free s ph) minor s fp rs farr sl n /\
                   GC.Gen.Paint.phase_at ph s == ph /\
                   (Ph.Idle? ph \/ GC.Gen.Paint.colour_blind (GI.phase_free s ph)))
  = GI.phase_shape_collection minor s fp ph;
    GI.phase_free_ok minor s fp rs ph
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let any_phase_post (minor: minor_state) (s: heap) (fp: U64.t) (ph: Ph.gc_phase)
    (rs sl: Seq.seq U64.t) (n: nat) (ok: bool)
    (d2: minor_heap) (b2: U64.t) (s2: heap) (fp2: U64.t) (rs2 farr2: Seq.seq U64.t) (ph2: Ph.gc_phase)
  : Lemma (requires GI.phase_shape minor s fp ph /\
                    minor_collect_post_with_at ph (GI.phase_free s ph) minor s fp rs sl n
                      ok d2 b2 s2 fp2 rs2 farr2 ph2)
          (ensures GI.phase_shape ({ data = d2; bump = b2 } <: minor_state) s2 fp2 ph2 /\
                   Ph.Idle? ph2 == Ph.Idle? ph)
  = match ph with
    | Ph.Idle ->
        GI.phase_free_idle s;
        minor_collect_post_at_idle SpecFields.free_stw minor s fp rs sl n ok
          d2 b2 s2 fp2 rs2 farr2 ph2;
        CV.cheney_collect_spec_with_stw minor s fp rs;
        GI.phase_shape_idle minor s fp;
        CheneyPres.cheney_collect_preserves_collection_heap_shape minor s fp rs;
        GI.phase_shape_idle ({ data = d2; bump = b2 } <: minor_state) s2 fp2
    | Ph.Sweeping st ->
        GI.phase_free_sweeping s st;
        GI.minor_keeps_phase_shape minor s fp st rs
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
fn minor_collect_any_phase (gh: gen_heap_t)
                           (roots: array U64.t) (nroots: SZ.t)
                           (fwd_arr: array U64.t)
                           (queue: larray U64.t Cheney.queue_size)
                           (slots: array U64.t) (nslots: SZ.t)
  requires gc_state gh 'd 'b 's 'fp 'ph **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           pure (SZ.v nroots == Seq.length 'rs /\
                 minor_slots_ok 'ph ({ data = 'd; bump = 'b } <: minor_state) 's
                   'rs 'farr 'sl (SZ.v nslots))
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2 ph2.
    gc_state gh d2 b2 s2 fp2 ph2 **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    pure (minor_collect_post_with_at 'ph (GI.phase_free 's 'ph) ({ data = 'd; bump = 'b } <: minor_state)
            's 'fp 'rs 'sl (SZ.v nslots) ok d2 b2 s2 fp2 rs2 farr2 ph2 /\
          Ph.Idle? ph2 == Ph.Idle? 'ph)
{
  unfold gc_state;
  any_phase_pre ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'ph 'rs 'farr 'sl (SZ.v nslots);
  let ok = minor_collect_full gh roots nroots fwd_arr queue slots nslots
             #(hide (GI.phase_free 's 'ph));
  with d2 b2 s2 fp2. assert (is_gen_heap gh d2 b2 s2 fp2);
  with rs2. assert (pts_to roots rs2);
  with farr2. assert (pts_to fwd_arr farr2);
  with ph2. assert (gen_phase gh ph2);
  any_phase_post ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'ph 'rs 'sl (SZ.v nslots) ok
    d2 b2 s2 fp2 rs2 farr2 ph2;
  fold (gc_state gh d2 b2 s2 fp2 ph2);
  ok
}
#pop-options

/// ---------------------------------------------------------------------------
/// Major allocation at either phase
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let alloc_major_post_intro (ph: Ph.gc_phase) (minor: minor_state) (s: heap) (fp: U64.t)
    (wz: nat) (tag: GSP.tag_t)
  : Lemma (let ar = AC.alloc_phase s fp ph wz tag in
           alloc_major_post ph minor s fp wz tag (fst ar).SA.obj_out (fst ar).SA.heap_out
             (fst ar).SA.fp_out (snd ar))
  = let ar = AC.alloc_phase s fp ph wz tag in
    let aux (st: FS.sweep_state)
      : Lemma (requires ph == Ph.Sweeping st /\ GI.phase_shape minor s fp ph /\
                        tag <> GC.Spec.Object.infix_tag)
              (ensures (let st' = GSP.alloc_state s fp wz st in
                        let r = fst ar in
                        snd ar == Ph.Sweeping st' /\
                        (r.SA.obj_out == 0UL ==> r.SA.heap_out == s /\ r.SA.fp_out == fp /\ st' == st /\
                           GI.phase_shape minor r.SA.heap_out r.SA.fp_out (snd ar)) /\
                        (r.SA.obj_out <> 0UL ==>
                           GSP.new_block s r.SA.heap_out st r.SA.obj_out wz tag /\
                           GSP.fresh_ok r.SA.heap_out r.SA.fp_out st' (r.SA.obj_out <: obj_addr))))
      = GI.phase_shape_sweeping minor s fp st;
        GSP.alloc_sweep_phase s fp st wz tag
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
fn gen_alloc_major (gh: gen_heap_t) (wosize: U64.t) (tag: GSP.tag_t)
  requires is_gen_heap gh 'd 'b 's 'fp ** gen_phase gh 'ph ** pure (U64.v wosize >= 1)
  returns obj: U64.t
  ensures exists* s2 fp2 ph2.
    is_gen_heap gh 'd 'b s2 fp2 ** gen_phase gh ph2 **
    pure (alloc_major_post 'ph ({ data = 'd; bump = 'b } <: minor_state) 's 'fp
            (U64.v wosize) tag obj s2 fp2 ph2)
{
  unfold is_gen_heap;
  unfold gen_phase;
  let fp = R.op_Bang gh.fp_ref;
  let res = Alloc.allocate gh.major fp gh.phase_ref wosize tag;
  R.op_Colon_Equals gh.fp_ref (fst res);
  alloc_major_post_intro 'ph ({ data = 'd; bump = 'b } <: minor_state) 's 'fp (U64.v wosize) tag;
  fold (gen_phase gh (snd (AC.alloc_phase 's 'fp 'ph (U64.v wosize) tag)));
  fold (is_gen_heap gh 'd 'b _ _);
  snd res
}
#pop-options

/// ---------------------------------------------------------------------------
/// Starting the sweep phase
/// ---------------------------------------------------------------------------

module MarkBoundedImpl = GC.Impl.MarkBounded
module MarkCorr = GC.Spec.MarkBoundedCorrectness
module MajorGC = GC.Impl
module GMP = GC.Gen.MajorPrecondition
module CheneyCorr = GC.Gen.CheneyCorrectness
module SweepInv = GC.Spec.SweepInv

/// The phase record at the start of the sweep.
inline_for_extraction noextract
let start_record : Alloc.phase_state =
  { Alloc.ps_kind = 1UL; Alloc.ps_cursor = zero_addr;
    Alloc.ps_swept_tail = 0UL; Alloc.ps_last_fragment = 0UL }

let start_record_phase () : Lemma (Alloc.phase_of start_record == Ph.Sweeping FS.sweep_start) = ()

/// Marking leaves the heap `mark_post` describes, from which the sweep
/// phase starts.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let start_after_mark (minor: minor_state) (h: heap) (h_mark: heap)
    (st roots: Seq.seq obj_addr) (fp: U64.t) (cap: nat)
  : Lemma (requires MajorGC.gc_precondition_with_roots h st roots fp cap /\
                    SpecFields.well_formed_heap h_mark /\
                    SweepInv.no_gray_objects h_mark /\
                    SpecFields.objects zero_addr h_mark == SpecFields.objects zero_addr h /\
                    MarkCorr.mark_color_inv h h_mark /\
                    MarkCorr.gray_black_reachable h h_mark roots /\
                    MarkCorr.gray_stays h h_mark)
          (ensures SpecGCPost.mark_post h h_mark roots fp /\
                   GI.phase_shape (minor_reset minor) h_mark fp (Ph.Sweeping FS.sweep_start))
  = MarkCorr.mark_post_from_bounded_mark h h_mark roots fp;
    SpecGCPost.mark_post_sweep_pre h h_mark roots fp;
    SpecGCPost.mark_post_elim_no_grey h h_mark roots fp;
    SpecGCPost.mark_post_elim_tri_color h h_mark roots fp;
    SPI.sweep_phase_start h_mark fp;
    GI.phase_shape_start minor h_mark fp
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
fn gen_gc_start (gh: gen_heap_t)
                (roots: array U64.t) (nroots: SZ.t)
                (fwd_arr: array U64.t)
                (queue: larray U64.t Cheney.queue_size)
                (slots: array U64.t) (nslots: SZ.t)
                (st: gray_stack)
  requires gc_state gh 'd 'b 's 'fp Ph.Idle **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           is_gray_stack st 'st **
           pure (gen_gc_stack_budget 'rs 'st (stack_capacity st) /\
                 SZ.v nroots == Seq.length 'rs /\
                 Seq.length 'farr == UpdatePtrs.fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
                 RT.ref_table_sound 's 'sl (SZ.v nslots) /\
                 RT.ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
                 RT.slots_pairwise_distinct 'sl (SZ.v nslots) /\
                 MinorFwd.remembered_targets_in_roots 's 'rs 'sl (SZ.v nslots) /\
                 MinorFwd.roots_valid_for_minor_collection
                   ({ data = 'd; bump = 'b } <: minor_state) 's 'rs)
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 ph2 rs2 farr2 qv2 st2.
    gc_state gh d2 b2 s2 fp2 ph2 **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    is_gray_stack st st2 **
    pure (let minor_st : minor_state = { data = 'd; bump = 'b } in
          ({ data = d2; bump = b2 } <: minor_state) == minor_reset minor_st /\
          gen_gc_roots_post minor_st 's 'fp 'rs rs2 ok 'st (stack_capacity st) /\
          gen_gc_start_post minor_st 's 'fp 'rs ok s2 fp2 ph2 rs2 'st (stack_capacity st))
{
  unfold gc_state;
  GI.phase_shape_idle ({data = 'd; bump = 'b} <: minor_state) 's 'fp;
  GenInv.collection_heap_shape_elim ({data = 'd; bump = 'b} <: minor_state) 's 'fp;
  GenInv.major_heap_shape_elim 's 'fp;
  GenInv.major_heap_shape_walk 's 'fp;
  GenInv.minor_heap_shape_elim ({data = 'd; bump = 'b} <: minor_state);

  // The minor collection, on the `free_stw` definition (as in `gen_gc`).
  minor_collect_idle_pre ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'farr 'sl
    (SZ.v nslots);
  let ok = minor_collect_full gh roots nroots fwd_arr queue slots nslots
             #(hide SpecFields.free_stw);

  with d_mid b_mid ms_updated fp_mid. assert (is_gen_heap gh d_mid b_mid ms_updated fp_mid);
  with rs_mid. assert (pts_to roots rs_mid);
  with farr_mid. assert (pts_to fwd_arr farr_mid);
  with ph_mid. assert (gen_phase gh ph_mid);
  minor_collect_post_at_idle SpecFields.free_stw ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'sl
    (SZ.v nslots) ok d_mid b_mid ms_updated fp_mid rs_mid farr_mid ph_mid;
  rewrite (gen_phase gh ph_mid) as (gen_phase gh Ph.Idle);
  minor_collect_idle_post ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'farr 'sl
    (SZ.v nslots) ok d_mid b_mid ms_updated fp_mid rs_mid farr_mid;

  unfold is_gen_heap;
  let fp_val = R.op_Bang gh.fp_ref;
  PromoteSpec.rewrite_roots_length 'rs
    (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map;
  assert (pure (SZ.v nroots == Seq.length rs_mid));
  if ok {
    // Root darkening and marking, as `gen_gc` does them.
    MarkBoundedImpl.darken_roots_bounded gh.major st roots nroots (stack_capacity st);
    with prepared_major prepared_st roots_after. assert (
      is_heap gh.major prepared_major **
      is_gray_stack st prepared_st **
      pts_to roots roots_after);
    gen_gc_major_precondition_elim
      ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'st (stack_capacity st);
    assert (pure (MajorGC.gc_precondition_with_roots
      prepared_major prepared_st prepared_st fp_val (stack_capacity st)));
    MarkBoundedImpl.mark_loop_bounded gh.major st prepared_st;
    with s_mark st_mark. assert (is_heap gh.major s_mark ** is_gray_stack st st_mark);
    start_after_mark ({data = 'd; bump = 'b} <: minor_state) prepared_major s_mark
      prepared_st prepared_st fp_val (stack_capacity st);

    // Instead of sweeping: the sweep phase starts.
    unfold gen_phase;
    unfold Alloc.is_phase;
    R.op_Colon_Equals gh.phase_ref start_record;
    start_record_phase ();
    fold (Alloc.is_phase gh.phase_ref (Ph.Sweeping FS.sweep_start));
    fold (gen_phase gh (Ph.Sweeping FS.sweep_start));
    fold (is_gen_heap gh d_mid b_mid s_mark fp_val);
    fold (gc_state gh d_mid b_mid s_mark fp_val (Ph.Sweeping FS.sweep_start));
    ok
  } else {
    // Out of memory: as `gen_gc`, the major phase is skipped and the
    // collector stays idle, in the shape the minor collection left.
    GI.phase_shape_idle ({ data = d_mid; bump = b_mid } <: minor_state) ms_updated fp_val;
    fold (is_gen_heap gh d_mid b_mid ms_updated fp_val);
    fold (gc_state gh d_mid b_mid ms_updated fp_val Ph.Idle);
    ok
  }
}
#pop-options
