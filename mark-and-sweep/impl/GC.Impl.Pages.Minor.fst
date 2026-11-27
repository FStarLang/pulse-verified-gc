/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Minor - the minor collection with the page allocator
/// ---------------------------------------------------------------------------
///
/// Plan §30.  akhil's `GC.Gen.Impl.minor_collect_with`, with the page
/// allocator: the Cheney promotion (`GC.Impl.Pages.Cheney.promote_all`),
/// then his pointer update in two passes, the promoted objects and the
/// remembered slots, and his root rewriting (`GC.Gen.Impl.UpdatePtrs`,
/// unchanged), then the nursery reset (`GC.Gen.Impl.MinorHeap`, unchanged).
///
/// `minor_collect` is **exactly the model's minor collection**
/// (`Spec.Pages.Promote.collect a`: major heap, page state, nursery and
/// roots), for any allocator `a` that is the page allocator of the phase
/// (`Sim.at_phase`), given the write barrier's remembered set for what `a`
/// counts as free.  The two passes are the model's pointer update by
/// `Promote.TwoPass.two_pass`.
///
/// The instances, each exactly the model's collection of its phase:
///   * `minor_collect_idle`: `Promote.Idle.icollect`, from `ipre`;
///   * `minor_collect_marking`: `Promote.Mark.mcollect`, from `mpre_mark`;
///   * `minor_collect_sweeping`: `Promote.Sweep.scollect`, from `spre`.
///
/// `ok` is false exactly when an allocation failed (`Promote.Fail.failed`);
/// the collection is then still the model's, which skips that object.  It
/// reads only what it follows (`Loop.cpre_w`, design doc §12).

module GC.Impl.Pages.Minor

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.ForwardingArray
open GC.Gen.RefTable
open GC.Gen.Impl.UpdatePtrs
open GC.Impl.Heap
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Impl.Pages.State
open GC.Gen.Promote
open GC.Spec.Pages.Promote
open GC.Impl.Pages.Forward
open GC.Impl.Pages.Cheney

module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq
module I = GC.Spec.AllocIface
module Sim = GC.Spec.Pages.Promote.Sim
module L = GC.Spec.Pages.Promote.Loop
module TwoPass = GC.Spec.Pages.Promote.TwoPass
module GenInv = GC.Gen.HeapInvariant
module PI = GC.Spec.Pages.PromoteInst
module PId = GC.Spec.Pages.Promote.Idle
module PM = GC.Spec.Pages.Promote.Mark
module PS = GC.Spec.Pages.Promote.Sweep
module MS = GC.Spec.Pages.MidSweep
module Fl = GC.Spec.Pages.Promote.Fail
module Gd = GC.Spec.Pages.Promote.Guard

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// The nursery after the reset is the model's.
let reset_is (ms: minor_state)
  : Lemma (mst (Seq.create minor_heap_size 0uy) 0UL == minor_reset ms)
  = let r = minor_reset ms in
    assert (r.bump == 0UL);
    assert (r == { data = r.data; bump = r.bump })

/// **The minor collection**: exactly the model's `collect a`.  The
/// forwarding array must be zero on entry.
#push-options "--z3rlimit 30"
fn minor_collect (minor: minor_heap_t) (major: heap_t) (t: pstate_t) (marking: bool)
  (roots: array U64.t) (nroots: SZ.t) (fwd_arr queue: array U64.t) (slots: array U64.t) (nslots: SZ.t)
  (#a: erased (tal pstate)) (#ph: erased I.phase)
  requires is_minor minor 'md 'mb ** is_heap major 'g ** pages_st t 'st **
           pts_to roots 'rs ** pts_to fwd_arr 'farr ** pts_to queue 'qv ** pts_to slots 'sl **
           pure (Sim.at_phase a ph /\ marking == I.Marking? ph /\
                 L.cpre_w a (mst 'md 'mb) 'g 'st 'rs /\
                 Gd.fields_gd (mst 'md 'mb) /\ Gd.roots_gd (mst 'md 'mb) 'rs /\
                 Seq.length 'farr == fwd_array_size /\
                 (forall (i: nat). i < fwd_array_size ==> Seq.index 'farr i == 0UL) /\
                 Seq.length 'qv == queue_size /\ SZ.v nroots == Seq.length 'rs /\
                 ref_table_sound_with a.free 'g 'sl (SZ.v nslots) /\
                 ref_table_covers_with a.free 'g 'sl (SZ.v nslots))
  returns ok: bool
  ensures exists* d' b' g' st' rs' farr' qv'.
          is_minor minor d' b' ** is_heap major g' ** pages_st t st' **
          pts_to roots rs' ** pts_to fwd_arr farr' ** pts_to queue qv' ** pts_to slots 'sl **
          pure (let r = collect a (mst 'md 'mb) 'g 'st 'rs in
                ok == not (Fl.failed a (mst 'md 'mb) 'g 'st 'rs) /\
                g' == r.rmajor /\ st' == r.rst /\ mst d' b' == r.rminor /\ rs' == r.rroots)
{
  let ok = promote_all minor major t marking fwd_arr queue roots nroots #a #ph;
  with g1 farr1. assert (is_heap major g1 ** pts_to fwd_arr farr1);
  TwoPass.two_pass a (mst 'md 'mb) 'g 'st 'rs farr1 'sl (SZ.v nslots);
  update_promoted_objects major fwd_arr #(promote a (mst 'md 'mb) 'g 'st 'rs).fwd;
  rewrite_heap_slots major fwd_arr slots nslots #(promote a (mst 'md 'mb) 'g 'st 'rs).fwd;
  rewrite_roots_impl roots fwd_arr nroots #(promote a (mst 'md 'mb) 'g 'st 'rs).fwd;
  minor_heap_reset minor;
  reset_is (mst 'md 'mb);
  ok
}
#pop-options

/// ---------------------------------------------------------------------------
/// The instances
/// ---------------------------------------------------------------------------

/// **Idle**: exactly `Promote.Idle.icollect`.
#push-options "--z3rlimit 30"
fn minor_collect_idle (minor: minor_heap_t) (major: heap_t) (t: pstate_t)
  (roots: array U64.t) (nroots: SZ.t) (fwd_arr queue: array U64.t) (slots: array U64.t) (nslots: SZ.t)
  requires is_minor minor 'md 'mb ** is_heap major 'g ** pages_st t 'st **
           pts_to roots 'rs ** pts_to fwd_arr 'farr ** pts_to queue 'qv ** pts_to slots 'sl **
           pure (PId.ipre (mst 'md 'mb) 'g 'st /\
                 Seq.length 'farr == fwd_array_size /\
                 (forall (i: nat). i < fwd_array_size ==> Seq.index 'farr i == 0UL) /\
                 Seq.length 'qv == queue_size /\ SZ.v nroots == Seq.length 'rs /\
                 ref_table_sound_with free_stw 'g 'sl (SZ.v nslots) /\
                 ref_table_covers_with free_stw 'g 'sl (SZ.v nslots))
  returns ok: bool
  ensures exists* d' b' g' st' rs' farr' qv'.
          is_minor minor d' b' ** is_heap major g' ** pages_st t st' **
          pts_to roots rs' ** pts_to fwd_arr farr' ** pts_to queue qv' ** pts_to slots 'sl **
          pure (let r = PId.icollect (mst 'md 'mb) 'g 'st 'rs in
                g' == r.rmajor /\ st' == r.rst /\ mst d' b' == r.rminor /\ rs' == r.rroots)
{
  Sim.idle_at ();
  PId.idle_contract ();
  GenInv.minor_heap_shape_elim (mst 'md 'mb);
  Gd.gd_of_complete (mst 'md 'mb) 'rs;
  contract_wf PId.idle_tal 'g 'st;
  L.cpre_weaken PId.idle_tal (mst 'md 'mb) 'g 'st 'rs;
  minor_collect minor major t false roots nroots fwd_arr queue slots nslots #PId.idle_tal #I.Idle
}
#pop-options

/// **Marking**: exactly `Promote.Mark.mcollect`.
#push-options "--z3rlimit 30"
fn minor_collect_marking (minor: minor_heap_t) (major: heap_t) (t: pstate_t)
  (roots: array U64.t) (nroots: SZ.t) (fwd_arr queue: array U64.t) (slots: array U64.t) (nslots: SZ.t)
  requires is_minor minor 'md 'mb ** is_heap major 'g ** pages_st t 'st **
           pts_to roots 'rs ** pts_to fwd_arr 'farr ** pts_to queue 'qv ** pts_to slots 'sl **
           pure (PM.mpre_mark (mst 'md 'mb) 'g 'st /\
                 Seq.length 'farr == fwd_array_size /\
                 (forall (i: nat). i < fwd_array_size ==> Seq.index 'farr i == 0UL) /\
                 Seq.length 'qv == queue_size /\ SZ.v nroots == Seq.length 'rs /\
                 ref_table_sound_with free_stw 'g 'sl (SZ.v nslots) /\
                 ref_table_covers_with free_stw 'g 'sl (SZ.v nslots))
  returns ok: bool
  ensures exists* d' b' g' st' rs' farr' qv'.
          is_minor minor d' b' ** is_heap major g' ** pages_st t st' **
          pts_to roots rs' ** pts_to fwd_arr farr' ** pts_to queue qv' ** pts_to slots 'sl **
          pure (let r = PM.mcollect (mst 'md 'mb) 'g 'st 'rs in
                g' == r.rmajor /\ st' == r.rst /\ mst d' b' == r.rminor /\ rs' == r.rroots)
{
  Sim.mark_at ();
  PM.mpre_facts (mst 'md 'mb) 'g 'st;
  GenInv.minor_heap_shape_elim (mst 'md 'mb);
  Gd.gd_of_complete (mst 'md 'mb) 'rs;
  L.cpre_weaken PI.mark_tal (mst 'md 'mb) 'g 'st 'rs;
  minor_collect minor major t true roots nroots fwd_arr queue slots nslots #PI.mark_tal #I.Marking
}
#pop-options

/// **Mid-sweep**: exactly `Promote.Sweep.scollect`.
#push-options "--z3rlimit 30"
fn minor_collect_sweeping (minor: minor_heap_t) (major: heap_t) (t: pstate_t)
  (roots: array U64.t) (nroots: SZ.t) (fwd_arr queue: array U64.t) (slots: array U64.t) (nslots: SZ.t)
  requires is_minor minor 'md 'mb ** is_heap major 'g ** pages_st t 'st **
           pts_to roots 'rs ** pts_to fwd_arr 'farr ** pts_to queue 'qv ** pts_to slots 'sl **
           pure (PS.spre (mst 'md 'mb) 'g 'st /\
                 Seq.length 'farr == fwd_array_size /\
                 (forall (i: nat). i < fwd_array_size ==> Seq.index 'farr i == 0UL) /\
                 Seq.length 'qv == queue_size /\ SZ.v nroots == Seq.length 'rs /\
                 ref_table_sound_with (MS.free_sw 'st.pm) 'g 'sl (SZ.v nslots) /\
                 ref_table_covers_with (MS.free_sw 'st.pm) 'g 'sl (SZ.v nslots))
  returns ok: bool
  ensures exists* d' b' g' st' rs' farr' qv'.
          is_minor minor d' b' ** is_heap major g' ** pages_st t st' **
          pts_to roots rs' ** pts_to fwd_arr farr' ** pts_to queue qv' ** pts_to slots 'sl **
          pure (let r = PS.scollect (mst 'md 'mb) 'g 'st 'rs in
                g' == r.rmajor /\ st' == r.rst /\ mst d' b' == r.rminor /\ rs' == r.rroots)
{
  Sim.sw_at (reveal 'st).pm;
  PI.sw_contract (reveal 'st).pm;
  GenInv.minor_heap_shape_elim (mst 'md 'mb);
  Gd.gd_of_complete (mst 'md 'mb) 'rs;
  contract_wf (PI.sw_tal (reveal 'st).pm) 'g 'st;
  L.cpre_weaken (PI.sw_tal (reveal 'st).pm) (mst 'md 'mb) 'g 'st 'rs;
  minor_collect minor major t false roots nroots fwd_arr queue slots nslots
    #(PI.sw_tal (reveal 'st).pm) #I.Sweeping
}
#pop-options
