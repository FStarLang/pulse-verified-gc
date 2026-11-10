/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Sweep - the whole sweep, in Pulse
/// ---------------------------------------------------------------------------
///
/// - `start_sweep` computes exactly `GC.Spec.Pages.StartSweep.start_sweep`:
///   every page that is not free becomes unswept, and every list is emptied.
///   It does not visit the pages: it starts a new sweep epoch
///   (`State.start_epoch`) and clears the list heads, as OCaml 5's cycle
///   start only swaps list heads.  The heap is not touched.
/// - `sweep_all` computes exactly `GC.Spec.Pages.SweepAll.sweep_all`: it
///   sweeps every unit from page 0 on, a pool page with
///   `GC.Impl.Pages.SweepPage.pool_step` and a run with
///   `GC.Impl.Pages.SweepRun.run_step`, skipping free pages and units
///   already swept, and moves to the next unit (`span`).
///   Its precondition is `map_ok` of the map it starts from, which the sweep's
///   own precondition `sweep_ready` includes: each run's pages are then run
///   pages when the sweep reaches it, since a step changes only its own
///   unit's entries (`step_frame`).
/// - `sweep` is the two together, the collector's step after the mark.

module GC.Impl.Pages.Sweep

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Impl.Heap
open GC.Impl.Pages.Params
open GC.Impl.Pages.State

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq
module R = Pulse.Lib.Reference
module Base = GC.Spec.Base
module FLs = GC.Spec.FreeLists
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun
module SS = GC.Spec.Pages.SweepStep
module SA = GC.Spec.Pages.SweepAll
module SSt = GC.Spec.Pages.StartSweep
module RM = GC.Spec.Pages.RunMap
module Ce = GC.Spec.Pages.Cells
module RML = GC.Impl.Pages.RunMapLemmas
module PL = GC.Impl.Pages.Pool
module ISP = GC.Impl.Pages.SweepPage
module ISR = GC.Impl.Pages.SweepRun

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The step before the sweep
/// ---------------------------------------------------------------------------

let start_eq (st: pstate)
  : Lemma (({ ({ st with pm = unswept_map st.pm }) with avail = Seq.create n_cls 0UL; large = FLs.fls_empty })
           == SSt.start_sweep st)
  = let aux (i: nat{i < n_pages}) : Lemma (Seq.index (unswept_map st.pm) i == Seq.index (SSt.clear_map st.pm) i)
      = SSt.clear_entry st.pm i
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro (unswept_map st.pm) (SSt.clear_map st.pm)

fn start_sweep (t: pstate_t) (#st: erased pstate)
  requires pages_st t st
  ensures pages_st t (SSt.start_sweep st)
{
  start_epoch t;
  clear_lists t;
  start_eq st;
  rewrite (pages_st t ({ ({ reveal st with pm = unswept_map st.pm }) with avail = Seq.create n_cls 0UL; large = FLs.fls_empty }))
       as (pages_st t (SSt.start_sweep st))
}

/// ---------------------------------------------------------------------------
/// The sweep, a unit at a time
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let sweep_from_step (g: Base.heap) (st: pstate) (p: nat)
  : Lemma (requires p < n_pages)
          (ensures SA.sweep_from g st p ==
                   (let k = span st.pm p in
                    let (g', st') = SA.step g st p in
                    SA.sweep_from g' st' (p + k)))
  = ()

let sweep_from_end (g: Base.heap) (st: pstate) (p: nat)
  : Lemma (requires p >= n_pages) (ensures SA.sweep_from g st p == (g, st))
  = ()
#pop-options

/// The step, by the kind of the unit.
let step_swept (g: Base.heap) (st: pstate) (p: nat{p < n_pages})
  : Lemma (requires (entry st.pm p).swept) (ensures SA.step g st p == (g, st))
  = ()

let step_pool (g: Base.heap) (st: pstate) (p: nat{p < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires not (entry st.pm p).swept /\ (entry st.pm p).kind == Pool c)
          (ensures SA.step g st p ==
                   (fst (SP.sweep_page g st.pm p), SS.push_avail st p (snd (SP.sweep_page g st.pm p))))
  = ()

let step_run (g: Base.heap) (st: pstate) (p: nat{p < n_pages}) (n: pos)
  : Lemma (requires not (entry st.pm p).swept /\ (entry st.pm p).kind == LargeHead n)
          (ensures SA.step g st p ==
                   (Mktuple3?._1 (SR.sweep_run g st.pm p (Ce.large_head st)),
                    SS.run_state st (Mktuple3?._2 (SR.sweep_run g st.pm p (Ce.large_head st)))
                                    (Mktuple3?._3 (SR.sweep_run g st.pm p (Ce.large_head st)))))
  = ()

let step_other (g: Base.heap) (st: pstate) (p: nat{p < n_pages})
  : Lemma (requires not (entry st.pm p).swept /\ ~(Pool? (entry st.pm p).kind) /\ ~(LargeHead? (entry st.pm p).kind))
          (ensures SA.step g st p == (g, st))
  = ()

/// The entries from `p` on are those the sweep started with.
let ahead (pm0 pm: page_map) (p: nat) : prop =
  forall (j: nat{j < n_pages}). j >= p ==> entry pm j == entry pm0 j

/// A run the sweep reaches has its run pages.
let run_reached (pm0 pm: page_map) (p: nat{p < n_pages}) (n: pos)
  : Lemma (requires map_ok pm0 /\ ahead pm0 pm p /\ (entry pm p).kind == LargeHead n)
          (ensures RML.run_pages pm p n)
  = assert (run_ok pm0 p)

/// Each step changes only its own unit's entries.
let pool_frame (st: pstate) (p: nat{p < n_pages}) (e: page_info) (j: nat{j < n_pages})
  : Lemma (requires j > p) (ensures entry (SS.push_avail st p e).pm j == entry st.pm j)
  = ()

let run_frame (pm: page_map) (fs: list GC.Spec.Pages.Blk.blk) (h n: nat) (j: nat{j < n_pages})
  : Lemma (requires j >= h + n) (ensures entry (RM.new_map pm fs h n) j == entry pm j)
  = RM.new_map_entry pm fs h n j

let run_ahead (g: Base.heap) (st0 st: pstate) (p: nat{p < n_pages}) (n: pos)
  : Lemma (requires ahead st0.pm st.pm p /\ (entry st.pm p).kind == LargeHead n)
          (ensures ahead st0.pm (SS.run_state st (Mktuple3?._2 (SR.sweep_run g st.pm p (Ce.large_head st)))
                                                  (Mktuple3?._3 (SR.sweep_run g st.pm p (Ce.large_head st)))).pm
                         (p + n))
  = let fs = GC.Spec.Pages.RunList.fin g (page_base p) (page_base (p + n)) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (run_frame st.pm fs p n))

let pool_ahead (g: Base.heap) (st0 st: pstate) (p: nat{p < n_pages})
  : Lemma (requires ahead st0.pm st.pm p)
          (ensures ahead st0.pm (SS.push_avail st p (snd (SP.sweep_page g st.pm p))).pm (p + 1))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (pool_frame st p (snd (SP.sweep_page g st.pm p))))

let ahead_more (pm0 pm: page_map) (p q: nat)
  : Lemma (requires ahead pm0 pm p /\ p <= q) (ensures ahead pm0 pm q)
  = ()

/// The next unit is in the heap's pages.
let next_bound (pm0 pm: page_map) (p: nat{p < n_pages})
  : Lemma (requires map_ok pm0 /\ ahead pm0 pm p) (ensures p + span pm p <= n_pages)
  = assert (run_ok pm0 p)

fn sweep_all (heap: heap_t) (t: pstate_t) (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st ** pure (map_ok st.pm)
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' ** pure ((g', st') == SA.sweep_all 'g st)
{
  let np = n_pages_u64 ();
  let mut p = 0UL;
  while (U64.lt !p np)
    invariant exists* vp g1 st1.
      R.pts_to p vp ** is_heap heap g1 ** pages_st t st1 **
      pure (U64.v vp <= n_pages /\ ahead st.pm st1.pm (U64.v vp) /\
            SA.sweep_from g1 st1 (U64.v vp) == SA.sweep_all 'g st)
    decreases (n_pages - U64.v !p)
  {
    let vp = !p;
    with g1 st1. assert (is_heap heap g1 ** pages_st t st1);
    sweep_from_step g1 st1 (U64.v vp);
    next_bound st.pm st1.pm (U64.v vp);
    let r = read_entry t vp;
    if (r.swept) {
      step_swept g1 st1 (U64.v vp);
      ahead_more st.pm st1.pm (U64.v vp) (U64.v vp + span st1.pm (U64.v vp));
      if (is_head r) {
        p := U64.add vp r.arg
      } else {
        p := U64.add vp 1UL
      }
    } else {
      if (is_pool r) {
        step_pool g1 st1 (U64.v vp) (U64.v r.arg);
        pool_ahead g1 st st1 (U64.v vp);
        ISP.pool_step heap t vp r;
        p := U64.add vp 1UL
      } else {
        if (is_head r) {
          step_run g1 st1 (U64.v vp) (U64.v r.arg);
          run_reached st.pm st1.pm (U64.v vp) (U64.v r.arg);
          run_ahead g1 st st1 (U64.v vp) (U64.v r.arg);
          ISR.run_step heap t vp r;
          p := U64.add vp r.arg
        } else {
          step_other g1 st1 (U64.v vp);
          ahead_more st.pm st1.pm (U64.v vp) (U64.v vp + 1);
          p := U64.add vp 1UL
        }
      }
    }
  };
  with g1 st1. assert (is_heap heap g1 ** pages_st t st1);
  let vp = !p;
  assert (pure (U64.v vp >= n_pages));
  sweep_from_end g1 st1 (U64.v vp);
  assert (pure (SA.sweep_from g1 st1 (U64.v vp) == (reveal g1, reveal st1)))
}

/// ---------------------------------------------------------------------------
/// The collector's step after the mark
/// ---------------------------------------------------------------------------

/// Clear the lists and mark the pages unswept, then sweep every unit:
/// `sweep_all g (start_sweep st)`, which `StartSweep.collection_cycle`
/// proves returns the allocator to its `Idle` invariant.
fn sweep (heap: heap_t) (t: pstate_t) (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st ** pure (map_ok st.pm)
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st') == SA.sweep_all 'g (SSt.start_sweep st))
{
  start_sweep t;
  SSt.clear_map_ok st.pm;
  sweep_all heap t
}
