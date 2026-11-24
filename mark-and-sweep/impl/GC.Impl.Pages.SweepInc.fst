/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.SweepInc - the incremental page sweep, in Pulse
/// ---------------------------------------------------------------------------
///
/// Plan §28.  The sweep of incremental mode, a unit at a time, between
/// allocations:
///   - `sweep_unit` sweeps the unit at page `p` and returns the page after
///     it: exactly the model's sweep step, `GC.Spec.Pages.SweepAll.step`,
///     the page cycle's sweep event (`CSStep p`), for every `p`.  A unit
///     already swept, a free page and a continuation page are left as they
///     are.
///   - `sweep_slice` sweeps from the cursor `c` until `budget` units are
///     swept or the pages end, and returns the new cursor: exactly
///     `GC.Spec.Pages.Incr.slice_from`, which is a sequence of sweep steps
///     (`GC.Spec.Pages.Cycle.Incr.slice_events`).
/// The sweep starts with `GC.Impl.Pages.Sweep.start_sweep` (the model's
/// `StartSweep.start_sweep`: a new epoch, so every page in use reads as
/// unswept) and the cursor at 0; it may end once the cursor reaches the
/// end of the pages (`Incr.cursor_end`).  Each needs only `map_ok`, which the
/// mid-sweep invariant includes; so allocations (`GC.Impl.Pages.AllocInc`)
/// and sweep steps may come in any order.

module GC.Impl.Pages.SweepInc

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Impl.Heap
open GC.Impl.Pages.Params
open GC.Impl.Pages.State

module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
module Base = GC.Spec.Base
module SA = GC.Spec.Pages.SweepAll
module Inc = GC.Spec.Pages.Incr
module IS = GC.Impl.Pages.Sweep
module ISP = GC.Impl.Pages.SweepPage
module ISR = GC.Impl.Pages.SweepRun

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// One unit
/// ---------------------------------------------------------------------------

/// **One unit**: the model's sweep step at `p`; returns the page after the
/// unit.
fn sweep_unit (heap: heap_t) (t: pstate_t) (vp: U64.t{U64.v vp < n_pages}) (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st ** pure (map_ok st.pm)
  returns q: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st') == SA.step 'g st (U64.v vp) /\
                U64.v q == U64.v vp + span st.pm (U64.v vp) /\ U64.v q <= n_pages)
{
  IS.next_bound st.pm st.pm (U64.v vp);
  let r = read_entry t vp;
  if (r.swept) {
    IS.step_swept 'g st (U64.v vp);
    if (is_head r) {
      U64.add vp r.arg
    } else {
      U64.add vp 1UL
    }
  } else {
    if (is_pool r) {
      IS.step_pool 'g st (U64.v vp) (U64.v r.arg);
      ISP.pool_step heap t vp r;
      U64.add vp 1UL
    } else {
      if (is_head r) {
        IS.step_run 'g st (U64.v vp) (U64.v r.arg);
        IS.run_reached st.pm st.pm (U64.v vp) (U64.v r.arg);
        ISR.run_step heap t vp r;
        U64.add vp r.arg
      } else {
        IS.step_other 'g st (U64.v vp);
        U64.add vp 1UL
      }
    }
  }
}

/// ---------------------------------------------------------------------------
/// A slice
/// ---------------------------------------------------------------------------

/// The step's budget: one less when it sweeps a unit.
let budget_pool (pm: page_map) (p: nat{p < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires not (entry pm p).swept /\ (entry pm p).kind == Pool c) (ensures Inc.sweeps pm p)
  = ()

let budget_head (pm: page_map) (p: nat{p < n_pages}) (n: pos)
  : Lemma (requires not (entry pm p).swept /\ (entry pm p).kind == LargeHead n) (ensures Inc.sweeps pm p)
  = ()

/// **A slice**: sweep units from the cursor `c` until `budget` of them are
/// swept or the pages end (`Incr.slice_from`); returns the new cursor.
fn sweep_slice (heap: heap_t) (t: pstate_t) (c: U64.t) (budget: U64.t) (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st ** pure (map_ok st.pm /\ U64.v c <= n_pages)
  returns q: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', U64.v q) == Inc.slice_from 'g st (U64.v c) (U64.v budget))
{
  let np = n_pages_u64 ();
  let mut p = c;
  let mut n = budget;
  IS.ahead_more st.pm st.pm 0 (U64.v c);
  while (U64.lt !p np && U64.gt !n 0UL)
    invariant exists* vp vn g1 st1.
      R.pts_to p vp ** R.pts_to n vn ** is_heap heap g1 ** pages_st t st1 **
      pure (U64.v vp <= n_pages /\ IS.ahead st.pm st1.pm (U64.v vp) /\
            Inc.slice_from g1 st1 (U64.v vp) (U64.v vn) == Inc.slice_from 'g st (U64.v c) (U64.v budget))
    decreases (n_pages - U64.v !p)
  {
    let vp = !p;
    let vn = !n;
    with g1 st1. assert (is_heap heap g1 ** pages_st t st1);
    Inc.slice_unfold g1 st1 (U64.v vp) (U64.v vn);
    IS.next_bound st.pm st1.pm (U64.v vp);
    let r = read_entry t vp;
    if (r.swept) {
      IS.step_swept g1 st1 (U64.v vp);
      IS.ahead_more st.pm st1.pm (U64.v vp) (U64.v vp + span st1.pm (U64.v vp));
      if (is_head r) {
        p := U64.add vp r.arg
      } else {
        p := U64.add vp 1UL
      }
    } else {
      if (is_pool r) {
        IS.step_pool g1 st1 (U64.v vp) (U64.v r.arg);
        budget_pool st1.pm (U64.v vp) (U64.v r.arg);
        IS.pool_ahead g1 st st1 (U64.v vp);
        ISP.pool_step heap t vp r;
        p := U64.add vp 1UL;
        n := U64.sub vn 1UL
      } else {
        if (is_head r) {
          IS.step_run g1 st1 (U64.v vp) (U64.v r.arg);
          budget_head st1.pm (U64.v vp) (U64.v r.arg);
          IS.run_reached st.pm st1.pm (U64.v vp) (U64.v r.arg);
          IS.run_ahead g1 st st1 (U64.v vp) (U64.v r.arg);
          ISR.run_step heap t vp r;
          p := U64.add vp r.arg;
          n := U64.sub vn 1UL
        } else {
          IS.step_other g1 st1 (U64.v vp);
          IS.ahead_more st.pm st1.pm (U64.v vp) (U64.v vp + 1);
          p := U64.add vp 1UL
        }
      }
    }
  };
  with g1 st1. assert (is_heap heap g1 ** pages_st t st1);
  let vp = !p;
  let vn = !n;
  Inc.slice_unfold g1 st1 (U64.v vp) (U64.v vn);
  assert (pure (Inc.slice_from g1 st1 (U64.v vp) (U64.v vn) == (reveal g1, reveal st1, U64.v vp)));
  vp
}
