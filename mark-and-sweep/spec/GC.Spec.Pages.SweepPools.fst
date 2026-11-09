/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepPools - a swept pool page holds a live object
/// ---------------------------------------------------------------------------
///
/// After `sweep_all`, every page that is still a pool page has a used slot:
/// the page sweep gives a page with no survivor back as a `Free` page, and
/// the run sweep makes no pool page (`sweep_page_ok`, `run_pages_ok`).  So a
/// pool page with no live slot is `Free`, as plan §2.3 (c1) asks.
///
/// The fact is carried page by page with `GC.Spec.Pages.SweepAll.inv`: a
/// step at `p` keeps the entries and words of the pages before `p`.

module GC.Spec.Pages.SweepPools

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Theorems
open GC.Spec.Pages.SweepAll

module U64 = FStar.UInt64
module Seq = FStar.Seq
module FR = GC.Spec.Pages.Frame
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun
module SS = GC.Spec.Pages.SweepStep
module SW = GC.Spec.Pages.SweepWf

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// Page `i`, if a pool page, has a used slot.
let pool_live (g: heap) (st: pstate) (i: nat{i < n_pages}) : prop =
  forall (c: nat{c < n_cls}). (entry st.pm i).kind == Pool c ==>
    (exists (k: nat). k < n_slots c /\ slot_used g i c k)

let pools_before (g: heap) (st: pstate) (p: nat) : prop =
  forall (i: nat{i < n_pages}). i < p ==> pool_live g st i

/// A step at `p` keeps the entries below `p`.
let step_entries (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages})
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p)
          (ensures (let (_, st') = step g st p in
                    forall (j: nat{j < n_pages}). j < p ==> entry st'.pm j == entry st.pm j))
  = inv_elim g0 st0 g st p;
    if (entry st.pm p).swept then ()
    else match (entry st.pm p).kind with
      | Pool c ->
        let (g', e) = SP.sweep_page g st.pm p in
        SS.push_entry st p e
      | LargeHead _ ->
        marked_run_at g0 g st0 st p;
        SR.sweep_run_correct ();
        let (g', pm', fp') = SR.sweep_run g st.pm p (GC.Spec.Pages.Cells.large_head st) in
        assert (sweep_run_ok g st.pm p (GC.Spec.Pages.Cells.large_head st) g' pm' fp')
      | _ -> ()

/// A used slot of a page below `p` stays used.
let kept_live (g g': heap) (st st': pstate) (p: nat) (i: nat{i < n_pages})
  : Lemma (requires pool_live g st i /\ i < p /\ p <= n_pages /\ entry st'.pm i == entry st.pm i /\
                    (forall (x: hp_addr). U64.v x < page_base p ==> read_word g' x == read_word g x))
          (ensures pool_live g' st' i)
  = page_base_mono (i + 1) p;
    let one (c: nat{c < n_cls})
      : Lemma ((entry st'.pm i).kind == Pool c ==> (exists (k: nat). k < n_slots c /\ slot_used g' i c k))
      = if (entry st'.pm i).kind = Pool c then
          eliminate exists (k: nat). k < n_slots c /\ slot_used g i c k
          with begin
            FR.slot_kept g g' i c k;
            FR.slot_frame g g' i c k
          end
    in
    FStar.Classical.forall_intro one

/// A swept pool page that stays a pool page kept a survivor.
let pool_new (g: heap) (st: pstate) (p: nat{p < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires marked_pool_page g st.pm p c)
          (ensures (let (g1, e) = SP.sweep_page g st.pm p in pool_live g1 (SS.push_avail st p e) p))
  = SP.sweep_page_correct ();
    let (g1, e) = SP.sweep_page g st.pm p in
    assert (sweep_page_ok g st.pm p c g1 e);
    SS.push_entry st p e;
    if FStar.IndefiniteDescription.strong_excluded_middle
         (exists (k: nat). k < n_slots c /\ slot_used g p c k /\ color_at g (slot_base p c k) == Black)
    then
      eliminate exists (k: nat). k < n_slots c /\ slot_used g p c k /\ color_at g (slot_base p c k) == Black
      with assert (slot_used g1 p c k)

/// The step at a pool page.
let step_pool (g: heap) (st: pstate) (p: nat{p < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires (entry st.pm p).kind == Pool c /\ not (entry st.pm p).swept)
          (ensures span st.pm p == 1 /\
                   step g st p == (let (g1, e) = SP.sweep_page g st.pm p in (g1, SS.push_avail st p e)))
  = ()

/// The new pages of the step at `p`.
let new_live (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages}) (i: nat{i < n_pages})
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p /\ p <= i /\ i < p + span st.pm p)
          (ensures (let (g', st') = step g st p in pool_live g' st' i))
  = inv_elim g0 st0 g st p;
    let (g', st') = step g st p in
    assert (entry st.pm p == entry st0.pm p);
    if (entry st.pm p).swept then ()
    else match (entry st.pm p).kind with
      | Pool c ->
        marked_pool_at g0 g st0 st p c;
        step_pool g st p c;
        assert (i == p);
        pool_new g st p c
      | LargeHead n ->
        marked_run_at g0 g st0 st p;
        SR.sweep_run_correct ();
        let (g1, pm', fp') = SR.sweep_run g st.pm p (GC.Spec.Pages.Cells.large_head st) in
        assert (sweep_run_ok g st.pm p (GC.Spec.Pages.Cells.large_head st) g1 pm' fp');
        assert (run_pages_ok g1 pm' p n)
      | _ -> ()

let pools_step (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages})
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p /\ pools_before g st p)
          (ensures (let (g', st') = step g st p in pools_before g' st' (p + span st.pm p)))
  = SW.step_frame g0 g st0 st p;
    step_entries g0 g st0 st p;
    let (g', st') = step g st p in
    let one (i: nat{i < n_pages})
      : Lemma (i < p + span st.pm p ==> pool_live g' st' i)
      = if i < p then kept_live g g' st st' p i
        else if i < p + span st.pm p then new_live g0 g st0 st p i
    in
    FStar.Classical.forall_intro one

#push-options "--fuel 1"
let rec pools_from (g0 g: heap) (st0 st: pstate) (p: nat)
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p /\ pools_before g st p)
          (ensures (let (g', st') = sweep_from g st p in pools_before g' st' n_pages))
          (decreases (if p < n_pages then n_pages - p else 0))
  = inv_bound g0 st0 g st p;
    if p >= n_pages then ()
    else begin
      pools_step g0 g st0 st p;
      inv_step g0 g st0 st p;
      let (g', st') = step g st p in
      pools_from g0 g' st0 st' (p + span st.pm p)
    end
#pop-options

/// **After the whole sweep, every pool page holds a live object.**
let sweep_all_pools (g: heap) (st: pstate)
  : Lemma (requires sweep_ready g st)
          (ensures (let (g', st') = sweep_all g st in
                    forall (i: nat{i < n_pages}). pool_live g' st' i))
  = inv_init g st;
    pools_from g g st st 0
