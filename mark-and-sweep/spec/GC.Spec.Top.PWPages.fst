/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWPages - the page map along a pages witness run
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  The pages witness runs (GC.Spec.Top.PWSeq, PWInc) never
/// compute where the page allocator puts a block.  They need two facts about
/// the page map:
///   - **room**: every allocation of the runs succeeds.  The budget
///     `kinds_ok st j` (pages from `j` on are free, every page is free or a
///     pool page) gives a free page while `j < n_pages`, so the capacity
///     condition holds (`room_of`).  A small allocation changes the kind of
///     one page only, the first free one (`Witness.small_kinds`), so it
///     costs one page of the budget (`palloc_kinds`); the sweep's start and
///     steps cost nothing (`start_kinds`, `pstep_kinds`); a minor collection
///     costs one page per promotion (`replay_kinds`).
///   - **the sweep's length**: `nsw` counts the sweep steps left, one per
///     unit (pool page or run) from the cursor; while it is positive the
///     sweep is not done (`nsw_succ`), and at 0 it is (`nsw_done`).

module GC.Spec.Top.PWPages

open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.MinorHeap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Top.Word
open GC.Spec.Top.Low
open GC.Spec.Top.PagesAlloc
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module I = GC.Spec.AllocIface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module W = GC.Spec.Pages.Witness
module Pool = GC.Spec.Pages.Pool
module AT = GC.Spec.Pages.AllocTag
module Th = GC.Spec.Pages.Theorems
module SS = GC.Spec.Pages.StartSweep
module SA = GC.Spec.Pages.SweepAll
module SP = GC.Spec.Pages.SweepPage
module SSt = GC.Spec.Pages.SweepStep
module Incr = GC.Spec.Pages.Incr
module MS = GC.Spec.Pages.MidSweep
module PSw = GC.Spec.Top.PagesSweep
module PFi = GC.Spec.Top.PagesFits
module PR = GC.Spec.Top.PromoteRun
module PRe = GC.Spec.Top.PagesReplay
module Init = GC.Spec.Pages.Init

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The budget
/// ---------------------------------------------------------------------------

/// Pages from `j` on are free; every page is free or a pool page.
let kinds_ok (st: pstate) (j: nat) : prop =
  forall (i: nat{i < n_pages}). (j <= i ==> (entry st.pm i).kind == Free) /\
                                (Free? (entry st.pm i).kind \/ Pool? (entry st.pm i).kind)

let kinds_mono (st: pstate) (j j': nat) : Lemma (requires kinds_ok st j /\ j <= j') (ensures kinds_ok st j') = ()

let kinds_init () : Lemma (kinds_ok Init.init_state 0) = ()

/// The first free page is at most any free page.
#push-options "--fuel 1"
let rec find_free_le (pm: page_map) (i j: nat)
  : Lemma (requires i <= j /\ j < n_pages /\ (entry pm j).kind == Free) (ensures Pool.find_free pm i <= j)
          (decreases (if i < n_pages then n_pages - i else 0))
  = if (entry pm i).kind = Free then () else find_free_le pm (i + 1) j
#pop-options

/// A small allocation costs one page of the budget.
let small_ok (clr: bool) (g: heap) (st: pstate) (wz: nat{wz + 1 <= small_max}) (j: nat)
  : Lemma (requires kinds_ok st j)
          (ensures (let (_, st', _) = Pool.small_alloc_as clr g st wz in kinds_ok st' (j + 1)))
  = W.small_kinds clr g st wz;
    let (_, st', _) = Pool.small_alloc_as clr g st wz in
    if j < n_pages then find_free_le st.pm 0 j;
    let one (i: nat{i < n_pages})
      : Lemma ((j + 1 <= i ==> (entry st'.pm i).kind == Free) /\
               (Free? (entry st'.pm i).kind \/ Pool? (entry st'.pm i).kind))
      = assert (W.kind_of st' i == W.kind_of st i \/
                (i == W.first_free st /\ W.kind_of st i == Free /\ W.kind_of st' i == Pool (class_of (wz + 1)))) in
    FStar.Classical.forall_intro one

/// One allocation of the page allocator component.
let palloc_kinds (ph: T.phase pprog) (h: heap) (s: pst) (sz: M.size_t) (tag: M.tag_t) (j: nat)
  : Lemma (requires kinds_ok s.ps j /\ sz + 1 <= small_max)
          (ensures (let (_, s', _) = palloc ph h s sz tag in kinds_ok s'.ps (j + 1)))
  = params_ok ();
    let g = gl h s in
    AT.alloc_col_tag_eq (I.new_colour (iph ph)) (tg tag) g s.ps sz;
    small_ok false g s.ps sz j

/// **Room**: a free page left in the budget.
let no_fit_free (g: heap) (st: pstate) (w: pos) (j: nat)
  : Lemma (requires kinds_ok st j /\ j < n_pages /\ w <= small_max) (ensures ~(Th.no_fit g st w))
  = assert ((entry st.pm j).kind == Free)

let room_of (ph: T.phase pprog) (h: heap) (s: pst) (sz: M.size_t) (j: nat)
  : Lemma (requires pinv ph h s /\ kinds_ok s.ps j /\ j < n_pages /\ sz + 1 <= small_max)
          (ensures pa.T.room ph s h sz == true)
  = params_ok ();
    FStar.Math.Lemmas.pow2_lt_compat 54 20;
    no_fit_free (gl h s) s.ps (sz + 1) j;
    assert (pinv ph h s /\ sz + 1 < pow2 54 /\ ~(Th.no_fit (gl h s) s.ps (sz + 1)));
    assert_norm (PFi.pfits ph s h sz <==> (pinv ph h s /\ sz + 1 < pow2 54 /\ ~(Th.no_fit (gl h s) s.ps (sz + 1))));
    PFi.pfits_room ph s h sz

/// ---------------------------------------------------------------------------
/// The sweep costs nothing
/// ---------------------------------------------------------------------------

let start_kinds (st: pstate) (j: nat) : Lemma (requires kinds_ok st j) (ensures kinds_ok (SS.start_sweep st) j)
  = FStar.Classical.forall_intro (SS.clear_entry st.pm)

let pstart_kinds (h: heap) (s: pst) (j: nat)
  : Lemma (requires kinds_ok s.ps j) (ensures kinds_ok (snd (PSw.pstart h s)).ps j)
  = start_kinds s.ps j

/// Sweeping a pool page leaves it a pool page or frees it; no other page
/// changes kind.
let step_kinds (g: heap) (st: pstate) (q: nat{q < n_pages}) (j: nat)
  : Lemma (requires kinds_ok st j) (ensures kinds_ok (snd (SA.step g st q)) j)
  = if (entry st.pm q).swept then ()
    else match (entry st.pm q).kind with
    | Pool c ->
      let (g', e) = SP.sweep_page g st.pm q in
      assert (e.kind == Pool c \/ e.kind == Free);
      SSt.push_entry st q e;
      let st1 = SSt.push0 st q e in
      assert (kinds_ok st1 j);
      (match SSt.old_tail st q e with
       | None -> ()
       | Some q' ->
         let pm2 = SSt.set_next st1.pm q' (SSt.page_id q) in
         assert (forall (i: nat{i < n_pages}). (entry pm2 i).kind == (entry st1.pm i).kind))
    | _ -> ()

let pstep_kinds (p: pprog) (h: heap) (s: pst) (j: nat)
  : Lemma (requires kinds_ok s.ps j) (ensures (let (_, _, s', _) = PSw.pstep p h s in kinds_ok s'.ps j))
  = let q = PSw.nextu s.ps.pm p.cur in
    if q >= n_pages then () else step_kinds (gl h s) s.ps q j

/// ---------------------------------------------------------------------------
/// A minor collection costs one page per promotion
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --z3rlimit 40"
let rec replay_kinds (ph: T.phase pprog) (st0: pst) (ms: minor_state) (g0: heap) (q: Seq.seq U64.t) (k: nat) (j: nat)
  : Lemma (requires kinds_ok st0.ps j /\ k <= Seq.length q /\
                    (forall (i: nat). i < k ==> minor_wosize ms (Seq.index q i) + 1 <= small_max))
          (ensures kinds_ok (snd (PR.replay (PRe.ptal ph st0) ms g0 st0.ps q k)) (j + k))
          (decreases k)
  = if k = 0 then ()
    else begin
      replay_kinds ph st0 ms g0 q (k - 1) j;
      let (g, s) = PR.replay (PRe.ptal ph st0) ms g0 st0.ps q (k - 1) in
      let m = Seq.index q (k - 1) in
      if minor_wosize ms m > 0 then begin
        PRe.promote_palloc ph st0 ms g s m;
        palloc_kinds ph g (PRe.tst g s) (minor_wosize ms m) (PRe.mtag ms m) (j + k - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The sweep's length
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec nextu_spec (pm: page_map) (c: nat)
  : Lemma (ensures (let q = PSw.nextu pm c in
                    (q < n_pages ==> c <= q /\ Incr.sweeps pm q) /\
                    (q >= n_pages ==> (forall (j: nat{j < n_pages}). c <= j ==> not (Incr.sweeps pm j)))))
          (decreases (if c < n_pages then n_pages - c else 0))
  = if c >= n_pages then () else if Incr.sweeps pm c then () else nextu_spec pm (c + 1)
#pop-options

/// The sweep steps left: one per unit from the cursor.
let rec nsw (p: pprog) (h: heap) (s: pst) : GTot nat (decreases (if p.cur < n_pages then n_pages - p.cur else 0)) =
  if PSw.pdone p then 0
  else begin
    let q = PSw.nextu s.ps.pm p.cur in
    if q >= n_pages then 0
    else begin
      nextu_spec s.ps.pm p.cur;
      let (p', h', s', _) = PSw.pstep p h s in
      1 + nsw p' h' s'
    end
  end

#push-options "--fuel 1"
let nsw_succ (p: pprog) (h: heap) (s: pst)
  : Lemma (requires nsw p h s > 0)
          (ensures PSw.pdone p == false /\
                   (let (p', h', s', _) = PSw.pstep p h s in nsw p' h' s' == nsw p h s - 1))
  = ()

let nsw_zero (p: pprog) (h: heap) (s: pst)
  : Lemma (requires nsw p h s == 0 /\ PSw.pdone p == false)
          (ensures PSw.nextu s.ps.pm p.cur >= n_pages)
  = ()
#pop-options

/// No unit from the cursor on, and every page below it swept: every page is.
let all_swept_of (pm: page_map) (c: nat)
  : Lemma (requires map_ok pm /\ Incr.swept_below pm c /\
                    (forall (j: nat{j < n_pages}). c <= j ==> not (Incr.sweeps pm j)))
          (ensures forall (j: nat{j < n_pages}). (entry pm j).swept)
  = let one (j: nat{j < n_pages}) : Lemma ((entry pm j).swept)
      = if j < c then ()
        else match (entry pm j).kind with
        | LargeCont ->
          assert (cont_ok pm j);
          eliminate exists (h: nat{h < n_pages}). h < j /\ in_run pm h j
          with assert (run_ok pm h)
        | _ -> assert (free_ok pm j) in
    FStar.Classical.forall_intro one

/// **At 0 steps left, the sweep is done.**
let nsw_done (p: pprog) (h: heap) (s: pst)
  : Lemma (requires nsw p h s == 0 /\ pinv (T.Sweeping p) h s) (ensures PSw.pdone p == true)
  = if PSw.pdone p then ()
    else begin
      nsw_zero p h s;
      nextu_spec s.ps.pm p.cur;
      MS.pages_ok_sw_elim (gl h s) s.ps;
      all_swept_of s.ps.pm p.cur;
      PSw.swept_upto_iff p.ppm n_pages
    end
