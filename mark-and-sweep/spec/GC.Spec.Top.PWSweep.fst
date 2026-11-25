/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWSweep - the sweep in a pages witness run
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  On a described configuration (GC.Spec.Top.PWDesc), from
/// the sweep's contract (`sweep_start_at`, `sweep_step_at`,
/// `sweep_done_at`):
///   - `step_hand`: the hand-over, when nothing is grey and no dark block
///     points to a white one: every block in use is unswept; live blocks are
///     black, garbage white;
///   - `step_sweep`: a step keeps the description: a live block is black
///     where unswept and white where swept; a garbage block in use is white
///     and unswept, and the step that sweeps it frees it;
///   - `sweeps`: the `PWPages.nsw` steps left are each enabled, and after
///     them the sweep is done;
///   - `step_end`: the end: the garbage is free, live blocks white, idle.
/// Which page each step sweeps is never computed.

module GC.Spec.Top.PWSweep

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.Run
open GC.Spec.Top.PWDesc
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module Y = GC.Spec.Top.Young
module RA = GC.Spec.Top.RunApp
module PIn = GC.Spec.Top.PagesInst
module PSw = GC.Spec.Top.PagesSweep
module PWP = GC.Spec.Top.PWPages

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let kph_same (x x': config pc) (k: phk) : Lemma (requires x'.ph == x.ph) (ensures kph x' k <==> kph x k) = ()

/// ---------------------------------------------------------------------------
/// The hand-over
/// ---------------------------------------------------------------------------

let hpre (x: config pc) (d: dsc) : prop =
  cok /\ holds x d /\ d.dk == DM /\ T.no_grey (mx x) /\ T.dark_closed (mx x) /\
  (forall (y: nat). Some? (d.db y) ==>
     ((Some?.v (d.db y)).blv ==> (Some?.v (d.db y)).bc == M.Black) /\
     (not (Some?.v (d.db y)).blv ==> (Some?.v (d.db y)).bc == M.White))

let dhand (d: dsc) : dsc = { d with dk = DS }

let hand_model (x: config pc) (d: dsc)
  : Lemma (requires hpre x d)
          (ensures (let x' = step pc x EHandover in
                    T.Sweeping? x'.ph /\ x'.w == x.w /\ x'.stopped == x.stopped /\
                    pa.T.inv x'.ph x'.w.cmaj (stx x') /\ PWP.kinds_ok (stx x').ps d.dj /\
                    (forall (y: nat). iu x' y == iu x y) /\
                    (forall (y: nat). iu x y ==> unsw x' y == true)))
  = holds_elim x d;
    brepr_cabs x.w.cmaj;
    let x' = step pc x EHandover in
    cok_hyps x EHandover;
    assert (T.sweep_start_at byte_rep PSw.psweep x.w.cmaj (stx x));
    assert (T.sweep_start_m PSw.psweep x.w.cmaj (stx x) (mx x));
    PWP.pstart_kinds x.w.cmaj (stx x) d.dj

let hand_blk (x: config pc) (d: dsc) (y: nat)
  : Lemma (requires hpre x d /\ Some? (d.db y))
          (ensures bk (step pc x EHandover) (dhand d) y (Some?.v (d.db y)))
  = hand_model x d;
    holds_elim x d;
    holds_blk x d y;
    let b = Some?.v (d.db y) in
    let x' = step pc x EHandover in
    assert (mx x' == mx x);
    assert (b.blv ==> b.bc == M.Black);
    assert (not b.blv ==> b.bc == M.White);
    assert (iu x' y == iu x y);
    if iu x y then begin
      assert (unsw x' y == true);
      assert (hcol x' b y == b.bc);
      assert (hcol x b y == b.bc)
    end

let hand_des (x: config pc) (d: dsc) (y: nat)
  : Lemma (requires hpre x d) (ensures iu (step pc x EHandover) y == true ==> Some? (d.db y))
  = hand_model x d;
    if iu x y then holds_iu x d y

let step_hand (x: config pc) (d: dsc)
  : Lemma (requires hpre x d) (ensures holds (step pc x EHandover) (dhand d))
  = hand_model x d;
    holds_elim x d;
    let x' = step pc x EHandover in
    let bl (y: nat) : Lemma (Some? ((dhand d).db y) ==> bk x' (dhand d) y (Some?.v ((dhand d).db y)))
      = if Some? (d.db y) then hand_blk x d y in
    FStar.Classical.forall_intro bl;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (hand_des x d));
    holds_intro x' (dhand d)

/// ---------------------------------------------------------------------------
/// A sweep step
/// ---------------------------------------------------------------------------

/// The steps left.
let nsx (x: config pc) : GTot nat =
  match x.ph with
  | T.Sweeping p -> PWP.nsw p x.w.cmaj (stx x)
  | _ -> 0

/// Nothing is grey while sweeping.
let no_grey_s (x: config pc) (d: dsc)
  : Lemma (requires holds x d /\ d.dk == DS) (ensures T.no_grey (mx x))
  = holds_elim x d;
    let one (y: nat) : Lemma (M.is_block (mx x) y ==> M.col_of (mx x) y <> M.Grey)
      = iu_def x y;
        if iu x y then (holds_iu x d y; holds_blk x d y) in
    FStar.Classical.forall_intro one

let sw_post (x: config pc) (m': M.mheap) : prop =
  match x.ph with
  | T.Sweeping p ->
    let (p', h', st', res) = PSw.pstep p x.w.cmaj (stx x) in
    brepr m' h' /\ T.sweep_step_post pa p x.w.cmaj (stx x) p' h' st' res (mx x) m'
  | _ -> False

let sw_model (x: config pc) (d: dsc)
  : Lemma (requires cok /\ holds x d /\ d.dk == DS /\ nsx x > 0)
          (ensures exists (m': M.mheap). sw_post x m')
  = holds_elim x d;
    no_grey_s x d;
    brepr_cabs x.w.cmaj;
    let T.Sweeping p = x.ph in
    PWP.nsw_succ p x.w.cmaj (stx x);
    cok_hyps x ESweep;
    assert (T.sweep_step_at byte_rep PSw.psweep p x.w.cmaj (stx x))

/// The next configuration, on the models.
let sw_after (x: config pc) (d: dsc) (m': M.mheap) : prop =
  let x' = step pc x ESweep in
  R.heq (mx x') m' /\ T.Sweeping? x'.ph /\ x'.stopped == x.stopped /\ x'.w.cyng == x.w.cyng /\
  x'.w.croots == x.w.croots /\ x'.w.crem == x.w.crem /\
  pa.T.inv x'.ph x'.w.cmaj (stx x') /\ PWP.kinds_ok (stx x').ps d.dj /\ M.well_formed (mx x') /\
  nsx x' == nsx x - 1

#push-options "--z3rlimit 40"
let sw_next (x: config pc) (d: dsc) (m': M.mheap)
  : Lemma (requires cok /\ holds x d /\ d.dk == DS /\ nsx x > 0 /\ sw_post x m')
          (ensures sw_after x d m')
  = holds_elim x d;
    let T.Sweeping p = x.ph in
    let (p', h', st', res) = PSw.pstep p x.w.cmaj (stx x) in
    let x' = step pc x ESweep in
    assert (x'.w.cmaj == h' /\ stx x' == st' /\ x'.ph == T.Sweeping p');
    R.heq_sym m' (mx x');
    PIn.wf_heq m' (mx x');
    PWP.pstep_kinds p x.w.cmaj (stx x) d.dj;
    PWP.nsw_succ p x.w.cmaj (stx x)
#pop-options

/// In use after a step, read on the contract's model.
let sw_iu (x: config pc) (m': M.mheap) (y: nat)
  : Lemma (requires (match x.ph with
                     | T.Sweeping p ->
                       let (p', h', st', res) = PSw.pstep p x.w.cmaj (stx x) in
                       brepr m' h' /\ (step pc x ESweep).w.cmaj == h' /\ stx (step pc x ESweep) == st'
                     | _ -> False))
          (ensures (match x.ph with
                    | T.Sweeping p ->
                      let (p', h', st', res) = PSw.pstep p x.w.cmaj (stx x) in
                      iu (step pc x ESweep) y == T.in_use pa st' h' m' y
                    | _ -> True))
  = ()

/// The contract's step, at one block.
let sw_y (p p': pprog) (h h': heap) (st st': pst) (res: T.step_result) (m m': M.mheap) (y: nat)
  : Lemma (requires T.sweep_step_post pa p h st p' h' st' res m m')
          (ensures (T.in_use pa st h m y /\ T.region pk p p' y /\ M.col_of m y == M.Black ==>
                      T.in_use pa st' h' m' y /\ M.col_of m' y == M.White /\ M.same_contents m m' y) /\
                   (T.in_use pa st h m y /\ not (T.region pk p p' y) ==> T.in_use pa st' h' m' y /\ M.same_block m m' y) /\
                   (T.swept_white pa st h m p p' y ==> T.in_use pa st' h' m' y == false) /\
                   (T.in_use pa st' h' m' y ==> T.in_use pa st h m y) /\
                   (punswept p' y ==> punswept p y))
  = ()

#push-options "--z3rlimit 40"
let sw_blk (x: config pc) (d: dsc) (m': M.mheap) (y: nat)
  : Lemma (requires cok /\ holds x d /\ d.dk == DS /\ nsx x > 0 /\ sw_post x m' /\
                    sw_after x d m' /\ Some? (d.db y))
          (ensures bk (step pc x ESweep) d y (Some?.v (d.db y)) /\
                   (iu (step pc x ESweep) y == true ==> iu x y == true))
  = holds_elim x d;
    holds_blk x d y;
    let b = Some?.v (d.db y) in
    let T.Sweeping p = x.ph in
    let (p', h', st', res) = PSw.pstep p x.w.cmaj (stx x) in
    let x' = step pc x ESweep in
    assert (x'.w.cmaj == h' /\ stx x' == st' /\ x'.ph == T.Sweeping p');
    sw_iu x m' y;
    sw_y p p' x.w.cmaj h' (stx x) st' res (mx x) m' y;
    iu_def x y;
    assert (iu x' y == T.in_use pa st' h' m' y);
    if iu x y then begin
      if punswept p y && not (punswept p' y) then begin
        if b.blv then begin
          assert (M.col_of (mx x) y == M.Black);
          assert (hcol x' b y == M.White)
        end else
          assert (T.swept_white pa (stx x) x.w.cmaj (mx x) p p' y)
      end else begin
        assert (punswept p' y == punswept p y);
        assert (hcol x' b y == hcol x b y)
      end
    end
#pop-options

let sw_des (x: config pc) (d: dsc) (m': M.mheap) (y: nat)
  : Lemma (requires cok /\ holds x d /\ d.dk == DS /\ nsx x > 0 /\ sw_post x m' /\
                    sw_after x d m')
          (ensures iu (step pc x ESweep) y == true ==> Some? (d.db y))
  = let T.Sweeping p = x.ph in
    let (p', h', st', res) = PSw.pstep p x.w.cmaj (stx x) in
    let x' = step pc x ESweep in
    assert (x'.w.cmaj == h' /\ stx x' == st');
    sw_iu x m' y;
    if iu x y then holds_iu x d y

let sw_intro (x: config pc) (d: dsc) (m': M.mheap)
  : Lemma (requires holds x d /\ sw_after x d m' /\
                    (forall (y: nat). Some? (d.db y) ==> bk (step pc x ESweep) d y (Some?.v (d.db y))) /\
                    (forall (y: nat). iu (step pc x ESweep) y == true ==> Some? (d.db y)))
          (ensures holds (step pc x ESweep) d)
  = holds_elim x d;
    holds_intro (step pc x ESweep) d

/// **ESweep**: the description is kept, one step fewer is left.
let step_sweep (x: config pc) (d: dsc)
  : Lemma (requires cok /\ holds x d /\ d.dk == DS /\ nsx x > 0)
          (ensures holds (step pc x ESweep) d /\ nsx (step pc x ESweep) == nsx x - 1 /\
                   (forall (y: nat). iu (step pc x ESweep) y == true ==> iu x y == true))
  = sw_model x d;
    eliminate exists (m': M.mheap). sw_post x m'
    with begin
      sw_next x d m';
      let bl (y: nat) : Lemma (Some? (d.db y) ==> bk (step pc x ESweep) d y (Some?.v (d.db y)))
        = if Some? (d.db y) then sw_blk x d m' y in
      FStar.Classical.forall_intro bl;
      FStar.Classical.forall_intro (sw_des x d m');
      let iu1 (y: nat) : Lemma (iu (step pc x ESweep) y == true ==> iu x y == true)
        = if iu (step pc x ESweep) y then (sw_des x d m' y; sw_blk x d m' y) in
      FStar.Classical.forall_intro iu1;
      sw_intro x d m'
    end

/// Enabled: sweeping, with steps left.
let sweep_conds (sty: style) (x: config pc) (d: dsc)
  : Lemma (requires cok /\ holds x d /\ d.dk == DS /\ nsx x > 0)
          (ensures RA.conds pc sty x ESweep)
  = holds_elim x d;
    views_wd x d;
    let T.Sweeping p = x.ph in
    PWP.nsw_succ p x.w.cmaj (stx x);
    cok_hyps x ESweep;
    assert (pc.s.T.done p == false);
    assert (enabled pc x ESweep);
    assert (style_ok sty x ESweep);
    assert (mutator_ok x ESweep)

/// ---------------------------------------------------------------------------
/// The steps left
/// ---------------------------------------------------------------------------

let rec repl (k: nat) : list event = if k = 0 then [] else ESweep :: repl (k - 1)

#push-options "--fuel 1"
let rec sweeps (sty: style) (x: config pc) (d: dsc)
  : Lemma (requires cok /\ holds x d /\ d.dk == DS)
          (ensures (let x' = exec pc x (repl (nsx x)) in
                    RA.tail_ok pc sty x (repl (nsx x)) /\ holds x' d /\ nsx x' == 0 /\
                    (forall (y: nat). iu x' y == true ==> iu x y == true)))
          (decreases (nsx x))
  = if nsx x = 0 then ()
    else begin
      sweep_conds sty x d;
      step_sweep x d;
      let x1 = step pc x ESweep in
      sweeps sty x1 d;
      assert (repl (nsx x) == ESweep :: repl (nsx x1))
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The end
/// ---------------------------------------------------------------------------

let gend (b: bd) : bd = { b with bc = M.White }

let dend (d: dsc) : dsc =
  { d with dk = DI;
           db = (fun (y: nat) -> match d.db y with Some b -> if b.blv then Some (gend b) else None | None -> None) }

let end_model (x: config pc) (d: dsc)
  : Lemma (requires cok /\ holds x d /\ d.dk == DS /\ nsx x == 0)
          (ensures (let x' = step pc x EEnd in
                    x'.ph == T.Idle /\ x'.w == x.w /\ x'.ast == x.ast /\ x'.stopped == x.stopped /\
                    pa.T.inv T.Idle x.w.cmaj (stx x) /\
                    (forall (y: nat). iu x y == true ==> unsw x y == false) /\
                    (match x.ph with T.Sweeping p -> PSw.pdone p == true | _ -> False)))
  = holds_elim x d;
    brepr_cabs x.w.cmaj;
    let T.Sweeping p = x.ph in
    PWP.nsw_done p x.w.cmaj (stx x);
    cok_hyps x EEnd;
    assert (T.sweep_done_at byte_rep PSw.psweep p x.w.cmaj (stx x));
    assert (T.sweep_done_m PSw.psweep p x.w.cmaj (stx x) (mx x))

let end_blk (x: config pc) (d: dsc) (y: nat)
  : Lemma (requires cok /\ holds x d /\ d.dk == DS /\ nsx x == 0 /\ Some? ((dend d).db y))
          (ensures bk (step pc x EEnd) (dend d) y (Some?.v ((dend d).db y)))
  = end_model x d;
    holds_blk x d y

let end_des (x: config pc) (d: dsc) (y: nat)
  : Lemma (requires cok /\ holds x d /\ d.dk == DS /\ nsx x == 0)
          (ensures iu (step pc x EEnd) y == true ==> Some? ((dend d).db y))
  = end_model x d;
    if iu x y then (holds_iu x d y; holds_blk x d y)

let step_end (x: config pc) (d: dsc)
  : Lemma (requires cok /\ holds x d /\ d.dk == DS /\ nsx x == 0)
          (ensures holds (step pc x EEnd) (dend d) /\ RA.conds pc Sequential x EEnd /\ RA.conds pc Incremental x EEnd)
  = end_model x d;
    holds_elim x d;
    let x' = step pc x EEnd in
    let bl (y: nat) : Lemma (Some? ((dend d).db y) ==> bk x' (dend d) y (Some?.v ((dend d).db y)))
      = if Some? ((dend d).db y) then end_blk x d y in
    FStar.Classical.forall_intro bl;
    FStar.Classical.forall_intro (end_des x d);
    holds_intro x' (dend d);
    views_wd x d;
    cok_hyps x EEnd
