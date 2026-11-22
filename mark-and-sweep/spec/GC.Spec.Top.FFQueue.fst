/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFQueue - the replay invariant along the promotion's queue,
/// over first-fit
/// ---------------------------------------------------------------------------
///
/// `ri_queue`: after the first `j` promotions of the queue (each of which
/// succeeded, `PromoteRun.qok`), the replay invariant `FFReplay.ri`
/// holds, with the copies `copies q fwd j` (young block, copy) recorded.
/// GC.Spec.Top.PagesQueue's statements and proofs, over first-fit; the young
/// blocks and the copies of the queue (`yof`, `copies`) are PagesQueue's,
/// which do not depend on the allocator.

module GC.Spec.Top.FFQueue

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.FFReplay
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module P = GC.Spec.Pages.Promote
module PR = GC.Spec.Top.PromoteRun
module PC = GC.Spec.Top.PromoteCopy
module Y = GC.Spec.Top.Young
module Q0 = GC.Spec.Top.PagesQueue

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The first-fit state of a replay state.
let rstate (ph: T.phase U64.t) (st0: ffst) (h0: heap) (ms: minor_state) (q: seq U64.t) (j: nat) : GTot (heap & ffst) =
  let (g, s) = PR.replay (ptal ph st0) ms (gl h0 st0) st0.fp q j in (g, tst g s)

/// The start, in the replay's form.
#push-options "--fuel 1"
let ri_zero (ph: T.phase U64.t) (st0: ffst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state) (q: seq U64.t)
            (fwd: forwarding_map)
  : Lemma (requires ffa.T.inv ph h0 st0 /\ M.well_formed w.M.maj /\ R.heq w.M.maj (cabs h0) /\
                    T.young_sound ffa ph st0 h0 w /\ w.M.yng == y)
          (ensures (let (g, st) = rstate ph st0 h0 ms q 0 in ri ph st0 h0 y g st (cabs g) (Q0.copies q fwd 0)))
  = ri_start ph st0 h0 y w;
    let g0 = gl h0 st0 in
    low_set_low h0 st0.lo;
    assert (tst g0 st0.fp == st0);
    cabs_set_low h0 st0.lo;
    ri_heq ph st0 h0 y g0 st0 (cabs h0) (cabs g0) [];
    assert (PR.replay (ptal ph st0) ms g0 st0.fp q 0 == (g0, st0.fp));
    assert (Q0.copies q fwd 0 == [])
#pop-options

/// The conditions of the whole replay.
[@@"opaque_to_smt"]
let qpre (ph: T.phase U64.t) (st0: ffst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state) (cs: P.gstate U64.t)
  : prop =
  ffa.T.inv ph h0 st0 /\ M.well_formed w.M.maj /\ R.heq w.M.maj (cabs h0) /\
  T.young_sound ffa ph st0 h0 w /\ w.M.yng == y /\ Y.yrepr y ms /\
  PR.qok (ptal ph st0) ms (gl h0 st0) st0.fp cs

let qpre_elim (ph: T.phase U64.t) (st0: ffst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state) (cs: P.gstate U64.t)
  : Lemma (requires qpre ph st0 h0 y w ms cs)
          (ensures ffa.T.inv ph h0 st0 /\ M.well_formed w.M.maj /\ R.heq w.M.maj (cabs h0) /\
                   T.young_sound ffa ph st0 h0 w /\ w.M.yng == y /\ Y.yrepr y ms /\
                   PR.qok (ptal ph st0) ms (gl h0 st0) st0.fp cs)
  = reveal_opaque (`%qpre) (qpre ph st0 h0 y w ms cs)

/// **The replay invariant after the first `j` promotions of the queue.**
#push-options "--z3rlimit 40"
let rec ri_queue (ph: T.phase U64.t) (st0: ffst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state)
                 (cs: P.gstate U64.t) (j: nat)
  : Lemma (requires qpre ph st0 h0 y w ms cs /\ j <= Seq.length cs.P.queue)
          (ensures (let (g, st) = rstate ph st0 h0 ms cs.P.queue j in
                    ri ph st0 h0 y g st (cabs g) (Q0.copies cs.P.queue cs.P.fwd j)))
          (decreases j)
  = let q = cs.P.queue in
    if j = 0 then begin
      qpre_elim ph st0 h0 y w ms cs;
      ri_zero ph st0 h0 y w ms q cs.P.fwd
    end
    else begin
      let j1 : nat = j - 1 in
      ri_queue ph st0 h0 y w ms cs j1;
      qpre_elim ph st0 h0 y w ms cs;
      let x = Seq.index q (j - 1) in
      assert (PR.qentry (ptal ph st0) ms (gl h0 st0) st0.fp cs (j - 1));
      Q0.obj_young y ms x;
      let o = Q0.yof x in
      PC.young_obj y ms o;
      let (g, s) = PR.replay (ptal ph st0) ms (gl h0 st0) st0.fp q (j - 1) in
      GC.Spec.Top.PagesInst.wf_heq w.M.maj (cabs h0);
      ri_step ph st0 h0 y ms g (tst g s) (cabs g) (Q0.copies q cs.P.fwd (j - 1)) o;
      Q0.replay_unfold (ptal ph st0) ms (gl h0 st0) st0.fp q j;
      Q0.copies_unfold q cs.P.fwd j
    end
#pop-options
