/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesQueue - the replay invariant along the promotion's queue
/// ---------------------------------------------------------------------------
///
/// `ri_queue`: after the first `j` promotions of the queue (each of which
/// succeeded, `PromoteRun.qok`), the replay invariant `PagesReplay.ri`
/// holds, with the copies `copies q fwd j` (young block, copy) recorded.

module GC.Spec.Top.PagesQueue

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Spec.Pages.Inv
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.PagesReplay
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module P = GC.Spec.Pages.Promote
module PR = GC.Spec.Top.PromoteRun
module PC = GC.Spec.Top.PromoteCopy
module Y = GC.Spec.Top.Young

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The young block of a nursery object.
let yof (x: U64.t) : nat = if U64.v x >= 8 then (U64.v x - 8) / 8 else 0

let div8 (x: nat) : Lemma (requires x % 8 == 0) (ensures 8 * (x / 8) == x) = FStar.Math.Lemmas.lemma_div_exact x 8

let ywords_bound (o: nat) (b: nat)
  : Lemma (requires 8 * o < b /\ b <= minor_heap_size) (ensures o < ywords /\ 8 * o + 8 < pow2 64)
  = Y.msz ()

#push-options "--z3rlimit 40"
let obj_young (y: M.mheap) (ms: minor_state) (x: U64.t)
  : Lemma (requires Y.yrepr y ms /\ Seq.mem x (minor_objects ms))
          (ensures (let o = yof x in M.is_block y o /\ 8 * o + 8 < pow2 64 /\ PC.yobj o == x))
  = let b : nat = U64.v ms.bump in
    Y.yrepr_elim y ms;
    Y.young_objects ms x;
    Y.yok_elim ms;
    let q : nat = U64.v x - 8 in
    Y.yat_facts ms.data 0 b q;
    div8 q;
    let o = yof x in
    assert (8 * o == q);
    ywords_bound o b;
    assert (Some? (Y.yhd_of ms o));
    assert (M.is_block (Y.yabs ms) o);
    R.agree_blocks y (Y.yabs ms) o;
    U64.v_inj (PC.yobj o) x
#pop-options

/// The copies of the first `j` objects of the queue.
let rec copies (q: seq U64.t) (fwd: forwarding_map) (j: nat) : GTot (list (nat & nat)) (decreases j) =
  if j = 0 || j > Seq.length q then []
  else (yof (Seq.index q (j - 1)), maddr (fwd (Seq.index q (j - 1)))) :: copies q fwd (j - 1)

/// The page state of a replay state.
let rstate (ph: T.phase pprog) (st0: pst) (h0: heap) (ms: minor_state) (q: seq U64.t) (j: nat) : GTot (heap & pst) =
  let (g, s) = PR.replay (ptal ph st0) ms (gl h0 st0) st0.ps q j in (g, tst g s)

/// The start, in the replay's form.
#push-options "--fuel 1"
let ri_zero (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state) (q: seq U64.t)
            (fwd: forwarding_map)
  : Lemma (requires pa.T.inv ph h0 st0 /\ M.well_formed w.M.maj /\ R.heq w.M.maj (cabs h0) /\
                    T.young_sound pa ph st0 h0 w /\ w.M.yng == y)
          (ensures (let (g, st) = rstate ph st0 h0 ms q 0 in ri ph st0 h0 y g st (cabs g) (copies q fwd 0)))
  = ri_start ph st0 h0 y w;
    let g0 = gl h0 st0 in
    low_set_low h0 st0.lo;
    assert (tst g0 st0.ps == st0);
    cabs_set_low h0 st0.lo;
    ri_heq ph st0 h0 y g0 st0 (cabs h0) (cabs g0) [];
    assert (PR.replay (ptal ph st0) ms g0 st0.ps q 0 == (g0, st0.ps));
    assert (copies q fwd 0 == [])
#pop-options

#push-options "--fuel 1"
let replay_unfold (#s: Type0) (a: P.tal s) (ms: minor_state) (g0: heap) (st0: s) (q: seq U64.t) (j: nat)
  : Lemma (requires 0 < j /\ j <= Seq.length q)
          (ensures (let (g, st) = PR.replay a ms g0 st0 q (j - 1) in
                    let (g2, s2, _) = PR.promote_at a ms g st (Seq.index q (j - 1)) in
                    PR.replay a ms g0 st0 q j == (g2, s2)))
  = ()

let copies_unfold (q: seq U64.t) (fwd: forwarding_map) (j: nat)
  : Lemma (requires 0 < j /\ j <= Seq.length q)
          (ensures copies q fwd j == (yof (Seq.index q (j - 1)), maddr (fwd (Seq.index q (j - 1)))) :: copies q fwd (j - 1))
  = ()
#pop-options

/// The conditions of the whole replay.
[@@"opaque_to_smt"]
let qpre (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state) (cs: P.gstate pstate)
  : prop =
  pa.T.inv ph h0 st0 /\ M.well_formed w.M.maj /\ R.heq w.M.maj (cabs h0) /\
  T.young_sound pa ph st0 h0 w /\ w.M.yng == y /\ Y.yrepr y ms /\
  PR.qok (ptal ph st0) ms (gl h0 st0) st0.ps cs

let qpre_elim (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state) (cs: P.gstate pstate)
  : Lemma (requires qpre ph st0 h0 y w ms cs)
          (ensures pa.T.inv ph h0 st0 /\ M.well_formed w.M.maj /\ R.heq w.M.maj (cabs h0) /\
                   T.young_sound pa ph st0 h0 w /\ w.M.yng == y /\ Y.yrepr y ms /\
                   PR.qok (ptal ph st0) ms (gl h0 st0) st0.ps cs)
  = reveal_opaque (`%qpre) (qpre ph st0 h0 y w ms cs)

/// **The replay invariant after the first `j` promotions of the queue.**
#push-options "--z3rlimit 40"
let rec ri_queue (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state)
                 (cs: P.gstate pstate) (j: nat)
  : Lemma (requires qpre ph st0 h0 y w ms cs /\ j <= Seq.length cs.P.queue)
          (ensures (let (g, st) = rstate ph st0 h0 ms cs.P.queue j in
                    ri ph st0 h0 y g st (cabs g) (copies cs.P.queue cs.P.fwd j)))
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
      assert (PR.qentry (ptal ph st0) ms (gl h0 st0) st0.ps cs (j - 1));
      obj_young y ms x;
      let o = yof x in
      PC.young_obj y ms o;
      let (g, s) = PR.replay (ptal ph st0) ms (gl h0 st0) st0.ps q (j - 1) in
      GC.Spec.Top.PagesInst.wf_heq w.M.maj (cabs h0);
      ri_step ph st0 h0 y ms g (tst g s) (cabs g) (copies q cs.P.fwd (j - 1)) o;
      replay_unfold (ptal ph st0) ms (gl h0 st0) st0.ps q j;
      copies_unfold q cs.P.fwd j
    end
#pop-options
