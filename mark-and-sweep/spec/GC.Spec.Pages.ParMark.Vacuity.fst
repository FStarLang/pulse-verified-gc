/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.ParMark.Vacuity - the model's hypotheses can hold
/// ---------------------------------------------------------------------------
///
/// Real witnesses, not only `expect_failure` tests:
///   - an all-zero bitmap has no mark (`zero_no_marks`);
///   - the round-robin schedule is fair (`round_robin_fair`);
///   - a toy view with one object and one root (`toy`), when the heap has a
///     page, satisfies `view_ok` (`toy_ok`); then `mark_correct` and
///     `terminates` apply with two workers, the start is not finished, so
///     `progress` applies too, and at the end the root's bit is set
///     (`toy_marks`).

module GC.Spec.Pages.ParMark.Vacuity

open GC.Spec.Base
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Bitmap
open GC.Spec.Pages.ParMark.Bits
open GC.Spec.Pages.ParMark.Model
open GC.Spec.Pages.ParMark.Reach
open GC.Spec.Pages.ParMark.Inv

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module PI = GC.Spec.Pages.ParMark.Init
module T = GC.Spec.Pages.ParMark.Term
module Sf = GC.Spec.Pages.ParMark.Safety
module D = GC.Spec.Pages.ParMark.Decrease

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let zero_no_marks () : Lemma (PI.no_marks (Seq.create bm_len 0ul))
  = let aux (a: nat) : Lemma (~(marked (Seq.create bm_len 0ul) a))
      = if in_pages a then (widx_bound a; zero_bits (widx a % 32))
    in
    FStar.Classical.forall_intro aux

let round_robin (k: pos) (n: nat) : nat = n % k

let round_robin_fair (k: pos) : Lemma (T.fair k (round_robin k))
  = let aux (w n: nat) : Lemma (w < k ==> (exists (m: nat). m >= n /\ round_robin k m == w))
      = if w < k then begin
          FStar.Math.Lemmas.lemma_mod_plus w n k;
          FStar.Math.Lemmas.small_mod w k;
          FStar.Math.Lemmas.lemma_mult_le_left n 1 k;
          assert (round_robin k (w + n * k) == w)
        end
    in
    introduce forall (w n: nat). w < k ==> (exists (m: nat). m >= n /\ round_robin k m == w)
    with aux w n

/// One object, at the start of the first page, with no field; it is the root.
let y0 : nat = zw + 8

let toy_params : params = {
  k = 2; pkt = 4; chunk = 2; maxlen = 3; smin = 1; tickp = 2;
  nf = (fun _ -> 0); tst = (fun _ -> None); tgt = (fun _ -> None)
}

let toy_view : view = { ok = (fun y -> y == y0); univ = [y0]; maxnf = 0 }

#push-options "--fuel 2"
let toy_ok () : Lemma (requires n_pages > 0) (ensures view_ok toy_params toy_view [y0])
  = pages_end_bound ();
    assert (zw % 8 == 0);
    assert (page_base n_pages >= zw + page_bytes);
    assert (in_pages (y0 - 8));
    let p = toy_params in
    let v = toy_view in
    assert (forall (y: nat). v.ok y <==> y == y0);
    assert (forall (x: nat). p.nf x == 0);
    assert (forall (x a: nat). ~(field_of p x a));
    assert (L.mem y0 [y0]);
    assert (forall (y: nat). L.mem y [y0] <==> y == y0);
    assert (forall (y: nat). v.ok y ==> y >= 8 /\ in_pages (y - 8) /\ p.nf y <= v.maxnf /\ L.mem y v.univ)
#pop-options

let init_not_done (p: params) (bs0: Seq.seq U32.t) (rts: list nat)
  : Lemma (~(all_done (init p bs0 rts)))
  = assert ((Seq.index (init p bs0 rts).ws 0).pc == Id1)

/// **The theorems apply**, with a root: the start satisfies the invariant
/// and is not finished (`progress`, `step_inv`, `step_mu` apply to it); a
/// fair run finishes with the root marked.
let toy_marks () : Lemma (requires n_pages > 0)
  (ensures (let s0 = init toy_params (Seq.create bm_len 0ul) [y0] in
            inv toy_params toy_view [y0] s0 /\ ~(all_done s0) /\
            (exists (n: nat). all_done (T.runf toy_params s0 (round_robin 2) n) /\
                         marked (T.runf toy_params s0 (round_robin 2) n).bs (y0 - 8))))
  = toy_ok ();
    zero_no_marks ();
    round_robin_fair 2;
    let s0 = init toy_params (Seq.create bm_len 0ul) [y0] in
    PI.init_inv toy_params toy_view [y0] (Seq.create bm_len 0ul);
    init_not_done toy_params (Seq.create bm_len 0ul) [y0];
    T.terminates toy_params toy_view [y0] (Seq.create bm_len 0ul) (round_robin 2);
    reach_root toy_params [y0] y0;
    assert (L.mem y0 [y0])

/// ---------------------------------------------------------------------------
/// The hypotheses of the main lemmas are not refutable
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
[@@expect_failure [19]]
let step_inv_hyps_not_false (p: params) (v: view) (rts: list nat) (s: mstate)
  : Lemma (requires view_ok p v rts /\ inv p v rts s) (ensures False) = ()

[@@expect_failure [19]]
let progress_hyps_not_false (p: params) (v: view) (rts: list nat) (s: mstate)
  : Lemma (requires view_ok p v rts /\ inv p v rts s /\ ~(all_done s)) (ensures False) = ()

[@@expect_failure [19]]
let terminates_hyps_not_false (p: params) (v: view) (rts: list nat) (bs0: Seq.seq U32.t) (sched: nat -> nat)
  : Lemma (requires view_ok p v rts /\ PI.no_marks bs0 /\ T.fair p.k sched) (ensures False) = ()

[@@expect_failure [19]]
let complete_hyps_not_false (p: params) (v: view) (rts: list nat) (s: mstate)
  : Lemma (requires view_ok p v rts /\ inv p v rts s /\ s.cnt == 0) (ensures False) = ()

/// Termination does not hold without fairness: a schedule that only runs
/// worker 0 need not finish worker 1.
[@@expect_failure [19]]
let unfair_terminates (p: params) (v: view) (rts: list nat) (bs0: Seq.seq U32.t)
  : Lemma (requires view_ok p v rts /\ PI.no_marks bs0 /\ p.k == 2)
          (ensures exists (n: nat). all_done (T.runf p (init p bs0 rts) (fun _ -> 0) n)) = ()
#pop-options
