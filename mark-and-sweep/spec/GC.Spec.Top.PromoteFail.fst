/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PromoteFail - a failed promotion, and one that did not fail
/// ---------------------------------------------------------------------------
///
/// `PromoteRun.promote_done` ends in a disjunction: a witness of refusal
/// (`wit`), or every root and every field scanned covered.  The witness is
/// a counterfactual (some prefix of the queue after which a live object
/// would not fit), so a promotion can succeed while it holds.  Here the
/// disjunction is split by what happened (`Promote.Fail.failed`, design doc
/// §18, U7):
///
///   * an allocation that failed is a witness (`fn_failure`);
///   * when none failed, every root and every field scanned is covered.
///
/// `promote_failed`: under `promote_done`'s hypotheses, `failed ==> wit`,
/// and `not failed ==>` the closure.  For any allocator.

module GC.Spec.Top.PromoteFail

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Spec.Pages.Promote
open GC.Spec.Pages.Promote.Loop
open GC.Spec.Pages.Promote.Follow
open GC.Spec.Top.PromoteRun
open GC.Spec.Pages.Promote.Fail

module U64 = FStar.UInt64

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// **An object that is not infix**: a failure leaves the state and is a
/// witness; otherwise the object, if it has a body, is forwarded.
#push-options "--z3rlimit 40"
let fn_f (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
         (cs: gstate s) (addr: U64.t)
  : Lemma (requires ctx_w a minor g0 /\ sok a minor live g0 st0 cs /\ ~(is_infix_in_minor minor addr) /\
                    (Seq.mem addr (minor_objects minor) /\ minor_wosize minor addr > 0 ==> live addr))
          (ensures (let cs' = forward_normal a minor cs addr in
                    sok a minor live g0 st0 cs' /\ follows cs cs' /\
                    (fails_normal a minor cs addr ==> cs' == cs /\ wit a minor live g0 st0 cs.queue) /\
                    (~(fails_normal a minor cs addr) /\ Seq.mem addr (minor_objects minor) /\
                     minor_wosize minor addr > 0 ==> cs'.fwd addr <> 0UL)))
  = fn_ok a minor live g0 st0 cs addr;
    if fails_normal a minor cs addr then fn_failure a minor live g0 st0 cs addr
    else if Seq.mem addr (minor_objects minor) && cs.fwd addr = 0UL && minor_wosize minor addr > 0 then begin
      let (_, _, o) = promote_object a minor cs.major addr cs.st (minor_wosize minor addr) in
      assert (o <> 0UL);
      assert (forward_normal a minor cs addr == pushed a minor cs addr)
    end
#pop-options

/// An infix address: through its closure.
#push-options "--z3rlimit 40"
let fo_infix_f (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
               (cs: gstate s) (addr: U64.t)
  : Lemma (requires ctx_w a minor g0 /\ sok a minor live g0 st0 cs /\ justified minor live addr /\
                    follow_ok minor addr /\ cs.fwd addr == 0UL /\ is_infix_in_minor minor addr)
          (ensures (let cs' = forward_one a minor cs addr in
                    (fails_one a minor cs addr ==> wit a minor live g0 st0 cs'.queue) /\
                    (~(fails_one a minor cs addr) ==> covered minor cs' addr)))
  = let p = infix_parent minor addr in
    assert (infix_at minor addr);
    parent_facts_at minor addr;
    assert (resolve_minor minor addr == p);
    fn_f a minor live g0 st0 cs p;
    let cs1 = forward_normal a minor cs p in
    forward_normal_keeps_w a minor g0 cs p;
    assert (cs1.fwd addr == 0UL);
    if cs1.fwd p <> 0UL then begin
      infix_bound a minor g0 cs1 addr;
      fo_hit a minor cs addr;
      let v = U64.uint_to_t (U64.v (cs1.fwd p) + (U64.v addr - U64.v p)) in
      infix_extend a minor live g0 st0 cs1 addr v
    end
    else begin
      fo_miss a minor cs addr;
      parent_wz minor addr
    end
#pop-options

/// **Forwarding an address**: a failure is a witness, and otherwise the
/// address is covered.
#push-options "--z3rlimit 40"
let fo_f (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
         (cs: gstate s) (addr: U64.t)
  : Lemma (requires ctx_w a minor g0 /\ sok a minor live g0 st0 cs /\ justified minor live addr /\
                    follow_ok minor addr)
          (ensures (let cs' = forward_one a minor cs addr in
                    sok a minor live g0 st0 cs' /\ follows cs cs' /\
                    (fails_one a minor cs addr ==> wit a minor live g0 st0 cs'.queue) /\
                    (~(fails_one a minor cs addr) ==> covered minor cs' addr)))
  = fo_ok a minor live g0 st0 cs addr;
    if cs.fwd addr <> 0UL then fwd_covered a minor g0 cs addr
    else if is_infix_in_minor minor addr then fo_infix_f a minor live g0 st0 cs addr
    else begin
      resolve_minor_non_infix minor addr;
      fn_f a minor live g0 st0 cs addr;
      covered_def minor (forward_one a minor cs addr) addr
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The loops
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let rec ff_f (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
             (cs: gstate s) (parent: U64.t) (idx: nat) (wz: nat)
  : Lemma (requires ctx_w a minor g0 /\ sok a minor live g0 st0 cs /\
                    (forall (i: nat). idx <= i /\ i < wz ==> justified minor live (fld minor parent i)) /\
                    (forall (i: nat). idx <= i /\ i < wz ==> follow_ok minor (fld minor parent i)))
          (ensures (let cs' = forward_fields a minor cs parent idx wz in
                    sok a minor live g0 st0 cs' /\ follows cs cs' /\
                    (fails_fields a minor cs parent idx wz ==> wit a minor live g0 st0 cs'.queue) /\
                    (~(fails_fields a minor cs parent idx wz) ==>
                     (forall (i: nat). idx <= i /\ i < wz ==> covered minor cs' (fld minor parent i)))))
          (decreases (if idx >= wz then 0 else wz - idx))
  = if idx < wz then begin
      let fv = fld minor parent idx in
      fld_def minor parent idx;
      fo_f a minor live g0 st0 cs fv;
      let cs1 = forward_one a minor cs fv in
      ff_f a minor live g0 st0 cs1 parent (idx + 1) wz;
      let cs' = forward_fields a minor cs1 parent (idx + 1) wz in
      assert (forward_fields a minor cs parent idx wz == cs');
      fields_step a minor cs parent idx wz;
      follows_trans cs cs1 cs';
      if fails_one a minor cs fv then wit_follows a minor live g0 st0 cs1 cs'
      else if fails_fields a minor cs1 parent (idx + 1) wz then ()
      else begin
        covered_follows minor cs1 cs' fv;
        combine_cov minor cs' parent idx wz
      end
    end

let rec fr_f (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
             (cs: gstate s) (roots: seq U64.t) (idx: nat)
  : Lemma (requires ctx_w a minor g0 /\ sok a minor live g0 st0 cs /\ roots_follow minor roots /\
                    (forall (i: nat). idx <= i /\ i < Seq.length roots ==> justified minor live (Seq.index roots i)))
          (ensures (let cs' = forward_roots a minor cs roots idx in
                    sok a minor live g0 st0 cs' /\ follows cs cs' /\
                    (fails_roots a minor cs roots idx ==> wit a minor live g0 st0 cs'.queue) /\
                    (~(fails_roots a minor cs roots idx) ==>
                     (forall (i: nat). idx <= i /\ i < Seq.length roots ==> covered minor cs' (Seq.index roots i)))))
          (decreases (if idx >= Seq.length roots then 0 else Seq.length roots - idx))
  = if idx < Seq.length roots then begin
      let r = Seq.index roots idx in
      fo_f a minor live g0 st0 cs r;
      let cs1 = forward_one a minor cs r in
      fr_f a minor live g0 st0 cs1 roots (idx + 1);
      let cs' = forward_roots a minor cs1 roots (idx + 1) in
      assert (forward_roots a minor cs roots idx == cs');
      roots_step a minor cs roots idx;
      follows_trans cs cs1 cs';
      if fails_one a minor cs r then wit_follows a minor live g0 st0 cs1 cs'
      else if fails_roots a minor cs1 roots (idx + 1) then ()
      else begin
        covered_follows minor cs1 cs' r;
        combine_roots minor cs' roots idx
      end
    end
#pop-options

/// One object scanned.
#push-options "--z3rlimit 40"
let scan_step_f (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
                (cs: gstate s) (sc: nat) (f: bool)
  : Lemma (requires ctx_w a minor g0 /\ sok a minor live g0 st0 cs /\ live_ok minor live /\ sc < Seq.length cs.queue /\
                    (f ==> wit a minor live g0 st0 cs.queue) /\ (~f ==> scanned minor cs sc))
          (ensures (let x = Seq.index cs.queue sc in
                    let cs1 = forward_fields a minor cs x 0 (minor_scan_wosize minor x) in
                    let f1 = f || fails_fields a minor cs x 0 (minor_scan_wosize minor x) in
                    sok a minor live g0 st0 cs1 /\ follows cs cs1 /\
                    (f1 ==> wit a minor live g0 st0 cs1.queue) /\ (~f1 ==> scanned minor cs1 (sc + 1))))
  = let x = Seq.index cs.queue sc in
    scan_one_just a minor live g0 st0 cs sc;
    scan_one_follow a minor live g0 st0 cs sc;
    ff_f a minor live g0 st0 cs x 0 (minor_scan_wosize minor x);
    let cs1 = forward_fields a minor cs x 0 (minor_scan_wosize minor x) in
    if f then wit_follows a minor live g0 st0 cs cs1
    else if fails_fields a minor cs x 0 (minor_scan_wosize minor x) then ()
    else begin
      nsc_def minor x;
      scanned_step minor cs cs1 sc x
    end
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let rec scan_f (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
               (cs: gstate s) (sc: nat) (fuel: nat) (f: bool)
  : Lemma (requires ctx_w a minor g0 /\ sok a minor live g0 st0 cs /\ live_ok minor live /\
                    sc <= Seq.length cs.queue /\ Seq.length (minor_objects minor) <= sc + fuel /\
                    (f ==> wit a minor live g0 st0 cs.queue) /\ (~f ==> scanned minor cs sc))
          (ensures (let cs' = scan a minor cs sc fuel in
                    let f' = f || fails_scan a minor cs sc fuel in
                    sok a minor live g0 st0 cs' /\ follows cs cs' /\
                    (f' ==> wit a minor live g0 st0 cs'.queue) /\
                    (~f' ==> scanned minor cs' (Seq.length cs'.queue))))
          (decreases fuel)
  = if fuel = 0 || sc >= Seq.length cs.queue then begin
      queue_le a minor g0 st0 cs;
      scan_base a minor cs sc fuel
    end
    else begin
      let x = Seq.index cs.queue sc in
      scan_step_f a minor live g0 st0 cs sc f;
      let cs1 = forward_fields a minor cs x 0 (minor_scan_wosize minor x) in
      let f1 = f || fails_fields a minor cs x 0 (minor_scan_wosize minor x) in
      scan_unfold a minor cs sc fuel;
      GC.Spec.Pages.Promote.Fail.scan_step a minor cs sc fuel;
      let f' : nat = fuel - 1 in
      scan_f a minor live g0 st0 cs1 (sc + 1) f' f1;
      follows_trans cs cs1 (scan a minor cs1 (sc + 1) f')
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The whole promotion
/// ---------------------------------------------------------------------------

/// **What promotion ends in, by what happened**: every queued object live;
/// a failure is a witness; without one, every root and every field of
/// every queued object is covered.
#push-options "--z3rlimit 40"
let promote_failed (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
                   (roots: seq U64.t)
  : Lemma (requires ctx_w a minor g0 /\ a.inv g0 st0 /\ live_ok minor live /\ roots_follow minor roots /\
                    (forall (i: nat). i < Seq.length roots ==> justified minor live (Seq.index roots i)))
          (ensures (let cs = promote a minor g0 st0 roots in
                    sok a minor live g0 st0 cs /\
                    (failed a minor g0 st0 roots ==> wit a minor live g0 st0 cs.queue) /\
                    (~(failed a minor g0 st0 roots) ==>
                     (forall (i: nat). i < Seq.length roots ==> covered minor cs (Seq.index roots i)) /\
                     scanned minor cs (Seq.length cs.queue))))
  = start_ok a minor live g0 st0;
    let c0 = cs0 #s g0 st0 in
    fr_f a minor live g0 st0 c0 roots 0;
    let cs1 = forward_roots a minor c0 roots 0 in
    let f1 = fails_roots a minor c0 roots 0 in
    assert (scanned minor cs1 0);
    scan_f a minor live g0 st0 cs1 0 (Seq.length (minor_objects minor)) f1;
    let cs = scan a minor cs1 0 (Seq.length (minor_objects minor)) in
    assert (promote a minor g0 st0 roots == cs);
    assert (failed a minor g0 st0 roots == (f1 || fails_scan a minor cs1 0 (Seq.length (minor_objects minor))));
    if not f1 then begin
      let r (i: nat) : Lemma (i < Seq.length roots ==> covered minor cs (Seq.index roots i))
        = if i < Seq.length roots then covered_follows minor cs1 cs (Seq.index roots i) in
      FStar.Classical.forall_intro r
    end
#pop-options
