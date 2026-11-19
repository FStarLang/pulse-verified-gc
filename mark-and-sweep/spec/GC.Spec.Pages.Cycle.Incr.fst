/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cycle.Incr - the Pulse operations of incremental mode as
/// events of the page cycle
/// ---------------------------------------------------------------------------
///
/// Plan §28.  The Pulse code of incremental mode (`GC.Impl.Pages.AllocInc`,
/// `SweepInc`, `Sweep.start_sweep`) computes the specification functions of
/// `GC.Spec.Pages.Incr`.  Here those are the events of the page cycle with
/// the page invariant carried (`GC.Spec.Pages.Cycle.Carried`):
///
///   * **every state of a run meets the Pulse code's preconditions**
///     (`run_pre`): the page invariant of its phase (`Incr.phase_inv`, what
///     `alloc_ph` asks) and, mid-sweep, `map_ok` (what `sweep_unit` and
///     `sweep_slice` ask);
///   * a unit swept (`sweep_unit`, `SweepAll.step`) is the event `CSStep`;
///     a slice (`sweep_slice`, `Incr.slice_from`) is a sequence of them
///     (`slice_events`); an allocation (`alloc_ph` with tag 0, `PA.alloc
///     I.Sweeping`) and the caller's writes are `CSAlloc`, and with any tag
///     but 249 (`AT.alloc_tag I.Sweeping`) `CSAllocT`; the end, once the
///     cursor has passed every page (`Incr.cursor_end`), is `CSEnd`; the
///     start is `CSStart` at `StartSweep.start_sweep`, which the Pulse
///     `start_sweep` computes;
///   * so a run extended by any of them, in any order, is a run
///     (`cyc_unit`, `cyc_slice`, `cyc_alloc`, `cyc_alloc_t`, `cyc_end`), and
///     the theorems of the cycle (`Carried.ccycle_inv`, `ccycle_correct`)
///     hold of it.

module GC.Spec.Pages.Cycle.Incr

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module PMP = GC.Spec.Pages.MarkPhase
module SA = GC.Spec.Pages.SweepAll
module MS = GC.Spec.Pages.MidSweep
module MSA = GC.Spec.Pages.MidSweepAlloc
module SPC = GC.Spec.SweepPhase.Completeness
module GC_ = GC.Gen.Cycle
module Inc = GC.Spec.Pages.Incr
module CC = GC.Spec.Pages.Cycle.Carried
module AT = GC.Spec.Pages.AllocTag

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The Pulse code's preconditions hold at every state of a run
/// ---------------------------------------------------------------------------

/// The carried invariant is the phase's invariant the Pulse allocator asks.
let cinv_phase (g: heap) (st: pstate) (ph: I.phase)
  : Lemma (requires CC.cinv g st ph) (ensures Inc.phase_inv ph g st)
  = match ph with
    | I.Idle -> ()
    | I.Marking -> ()
    | I.Sweeping -> ()

/// **Every state of a run** meets the preconditions of the Pulse
/// allocator, and, mid-sweep, of the Pulse sweep.
let run_pre (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#ph: I.phase)
            (#since: obj_addr -> prop) (r: CC.ccycle g0 rs g st ph since)
  : Lemma (ensures Inc.phase_inv ph g st /\ (ph == I.Sweeping ==> map_ok st.pm))
  = CC.ccycle_inv r;
    cinv_phase g st ph;
    if I.Sweeping? ph then MS.pages_ok_sw_elim g st

/// ---------------------------------------------------------------------------
/// A slice is a sequence of sweep events
/// ---------------------------------------------------------------------------

let same_run (#g0 #g #g': heap) (#st #st': pstate) (#ph: I.phase) (#since: obj_addr -> prop)
             (r: CC.csweep g0 g st ph since)
  : Pure (CC.csweep g0 g' st' ph since) (requires g == g' /\ st == st') (ensures fun r' -> r' == r)
  = r

/// **A slice** (`Incr.slice_from`) extends a sweep run by one `CSStep` per
/// page it visits.
#push-options "--fuel 1 --ifuel 1"
let rec slice_events (#g0 #g: heap) (#st: pstate) (#since: obj_addr -> prop)
                     (r: CC.csweep g0 g st I.Sweeping since) (p n: nat) (g': heap) (st': pstate)
  : Ghost (CC.csweep g0 g' st' I.Sweeping since)
          (requires (let (a, b, _) = Inc.slice_from g st p n in a == g' /\ b == st'))
          (ensures fun r' -> CC.cstart_st r' == CC.cstart_st r)
          (decreases (if p < n_pages then n_pages - p else 0))
  = Inc.slice_unfold g st p n;
    if p >= n_pages || n = 0 then same_run r
    else begin
      let k = span st.pm p in
      let n' = if Inc.sweeps st.pm p then n - 1 else n in
      slice_events (CC.CSStep r p) (p + k) n' g' st'
    end
#pop-options

/// ---------------------------------------------------------------------------
/// A cycle run, extended
/// ---------------------------------------------------------------------------

/// A run of the cycle mid-sweep is a marking run, its hand-over, and a
/// sweep run.  Each Pulse operation extends the sweep run, so the cycle run.

/// An event keeps the state the sweep run started from.
#push-options "--fuel 1 --ifuel 1"
let cstart_step (#gh #g: heap) (#st: pstate) (#since: obj_addr -> prop)
                (r: CC.csweep gh g st I.Sweeping since) (p: nat{p < n_pages})
  : Lemma (CC.cstart_st (CC.CSStep r p) == CC.cstart_st r) = ()

let cstart_alloc (#gh #g: heap) (#st: pstate) (#since: obj_addr -> prop)
                 (r: CC.csweep gh g st I.Sweeping since)
                 (wz: nat) (g1: heap) (st1: pstate) (obj: obj_addr)
                 (h1: squash (PA.alloc I.Sweeping g st wz == (g1, st1, (obj <: U64.t))))
                 (g': heap) (h2: squash (I.fields_written_with (MS.free_sw st.pm) g1 g' obj))
  : Lemma (CC.cstart_st (CC.CSAlloc r wz g1 st1 obj h1 g' h2) == CC.cstart_st r) = ()

let cstart_alloc_t (#gh #g: heap) (#st: pstate) (#since: obj_addr -> prop)
                   (r: CC.csweep gh g st I.Sweeping since)
                   (wz: nat) (tag: AT.tag_t) (g1: heap) (st1: pstate) (obj: obj_addr)
                   (h1: squash (U64.v tag <> 249 /\ AT.alloc_tag I.Sweeping g st wz tag == (g1, st1, (obj <: U64.t))))
                   (g': heap) (h2: squash (AT.fields_written_away (MS.free_sw st.pm) g1 g' obj))
  : Lemma (CC.cstart_st (CC.CSAllocT r wz tag g1 st1 obj h1 g' h2) == CC.cstart_st r) = ()

let cstart_end (#gh #g: heap) (#st: pstate) (#since: obj_addr -> prop)
               (r: CC.csweep gh g st I.Sweeping since) (h: squash (PMP.all_swept st))
  : Lemma (CC.cstart_st (CC.CSEnd r h) == CC.cstart_st r) = ()
#pop-options

/// **A unit swept** (`sweep_unit`).
let cyc_unit (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#since: obj_addr -> prop)
             (r: CC.ccycle g0 rs g st I.Sweeping since) (p: nat{p < n_pages})
  : GTot (CC.ccycle g0 rs (fst (SA.step g st p)) (snd (SA.step g st p)) I.Sweeping since)
  = match r with
    | CC.CSweep rm minor gh sp' h1 sr h2 -> cstart_step sr p; CC.CSweep rm minor gh sp' h1 (CC.CSStep sr p) ()

/// **A slice** (`sweep_slice`).
let cyc_slice (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#since: obj_addr -> prop)
              (r: CC.ccycle g0 rs g st I.Sweeping since) (p n: nat) (g': heap) (st': pstate)
  : Ghost (CC.ccycle g0 rs g' st' I.Sweeping since)
          (requires (let (a, b, _) = Inc.slice_from g st p n in a == g' /\ b == st'))
          (ensures fun _ -> True)
  = match r with
    | CC.CSweep rm minor gh sp' h1 sr h2 -> CC.CSweep rm minor gh sp' h1 (slice_events sr p n g' st') ()

/// **An allocation** (`alloc_ph`, tag 0, mid-sweep) and the caller's
/// writes to the new object's fields.
let cyc_alloc (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#since: obj_addr -> prop)
              (r: CC.ccycle g0 rs g st I.Sweeping since)
              (wz: nat) (g1: heap) (st1: pstate) (obj: obj_addr) (g': heap)
  : Ghost (s: (obj_addr -> prop) & CC.ccycle g0 rs g' st1 I.Sweeping s)
          (requires PA.alloc I.Sweeping g st wz == (g1, st1, (obj <: U64.t)) /\
                    I.fields_written_with (MS.free_sw st.pm) g1 g' obj)
          (ensures fun _ -> True)
  = match r with
    | CC.CSweep #_ #_ #_ #_ #_ #sm rm minor gh sp' h1 #_ #_ #_ #ss sr h2 ->
      cstart_alloc sr wz g1 st1 obj () g' ();
      (| GC_.union sm (SPC.with_new ss obj), CC.CSweep rm minor gh sp' h1 (CC.CSAlloc sr wz g1 st1 obj () g' ()) () |)

/// **An allocation with a tag** (`alloc_ph`, any tag but 249, mid-sweep)
/// and the caller's writes to the new object's fields (plan §29.2).
let cyc_alloc_t (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#since: obj_addr -> prop)
                (r: CC.ccycle g0 rs g st I.Sweeping since)
                (wz: nat) (tag: AT.tag_t) (g1: heap) (st1: pstate) (obj: obj_addr) (g': heap)
  : Ghost (s: (obj_addr -> prop) & CC.ccycle g0 rs g' st1 I.Sweeping s)
          (requires U64.v tag <> 249 /\ AT.alloc_tag I.Sweeping g st wz tag == (g1, st1, (obj <: U64.t)) /\
                    AT.fields_written_away (MS.free_sw st.pm) g1 g' obj)
          (ensures fun _ -> True)
  = match r with
    | CC.CSweep #_ #_ #_ #_ #_ #sm rm minor gh sp' h1 #_ #_ #_ #ss sr h2 ->
      cstart_alloc_t sr wz tag g1 st1 obj () g' ();
      (| GC_.union sm (SPC.with_new ss obj), CC.CSweep rm minor gh sp' h1 (CC.CSAllocT sr wz tag g1 st1 obj () g' ()) () |)

/// **The end**, once the cursor has passed every page.
let cyc_end (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#since: obj_addr -> prop)
            (r: CC.ccycle g0 rs g st I.Sweeping since) (c: nat)
  : Ghost (CC.ccycle g0 rs g st I.Idle since)
          (requires Inc.swept_below st.pm c /\ c >= n_pages) (ensures fun _ -> True)
  = Inc.cursor_end st c;
    match r with
    | CC.CSweep rm minor gh sp' h1 sr h2 -> cstart_end sr (); CC.CSweep rm minor gh sp' h1 (CC.CSEnd sr ()) ()
