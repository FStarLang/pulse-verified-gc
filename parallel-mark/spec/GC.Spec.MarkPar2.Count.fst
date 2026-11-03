/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Count — work_in_flight
///
///   * In every state a run reaches, the counter equals the counted entries:
///     stack entries, inbox entries, and items held (`count_exact`).
///   * A 0 is final: from such a state with the counter at 0, every worker
///     step leaves it at 0 (`zero_final`).  Only the main thread, between
///     rounds, sets it again.  At 0 nothing is counted, so no stack or inbox
///     holds anything and no worker holds an item: the only thing a worker
///     can still do is stop.
///   * A worker that has stopped saw 0, and while any worker is stopped the
///     counter is 0 (`stopped_zero`); so the main thread, which runs only
///     when every worker has stopped, always finds 0.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Count

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar2.Model
open GC.Spec.MarkPar2.Inv

module M1 = GC.Spec.MarkPar.Model
module Own = GC.Spec.MarkPar.Own
module LS = GC.Spec.MarkPar2.Lists
module U = GC.Spec.MarkPar2.Upd
module E = GC.Spec.MarkPar2.End

let count_exact (k: cfg) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires ctx k g roots)
          (ensures (let s = run k g roots sched in s.count == counted s.wks))
  = E.run_inv k g roots sched;
    reveal_opaque (`%count_ok) (count_ok (run k g roots sched))

let stopped_zero (k: cfg) (g: heap) (roots: list obj_addr) (sched: list event) (i: nat)
  : Lemma (requires ctx k g roots /\ pc_of (run k g roots sched) i == Stopped /\
                    i < L.length (run k g roots sched).wks)
          (ensures (run k g roots sched).count == 0)
  = E.run_inv k g roots sched;
    let s = run k g roots sched in
    reveal_opaque (`%count_ok) (count_ok s);
    Own.nth_lt s.wks i

/// At 0, every record is empty and holds nothing.
let zero_empty (s: state) (i: nat) (w: wk)
  : Lemma (requires count_ok s /\ s.count == 0 /\ wk_of s i == Some w)
          (ensures w.stack == [] /\ w.inbox == [] /\ (w.pc == Loop \/ w.pc == Idle \/ w.pc == Stopped))
  = reveal_opaque (`%count_ok) (count_ok s);
    LS.counted_zero s.wks i w

let zero_step (k: cfg) (s: state) (i: nat)
  : Lemma (requires count_ok s /\ s.count == 0)
          (ensures (wstep k s i).count == 0)
  = match M1.nth s.wks i with
    | Some w -> zero_empty s i w
    | None -> ()

let zero_final (k: cfg) (g: heap) (roots: list obj_addr) (sched: list event) (i: nat)
  : Lemma (requires ctx k g roots /\ (run k g roots sched).count == 0)
          (ensures (step k (run k g roots sched) (W i)).count == 0)
  = E.run_inv k g roots sched;
    let s = run k g roots sched in
    if s.finished then () else zero_step k s i
