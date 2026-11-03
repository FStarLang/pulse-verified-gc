/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2 — the parallel mark of docs/parallel-mark-design.md:
/// statements
///
/// The model is `GC.Spec.MarkPar2.Model` (included here): k workers with
/// bounded stacks and inboxes, overflow flags, the work_in_flight counter,
/// and a main thread that runs setup, the overflow check and the fix-up
/// between rounds.  A run is any list of events; marking is done when the
/// run's `finished` flag is set.  The theorems:
///
///   mark_par_correct     a finished run, over all its rounds and fix-ups,
///                        leaves the heap the sequential mark leaves
///   mark_par_reachable   the same, said with reachability
///   step_writes_own      a worker step writes only headers of objects it
///                        owns
///   step_reads_own       a worker step depends only on the words in its
///                        range and the fields of the object it scans
///   step_race_free       so no word one worker's step writes is one
///                        another's may read
///   main_at_barrier      the main thread changes nothing unless every
///                        worker has stopped
///   count_exact          work_in_flight equals the counted entries
///   zero_final           from 0, every worker step leaves it 0
///   mark_par_terminates  every schedule has at most measure (init ...)
///                        effective steps, the others are no-ops or spin
///                        steps, and a run that has not finished always
///                        has an effective one
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar.Recolour

include GC.Spec.MarkPar2.Model

module M1 = GC.Spec.MarkPar.Model
module R = GC.Spec.MarkPar.Roots
module SM = GC.Spec.MarkPar.Seq
module I = GC.Spec.MarkPar2.Inv
module E = GC.Spec.MarkPar2.End
module Ft = GC.Spec.MarkPar2.Foot
module C = GC.Spec.MarkPar2.Count
module T = GC.Spec.MarkPar2.Term

/// The precondition every statement shares: the sequential mark's (as in
/// Stage 1), and a valid configuration (cuts as in Stage 1, S >= 1).
let pre (k: cfg) (g: heap) (roots: list obj_addr) : prop = M1.mark_pre g roots /\ valid_cfg k

let ctx_of (k: cfg) (g: heap) (roots: list obj_addr)
  : Lemma (requires pre k g roots) (ensures I.ctx k g roots)
  = R.graph_pre_holds g roots;
    reveal_opaque (`%I.ctx) (I.ctx k g roots)

/// ---------------------------------------------------------------------------
/// The result
/// ---------------------------------------------------------------------------

/// For every configuration and every schedule, a run that has finished,
/// after all its rounds and fix-ups, leaves the heap the sequential mark
/// leaves, byte for byte.
val mark_par_correct (k: cfg) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires pre k g roots /\ (run k g roots sched).finished)
          (ensures (run k g roots sched).heap == M1.sequential_mark g roots)

let mark_par_correct k g roots sched =
  E.run_end k g roots sched;
  SM.sequential_marked g roots;
  marked_as_ext g (run k g roots sched).heap (M1.sequential_mark g roots) (M1.reachable g roots)

/// The same, without the sequential mark: exactly the reachable objects are
/// black, each is its original header made black, and every other word of
/// the heap is unchanged.
val mark_par_reachable (k: cfg) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires pre k g roots /\ (run k g roots sched).finished)
          (ensures (let h = (run k g roots sched).heap in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                       (is_black x h <==> M1.reachable g roots x)) /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ M1.reachable g roots x ==>
                       read_word h (hd_address x) == read_word (makeBlack x g) (hd_address x)) /\
                    (forall (a: hp_addr).
                       (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ M1.reachable g roots x ==>
                          a <> hd_address x) ==>
                       read_word h a == read_word g a)))

let mark_par_reachable k g roots sched = E.run_end k g roots sched

/// ---------------------------------------------------------------------------
/// What a step touches
/// ---------------------------------------------------------------------------

/// Only the owner writes a colour: from any state a run reaches, worker i's
/// step changes the heap only in the header of an enumerated object i owns.
val step_writes_own (k: cfg) (g: heap) (roots: list obj_addr) (sched: list event) (i: nat) (a: hp_addr)
  : Lemma (requires pre k g roots /\
                    (let s = run k g roots sched in
                     read_word (step k s (W i)).heap a <> read_word s.heap a))
          (ensures exists (x: obj_addr).
                     a == hd_address x /\ Seq.mem x (objects zero_addr g) /\ own k x == i)

let step_writes_own k g roots sched i a =
  ctx_of k g roots;
  E.run_inv k g roots sched;
  let s = run k g roots sched in
  if s.finished then () else Ft.wstep_writes k g roots s i

/// Worker i's step reads only what `readable` allows: on any heap h2 that
/// agrees with the state's heap on those words, the step gives the same
/// workers, counter and flags, and writes the same words with the same
/// values.
val step_reads_own (k: cfg) (g: heap) (roots: list obj_addr) (sched: list event) (i: nat) (h2: heap)
  : Lemma (requires pre k g roots /\
                    (let s = run k g roots sched in
                     forall (a: hp_addr). readable k s i a ==> read_word s.heap a == read_word h2 a))
          (ensures (let s = run k g roots sched in
                    let s2 = { s with heap = h2 } in
                    let t1 = step k s (W i) in
                    let t2 = step k s2 (W i) in
                    t1.wks == t2.wks /\ t1.count == t2.count /\ t1.ovf_main == t2.ovf_main /\
                    t1.finished == t2.finished /\
                    (forall (a: hp_addr).
                       (read_word t1.heap a <> read_word s.heap a \/ read_word t2.heap a <> read_word h2 a) ==>
                       read_word t1.heap a == read_word t2.heap a)))

let step_reads_own k g roots sched i h2 =
  ctx_of k g roots;
  E.run_inv k g roots sched;
  let s = run k g roots sched in
  if s.finished then () else Ft.wstep_reads k g roots s i h2

/// So two workers never race: a word worker j's step writes is never a word
/// worker i's step may read, in the same state, for i <> j.
val step_race_free (k: cfg) (g: heap) (roots: list obj_addr) (sched: list event) (i j: nat) (a: hp_addr)
  : Lemma (requires pre k g roots /\ i <> j /\
                    (let s = run k g roots sched in
                     read_word (step k s (W j)).heap a <> read_word s.heap a))
          (ensures ~(readable k (run k g roots sched) i a))

let step_race_free k g roots sched i j a =
  ctx_of k g roots;
  E.run_inv k g roots sched;
  let s = run k g roots sched in
  if s.finished then () else Ft.race_free k g roots s i j a

/// The main thread acts only at the stop barrier.
val main_at_barrier (k: cfg) (s: state)
  : Lemma (requires ~(all_stopped s.wks)) (ensures step k s Main == s)

let main_at_barrier k s = ()

/// ---------------------------------------------------------------------------
/// work_in_flight
/// ---------------------------------------------------------------------------

/// The counter equals the counted entries: every stack entry, inbox entry
/// and item a worker holds.
val count_exact (k: cfg) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires pre k g roots)
          (ensures (let s = run k g roots sched in s.count == counted s.wks))

let count_exact k g roots sched = ctx_of k g roots; C.count_exact k g roots sched

/// A 0 is final: from 0, every worker step leaves the counter at 0.
val zero_final (k: cfg) (g: heap) (roots: list obj_addr) (sched: list event) (i: nat)
  : Lemma (requires pre k g roots /\ (run k g roots sched).count == 0)
          (ensures (step k (run k g roots sched) (W i)).count == 0)

let zero_final k g roots sched i = ctx_of k g roots; C.zero_final k g roots sched i

/// ---------------------------------------------------------------------------
/// Termination
/// ---------------------------------------------------------------------------

/// Every run ends: a schedule has at most `measure (init ...)` effective
/// steps; a step that is not enabled changes nothing, or is a spin step (a
/// worker with nothing to do, while the counter is not 0, moves between
/// Loop and Idle), which keeps the measure and which that worker's next
/// step undoes; and nothing is enabled exactly when marking is done.  So
/// any schedule that keeps taking enabled steps finishes within that many,
/// and the only way to run for ever is for some workers to spin while
/// others are never scheduled.
val mark_par_terminates (k: cfg) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires pre k g roots)
          (ensures (let s = run k g roots sched in
                    effective_steps k (init k g roots) sched <= measure k (init k g roots) /\
                    (forall (e: event). ~(L.mem e (enabled s)) ==>
                       step k s e == s \/
                       (spin s e /\ measure k (step k s e) == measure k s /\
                        step k (step k s e) e == s)) /\
                    (enabled s == [] <==> s.finished)))

let mark_par_terminates k g roots sched =
  ctx_of k g roots;
  GC.Spec.MarkPar2.Init.init_inv k g roots;
  T.effective_le k g roots (init k g roots) sched;
  E.run_inv k g roots sched;
  let s = run k g roots sched in
  FStar.Classical.forall_intro (FStar.Classical.move_requires (T.disabled_spin k g roots s));
  T.enabled_nil k g roots s
