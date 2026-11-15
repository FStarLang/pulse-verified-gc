/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.ParWitness - constructive witnesses for the parallel theorems
/// ---------------------------------------------------------------------------
///
/// The vacuity rule (docs/pages-allocator-proof-plan.md §18, on
/// sheera/pages-allocator): every theorem with hypotheses about heaps has a
/// witness, a state shown to satisfy all its hypotheses, with at least one
/// root, one reachable object, one unreachable object, one pool page and one
/// large run.
///
/// The state is `GC.Spec.Pages.Witness`'s `W`: roots `[A]`; A in a pool page;
/// B at the head of a run, reachable through A's field; C unreachable.  Two
/// workers run the mark round robin.  The lemmas are stated for any heap with
/// `W`'s facts (`wfacts`), and instantiated with `W` at the end (`w_wfacts`),
/// so that no query unfolds how `W` was built.
///
///   - `par_pre`: `Heap.par_pre` holds.
///   - `model_witness`: the model's hypotheses (`view_ok`, `no_marks`,
///     `fair`) hold, and the start state satisfies `inv` and is not finished:
///     so `Safety.step_inv`, `Decrease.step_mu`, `Term.progress`,
///     `Init.init_inv`, `Init.mark_correct` and `Term.terminates` apply.  In
///     the model A and B are reachable and C is not.
///   - `par_terminates_witness`: `par_mark_gc_terminates`'s hypotheses hold;
///     the run finishes, with A's and B's bits set and C's clear.
///   - `sweep_par_seq_witness`: for that bitmap, the pure precondition of
///     `CDrive.sweep_par_seq` holds, and so do the hypotheses of
///     `par_gc_correct` and `mark_marks_from`; the sweep starts with A's pool
///     page and B's run unswept.

module GC.Impl.Pages.ParWitness

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Bitmap
open GC.Spec.Pages.ParMark.Model
open GC.Spec.Pages.ParMark.Reach
open GC.Spec.Pages.ParMark.Heap
open GC.Spec.Pages.ParMark.Inv
open GC.Impl.Pages.ParMarkCorrect

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SS = GC.Spec.Pages.StartSweep
module CSw = GC.Impl.Pages.CSweep
module PMI = GC.Spec.Pages.ParMark.Init
module PMT = GC.Spec.Pages.ParMark.Term
module PV = GC.Spec.Pages.ParMark.Vacuity
module W = GC.Spec.Pages.Witness
module Corr = GC.Spec.Correctness
module HM = GC.Spec.HeapModel

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The facts of the witness
/// ---------------------------------------------------------------------------

/// A pool page holding `a`'s header, and a run headed by the page that
/// starts with `b`'s header, in the state `s`.
let pages (s: pstate) (a b: obj_addr) : prop =
  (exists (i: nat{i < n_pages}). Pool? (entry s.pm i).kind /\
     page_base i <= U64.v a - 8 /\ U64.v a - 8 < page_base (i + 1)) /\
  (exists (j: nat{j < n_pages}). LargeHead? (entry s.pm j).kind /\ U64.v b - 8 == page_base j)

/// `h, s, rs` is in `Idle` with live roots; `a` is a root, `b` is reachable
/// and not a root, `c` is a live object that is not reachable; `a` is in a
/// pool page and `b` heads a run.  Sealed; `wfacts_elim` opens it.
[@@"opaque_to_smt"]
let wfacts (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr) : prop =
  par_pre h s rs /\
  Seq.mem a rs /\ ~(Seq.mem b rs) /\
  Corr.heap_reachable h rs a /\ Corr.heap_reachable h rs b /\ ~(Corr.heap_reachable h rs c) /\
  Seq.mem c (objects zero_addr h) /\ ~(is_blue c h) /\
  pages s a b

let wfacts_elim (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr)
  : Lemma (requires wfacts h s rs a b c)
          (ensures par_pre h s rs /\
                   Seq.mem a rs /\ ~(Seq.mem b rs) /\
                   Corr.heap_reachable h rs a /\ Corr.heap_reachable h rs b /\ ~(Corr.heap_reachable h rs c) /\
                   Seq.mem c (objects zero_addr h) /\ ~(is_blue c h) /\
                   pages s a b)
  = reveal_opaque (`%wfacts) (wfacts h s rs a b c)

/// **`W` has them** (`Heap.par_pre` among them).
let w_wfacts (g: heap)
  : Lemma (requires W.big_enough)
          (ensures wfacts (W.w_heap g) (W.w_state g) (W.w_roots g) (W.oA g) (W.oB g) (W.oC g))
  = W.w_ok g;
    reveal_opaque (`%wfacts) (wfacts (W.w_heap g) (W.w_state g) (W.w_roots g) (W.oA g) (W.oB g) (W.oC g))

/// ---------------------------------------------------------------------------
/// The model
/// ---------------------------------------------------------------------------

/// Two workers; the prototype's other parameters, small.
let p2 (h: heap) : GTot params = hparams h 2 4 2 3 1 2
let bs0 : Seq.seq U32.t = Seq.create bm_len 0ul

/// In the model, `a` and `b` are reachable and `c` is not.
#push-options "--z3rlimit 40"
let model_reach (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr)
  : Lemma (requires wfacts h s rs a b c)
          (ensures reach (p2 h) (root_tgts h rs) (U64.v a) /\ reach (p2 h) (root_tgts h rs) (U64.v b) /\
                   ~(reach (p2 h) (root_tgts h rs) (U64.v c)))
  = wfacts_elim h s rs a b c;
    hparams_of h 2 4 2 3 1 2;
    reach_iff h s rs (p2 h) (U64.v a);
    reach_iff h s rs (p2 h) (U64.v b);
    reach_iff h s rs (p2 h) (U64.v c);
    HM.graph_vertices_mem h a;
    HM.graph_vertices_mem h b;
    HM.graph_vertices_mem h c
#pop-options

let model_view (h: heap) (s: pstate) (rs: Seq.seq obj_addr)
  : Lemma (requires par_pre h s rs) (ensures view_ok (p2 h) (hview h) (root_tgts h rs))
  = hparams_of h 2 4 2 3 1 2;
    view_ok_heap h s rs (p2 h)

/// **The model's hypotheses** hold, and its start satisfies the invariant
/// and is not finished.
let model_witness (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr)
  : Lemma (requires wfacts h s rs a b c)
          (ensures (let rts = root_tgts h rs in
                    let s0 = init (p2 h) bs0 rts in
                    view_ok (p2 h) (hview h) rts /\ PMI.no_marks bs0 /\ PMT.fair 2 (PV.round_robin 2) /\
                    inv (p2 h) (hview h) rts s0 /\ ~(all_done s0) /\
                    reach (p2 h) rts (U64.v a) /\ reach (p2 h) rts (U64.v b) /\ ~(reach (p2 h) rts (U64.v c))))
  = wfacts_elim h s rs a b c;
    model_view h s rs;
    PV.zero_no_marks ();
    PMI.init_inv (p2 h) (hview h) (root_tgts h rs) bs0;
    PV.init_not_done (p2 h) bs0 (root_tgts h rs);
    PV.round_robin_fair 2;
    model_reach h s rs a b c

/// ---------------------------------------------------------------------------
/// The bitmap the mark leaves
/// ---------------------------------------------------------------------------

/// What a finished run leaves, and what `CDrive.sweep_par_seq` needs of it.
/// Sealed, so that the existential over the run's length stays light.
[@@"opaque_to_smt"]
let finished (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr) (m: mstate) : prop =
  par_conclusion h s rs m /\
  marks_reach (p2 h) (root_tgts h rs) m.bs /\ Seq.length m.bs == bm_len /\
  marked m.bs (U64.v a - 8) /\ marked m.bs (U64.v b - 8) /\ ~(marked m.bs (U64.v c - 8))

let concl_of (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr) (m: mstate)
  : Lemma (requires wfacts h s rs a b c /\ all_done m /\
                    marks_reach (p2 h) (root_tgts h rs) m.bs /\ Seq.length m.bs == bm_len)
          (ensures par_conclusion h s rs m)
  = wfacts_elim h s rs a b c;
    hparams_of h 2 4 2 3 1 2;
    par_gc_correct h s rs (p2 h) m.bs

let marks_of (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr) (m: mstate)
  : Lemma (requires wfacts h s rs a b c /\ marks_reach (p2 h) (root_tgts h rs) m.bs)
          (ensures marked m.bs (U64.v a - 8) /\ marked m.bs (U64.v b - 8) /\ ~(marked m.bs (U64.v c - 8)))
  = model_reach h s rs a b c;
    assert (marked m.bs (U64.v a - 8));
    assert (marked m.bs (U64.v b - 8))

let finished_of (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr) (m: mstate)
  : Lemma (requires wfacts h s rs a b c /\ all_done m /\
                    marks_reach (p2 h) (root_tgts h rs) m.bs /\ Seq.length m.bs == bm_len)
          (ensures finished h s rs a b c m)
  = concl_of h s rs a b c m;
    marks_of h s rs a b c m;
    reveal_opaque (`%finished) (finished h s rs a b c m)

let finished_elim (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr) (m: mstate)
  : Lemma (requires finished h s rs a b c m)
          (ensures par_conclusion h s rs m /\
                   marks_reach (p2 h) (root_tgts h rs) m.bs /\ Seq.length m.bs == bm_len /\
                   marked m.bs (U64.v a - 8) /\ marked m.bs (U64.v b - 8) /\ ~(marked m.bs (U64.v c - 8)))
  = reveal_opaque (`%finished) (finished h s rs a b c m)

/// The marks alone.
let finished_marks (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr) (m: mstate)
  : Lemma (requires finished h s rs a b c m)
          (ensures marks_reach (p2 h) (root_tgts h rs) m.bs /\ Seq.length m.bs == bm_len /\
                   marked m.bs (U64.v a - 8) /\ marked m.bs (U64.v b - 8) /\ ~(marked m.bs (U64.v c - 8)))
  = reveal_opaque (`%finished) (finished h s rs a b c m)

/// The run from the start under the schedule `sched`.
let run_s (h: heap) (rs: Seq.seq obj_addr) (sched: nat -> nat) (n: nat) : GTot mstate =
  PMT.runf (p2 h) (init (p2 h) bs0 (root_tgts h rs)) sched n

/// **`par_mark_gc_terminates`**: its hypotheses hold, and some point of the
/// run under any fair schedule of two workers is finished, with `a`'s and
/// `b`'s bits set and `c`'s clear.
let par_terminates_gen (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr) (sched: nat -> nat)
  : Lemma (requires wfacts h s rs a b c /\ PMT.fair 2 sched)
          (ensures par_pre h s rs /\ PMI.no_marks bs0 /\
                   (exists (n: nat). finished h s rs a b c (run_s h rs sched n)))
  = wfacts_elim h s rs a b c;
    PV.zero_no_marks ();
    model_view h s rs;
    assert ((p2 h).k == 2);
    par_term h s rs (p2 h) bs0 sched;
    let fin (n: nat)
      : Lemma (requires all_done (run_s h rs sched n) /\
                        marks_reach (p2 h) (root_tgts h rs) (run_s h rs sched n).bs /\
                        Seq.length (run_s h rs sched n).bs == bm_len)
              (ensures finished h s rs a b c (run_s h rs sched n))
      = finished_of h s rs a b c (run_s h rs sched n)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fin)

/// What `CDrive.sweep_par_seq` (its pure precondition), `par_gc_correct`
/// and `mark_marks_from` need of the bitmap `bs`, and what makes it a
/// non-trivial one: `a`'s and `b`'s bits set, `c`'s clear, and the sweep
/// starting with `a`'s pool page and `b`'s run unswept.
let sweep_pre (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr) (bs: Seq.seq U32.t) : prop =
  Seq.length bs == bm_len /\ map_ok s.pm /\
  CSw.marks_from h bs (SS.start_sweep s).pm 0 n_pages /\
  par_pre h s rs /\ hp_of h (p2 h) /\ marks_reach (p2 h) (root_tgts h rs) bs /\
  marked bs (U64.v a - 8) /\ marked bs (U64.v b - 8) /\ ~(marked bs (U64.v c - 8)) /\
  pages (SS.start_sweep s) a b /\
  (forall (j: nat{j < n_pages}). (entry (SS.start_sweep s).pm j).kind =!= Free ==>
     not (entry (SS.start_sweep s).pm j).swept)

/// The sweep's start keeps the kinds, and leaves every page that is not
/// free unswept.
let start_pages (s: pstate) (a b: obj_addr)
  : Lemma (requires pages s a b)
          (ensures pages (SS.start_sweep s) a b /\
                   (forall (j: nat{j < n_pages}). (entry (SS.start_sweep s).pm j).kind =!= Free ==>
                      not (entry (SS.start_sweep s).pm j).swept))
  = FStar.Classical.forall_intro (SS.clear_entry s.pm)

let sweep_pre_of (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr) (m: mstate)
  : Lemma (requires wfacts h s rs a b c /\ finished h s rs a b c m)
          (ensures sweep_pre h s rs a b c m.bs)
  = finished_marks h s rs a b c m;
    wfacts_elim h s rs a b c;
    hparams_of h 2 4 2 3 1 2;
    start_pages s a b;
    mark_marks_from h s rs (p2 h) m.bs

/// **`CDrive.sweep_par_seq`**, **`par_gc_correct`** and `mark_marks_from`:
/// for the bitmap the mark leaves, their hypotheses hold.
let sweep_par_seq_gen (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr) (sched: nat -> nat)
  : Lemma (requires wfacts h s rs a b c /\ PMT.fair 2 sched)
          (ensures exists (bs: Seq.seq U32.t). sweep_pre h s rs a b c bs)
  = par_terminates_gen h s rs a b c sched;
    let one (n: nat)
      : Lemma (requires finished h s rs a b c (run_s h rs sched n))
              (ensures exists (bs: Seq.seq U32.t). sweep_pre h s rs a b c bs)
      = sweep_pre_of h s rs a b c (run_s h rs sched n);
        FStar.Classical.exists_intro (sweep_pre h s rs a b c) (run_s h rs sched n).bs
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// The finished state of the run: **`Complete.cnt_zero_complete`**,
/// `cnt_zero_marks` and `all_done_marks`'s hypotheses hold of it, with `b`
/// reachable and `c` not.
let final_ok (h: heap) (rs: Seq.seq obj_addr) (b c: obj_addr) (m: mstate) : prop =
  view_ok (p2 h) (hview h) (root_tgts h rs) /\ inv (p2 h) (hview h) (root_tgts h rs) m /\
  all_done m /\ m.cnt == 0 /\
  reach (p2 h) (root_tgts h rs) (U64.v b) /\ ~(reach (p2 h) (root_tgts h rs) (U64.v c))

let final_one (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr) (sched: nat -> nat) (n: nat)
  : Lemma (requires wfacts h s rs a b c /\ all_done (run_s h rs sched n))
          (ensures final_ok h rs b c (run_s h rs sched n))
  = let rts = root_tgts h rs in
    let m = run_s h rs sched n in
    model_witness h s rs a b c;
    PMT.runf_inv (p2 h) (hview h) rts (init (p2 h) bs0 rts) sched n;
    inv_reveal (p2 h) (hview h) rts m;
    assert ((Seq.index m.ws 0).pc == Done)

let final_gen (h: heap) (s: pstate) (rs: Seq.seq obj_addr) (a b c: obj_addr) (sched: nat -> nat)
  : Lemma (requires wfacts h s rs a b c /\ PMT.fair 2 sched)
          (ensures exists (n: nat). final_ok h rs b c (run_s h rs sched n))
  = wfacts_elim h s rs a b c;
    PV.zero_no_marks ();
    model_view h s rs;
    assert ((p2 h).k == 2);
    par_term h s rs (p2 h) bs0 sched;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (final_one h s rs a b c sched))

/// ---------------------------------------------------------------------------
/// Instantiated with `W`
/// ---------------------------------------------------------------------------

let par_terminates_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures (let h = W.w_heap g in
                    let rs = W.w_roots g in
                    par_pre h (W.w_state g) rs /\ PMI.no_marks bs0 /\ PMT.fair 2 (PV.round_robin 2) /\
                    (exists (n: nat). finished h (W.w_state g) rs (W.oA g) (W.oB g) (W.oC g)
                                        (run_s h rs (PV.round_robin 2) n))))
  = w_wfacts g;
    PV.round_robin_fair 2;
    par_terminates_gen (W.w_heap g) (W.w_state g) (W.w_roots g) (W.oA g) (W.oB g) (W.oC g) (PV.round_robin 2)

let model_witness_w (g: heap)
  : Lemma (requires W.big_enough)
          (ensures (let h = W.w_heap g in
                    let rts = root_tgts h (W.w_roots g) in
                    let s0 = init (p2 h) bs0 rts in
                    view_ok (p2 h) (hview h) rts /\ PMI.no_marks bs0 /\ PMT.fair 2 (PV.round_robin 2) /\
                    inv (p2 h) (hview h) rts s0 /\ ~(all_done s0) /\
                    reach (p2 h) rts (U64.v (W.oA g)) /\ reach (p2 h) rts (U64.v (W.oB g)) /\
                    ~(reach (p2 h) rts (U64.v (W.oC g)))))
  = w_wfacts g;
    model_witness (W.w_heap g) (W.w_state g) (W.w_roots g) (W.oA g) (W.oB g) (W.oC g)

let sweep_par_seq_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures exists (bs: Seq.seq U32.t).
                     sweep_pre (W.w_heap g) (W.w_state g) (W.w_roots g) (W.oA g) (W.oB g) (W.oC g) bs)
  = w_wfacts g;
    PV.round_robin_fair 2;
    sweep_par_seq_gen (W.w_heap g) (W.w_state g) (W.w_roots g) (W.oA g) (W.oB g) (W.oC g) (PV.round_robin 2)

let final_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures exists (n: nat). final_ok (W.w_heap g) (W.w_roots g) (W.oB g) (W.oC g)
                                     (run_s (W.w_heap g) (W.w_roots g) (PV.round_robin 2) n))
  = w_wfacts g;
    PV.round_robin_fair 2;
    final_gen (W.w_heap g) (W.w_state g) (W.w_roots g) (W.oA g) (W.oB g) (W.oC g) (PV.round_robin 2)
