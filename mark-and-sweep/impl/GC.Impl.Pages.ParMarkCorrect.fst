/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.ParMarkCorrect - the parallel mark meets the parallel sweep
/// ---------------------------------------------------------------------------
///
/// When the bitmap the parallel mark leaves has exactly the headers of the
/// objects reachable from the roots (`Reach.marks_reach`, the model's final
/// state), on a heap in the allocator's `Idle` state:
///
///   - **`mark_marks_from`**: its marks lie where the parallel sweep reads them
///     (`CSweep.marks_from`, the hypothesis of `CDrive.sweep_par_seq`): on the
///     slot headers of white blocks in a pool page, on the walk of a run, and
///     none in a free page;
///   - **`par_gc_correct`**: the collection `CDrive.sweep_par_seq` computes,
///     `GcCorrect.collect (with_marks h bs) st`, is safe and live
///     (`gc_safe_pages`, `gc_live_pages`), by `GcCorrect.gc_correct_gen` and
///     `ParMark.Marked.bitmap_marked`.

module GC.Impl.Pages.ParMarkCorrect

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Bitmap
open GC.Spec.Pages.ParMark.Model
open GC.Spec.Pages.ParMark.Reach
open GC.Spec.Pages.ParMark.Heap
open GC.Spec.Pages.ParMark.Marked

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module L = FStar.List.Tot
module R = GC.Spec.Pages.Replace
module PA = GC.Spec.Pages.Allocator
module I = GC.Spec.AllocIface
module MP = GC.Spec.Pages.MarkPhase
module SU = GC.Spec.Pages.SweepUnits
module SS = GC.Spec.Pages.StartSweep
module BU = GC.Spec.Pages.BitmapUnits
module GC = GC.Spec.Pages.GcCorrect
module CSw = GC.Impl.Pages.CSweep
module PMI = GC.Spec.Pages.ParMark.Init
module PMT = GC.Spec.Pages.ParMark.Term

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Where the marks lie
/// ---------------------------------------------------------------------------

/// A walk from `a` that reaches `x` and `e`, with `x < e`, has `x` on it.
#push-options "--fuel 1"
let rec on_walk_of (g: heap) (a e x: nat)
  : Lemma (requires steps_to g a x /\ steps_to g a e /\ x < e)
          (ensures BU.on_walk g a e x)
          (decreases (if a < e then e - a else 0))
  = steps_to_le g a x;
    BU.on_walk_step g a e x;
    steps_to_next g (mk_hp_addr a) e;
    R.block_bytes_words g a;
    if a < x then begin
      steps_to_next g (mk_hp_addr a) x;
      on_walk_of g (a + words_at g a * 8) e x
    end
#pop-options

/// A marked word is the header of a live object, reached by the walk of its
/// unit.
let marked_obj (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq U32.t)
  (j: nat{j < n_pages}) (x: nat)
  : Lemma (requires setting h st roots p bs /\ marked bs x /\ walk_page st.pm j /\ page_base j <= x)
          (ensures color_at h x =!= Blue /\ steps_to h (page_base j) x /\ x + 8 < heap_size /\
                   (exists (y: obj_addr). U64.v y == x + 8 /\ Seq.mem y (objects zero_addr h)))
  = setting_elim h st roots p bs;
    idle_facts h st;
    marked_reach h st roots p bs x;
    let yo = as_obj h (x + 8) in
    hw_obj h yo;
    R.hdr_obj h yo;
    is_blue_iff yo h;
    R.obj_iff h yo;
    walk_pages_reached h st.pm j;
    R.steps_to_det h (U64.v zero_addr) (page_base j) x

#push-options "--z3rlimit 40"
let unit_ok (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq U32.t) (j: nat{j < n_pages})
  : Lemma (requires setting h st roots p bs)
          (ensures CSw.unit_marks h bs (SS.start_sweep st).pm j)
  = setting_elim h st roots p bs;
    idle_facts h st;
    let pm' = (SS.start_sweep st).pm in
    SS.clear_entry st.pm j;
    assert (page_shape h st.pm j);
    match (entry st.pm j).kind with
    | Free ->
      let one (x: nat) : Lemma (page_base j <= x /\ x < page_base (j + 1) ==> not (marked bs x))
        = if page_base j <= x && x < page_base (j + 1) && marked bs x then begin
            marked_obj h st roots p bs j x;
            MP.free_page_only h j x
          end
      in
      FStar.Classical.forall_intro one
    | Pool c ->
      assert (MP.all_swept st);
      reveal_opaque (`%pages_ok) pages_ok;
      assert (pool_white h st.pm j);
      let on_slot (x: nat)
        : Lemma (page_base j <= x /\ x < page_base (j + 1) /\ marked bs x ==>
                 (exists (k: nat). k < n_slots c /\ x == slot_base j c k))
        = if page_base j <= x && x < page_base (j + 1) && marked bs x then begin
            marked_obj h st roots p bs j x;
            MP.slot0 j c;
            SU.pool_pos_from h j c 0 x
          end
      in
      let colours (k: nat)
        : Lemma (k < n_slots c ==>
                 (marked bs (slot_base j c k) ==> color_at h (slot_base j c k) == White) /\
                 (~(marked bs (slot_base j c k)) ==> ~(color_at h (slot_base j c k) == Black)))
        = if k < n_slots c then begin
            assert (slot_ok h j c k);
            slot_in_page j c k;
            if marked bs (slot_base j c k) then marked_obj h st roots p bs j (slot_base j c k)
          end
      in
      FStar.Classical.forall_intro on_slot;
      FStar.Classical.forall_intro colours
    | LargeHead n ->
      let one (x: nat)
        : Lemma (page_base j <= x /\ x < page_base (j + n) /\ marked bs x ==>
                 BU.on_walk h (page_base j) (page_base (j + n)) x)
        = if page_base j <= x && x < page_base (j + n) && marked bs x then begin
            marked_obj h st roots p bs j x;
            on_walk_of h (page_base j) (page_base (j + n)) x
          end
      in
      FStar.Classical.forall_intro one
    | LargeCont -> ()
#pop-options

/// **The marks lie where the parallel sweep reads them.**
let mark_marks_from (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq U32.t)
  : Lemma (requires par_pre h st roots /\ hp_of h p /\ Seq.length bs == bm_len /\
                    marks_reach p (root_tgts h roots) bs)
          (ensures CSw.marks_from h bs (SS.start_sweep st).pm 0 n_pages /\ map_ok st.pm)
  = setting_intro h st roots p bs;
    idle_facts h st;
    let one (j: nat{j < n_pages}) : Lemma (0 <= j /\ j < n_pages ==> CSw.unit_marks h bs (SS.start_sweep st).pm j)
      = unit_ok h st roots p bs j
    in
    FStar.Classical.forall_intro one

/// ---------------------------------------------------------------------------
/// The collection
/// ---------------------------------------------------------------------------

/// **The parallel collection is correct.**  The bitmap is the parallel
/// mark's result; `GcCorrect.collect (with_marks h bs) st` is what
/// `CDrive.sweep_par_seq` computes from it, whose hypotheses hold too.
let par_gc_correct (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq U32.t)
  : Lemma (requires par_pre h st roots /\ hp_of h p /\ Seq.length bs == bm_len /\
                    marks_reach p (root_tgts h roots) bs)
          (ensures CSw.marks_from h bs (SS.start_sweep st).pm 0 n_pages /\ map_ok st.pm /\
                   (let (g, st') = GC.collect (with_marks h bs) st in
                    GC.gc_safe_pages h g st' roots /\ GC.gc_live_pages h g st' roots))
  = mark_marks_from h st roots p bs;
    bitmap_marked h st roots p bs;
    GC.gc_correct_gen h (with_marks h bs) st roots

/// **The parallel mark, then the parallel sweep, is a correct collection.**
/// The model of the mark (`GC.Spec.Pages.ParMark.Model`), run from an
/// all-zero bitmap with the roots' targets claimed, in any interleaving of
/// its `k` workers' steps that ends with every worker finished, leaves a
/// bitmap that meets the parallel sweep's precondition (`CSweep.marks_from`,
/// with `map_ok`: the hypotheses of `CDrive.sweep_par_seq`), and the
/// collection `sweep_par_seq` then computes, `collect (with_marks h bs) st`,
/// is safe and live (`gc_safe_pages`, `gc_live_pages`).
let par_mark_gc_correct (h: heap) (st: pstate) (roots: Seq.seq obj_addr)
  (k pkt chunk maxlen: pos) (smin: nat) (tickp: pos) (bs0: Seq.seq U32.t) (sched: list nat)
  : Lemma (requires par_pre h st roots /\ PMI.no_marks bs0)
          (ensures (let p = hparams h k pkt chunk maxlen smin tickp in
                    let s = run p (init p bs0 (root_tgts h roots)) sched in
                    all_done s ==>
                    (CSw.marks_from h s.bs (SS.start_sweep st).pm 0 n_pages /\ map_ok st.pm /\
                     (let (g, st') = GC.collect (with_marks h s.bs) st in
                      GC.gc_safe_pages h g st' roots /\ GC.gc_live_pages h g st' roots))))
  = let p = hparams h k pkt chunk maxlen smin tickp in
    let rts = root_tgts h roots in
    hparams_of h k pkt chunk maxlen smin tickp;
    view_ok_heap h st roots p;
    PMI.mark_correct p (hview h) rts bs0 sched;
    let s = run p (init p bs0 rts) sched in
    FStar.Classical.move_requires (par_gc_correct h st roots p) s.bs

/// **With termination**: under any fair schedule of the `k` workers, the
/// mark finishes, and the parallel sweep's precondition and the
/// collection's correctness hold for the bitmap it leaves.
let par_conclusion (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (s: mstate) : prop =
  all_done s /\
  CSw.marks_from h s.bs (SS.start_sweep st).pm 0 n_pages /\ map_ok st.pm /\
  (let (g, st') = GC.collect (with_marks h s.bs) st in
   GC.gc_safe_pages h g st' roots /\ GC.gc_live_pages h g st' roots)

let par_pick (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (s0: mstate) (sched: nat -> nat)
  : Lemma (requires par_pre h st roots /\ hp_of h p /\
                    (exists (n: nat). all_done (PMT.runf p s0 sched n) /\
                                 marks_reach p (root_tgts h roots) (PMT.runf p s0 sched n).bs /\
                                 Seq.length (PMT.runf p s0 sched n).bs == bm_len))
          (ensures exists (n: nat). par_conclusion h st roots (PMT.runf p s0 sched n))
  = eliminate exists (n: nat). all_done (PMT.runf p s0 sched n) /\
                          marks_reach p (root_tgts h roots) (PMT.runf p s0 sched n).bs /\
                          Seq.length (PMT.runf p s0 sched n).bs == bm_len
    with par_gc_correct h st roots p (PMT.runf p s0 sched n).bs

let par_term (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs0: Seq.seq U32.t) (sched: nat -> nat)
  : Lemma (requires view_ok p (hview h) (root_tgts h roots) /\ PMI.no_marks bs0 /\ PMT.fair p.k sched)
          (ensures exists (n: nat). all_done (PMT.runf p (init p bs0 (root_tgts h roots)) sched n) /\
                               marks_reach p (root_tgts h roots) (PMT.runf p (init p bs0 (root_tgts h roots)) sched n).bs /\
                               Seq.length (PMT.runf p (init p bs0 (root_tgts h roots)) sched n).bs == bm_len)
  = PMT.terminates p (hview h) (root_tgts h roots) bs0 sched

/// **With termination**: under any fair schedule of the `k` workers, the
/// mark finishes, and the parallel sweep's precondition and the
/// collection's correctness hold for the bitmap it leaves.
let par_mark_gc_terminates (h: heap) (st: pstate) (roots: Seq.seq obj_addr)
  (k pkt chunk maxlen: pos) (smin: nat) (tickp: pos) (bs0: Seq.seq U32.t) (sched: nat -> nat)
  : Lemma (requires par_pre h st roots /\ PMI.no_marks bs0 /\ PMT.fair k sched)
          (ensures (let p = hparams h k pkt chunk maxlen smin tickp in
                    exists (n: nat). par_conclusion h st roots (PMT.runf p (init p bs0 (root_tgts h roots)) sched n)))
  = let p = hparams h k pkt chunk maxlen smin tickp in
    hparams_of h k pkt chunk maxlen smin tickp;
    view_ok_heap h st roots p;
    par_term h st roots p bs0 sched;
    par_pick h st roots p (init p bs0 (root_tgts h roots)) sched

/// ---------------------------------------------------------------------------
/// Vacuity
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
[@@expect_failure [19]]
let par_gc_correct_hyps_not_false (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq U32.t)
  : Lemma (requires par_pre h st roots /\ hp_of h p /\ Seq.length bs == bm_len /\
                    marks_reach p (root_tgts h roots) bs)
          (ensures False)
  = ()
#pop-options

/// The hypotheses hold together: the first heap of pages, no roots, an
/// empty bitmap.
#push-options "--fuel 1"
let rec no_reach_t (p: params) (y: nat) (r: reach_t p [] y) : Lemma False (decreases r)
  = match r with
    | RRoot _ -> assert_norm (L.mem y [] == false)
    | RStep x r' _ _ -> no_reach_t p x r'
#pop-options

#push-options "--fuel 1"
let par_witness (g: heap)
  : Lemma (let h = GC.Spec.Pages.Init.init_heap g in
           let p = hparams h 1 1 1 1 0 1 in
           par_pre h GC.Spec.Pages.Init.init_state Seq.empty /\ hp_of h p /\
           Seq.length (Seq.create bm_len 0ul) == bm_len /\
           marks_reach p (root_tgts h Seq.empty) (Seq.create bm_len 0ul))
  = let h = GC.Spec.Pages.Init.init_heap g in
    let p = hparams h 1 1 1 1 0 1 in
    GC.Spec.Pages.Alloc.init_alloc_pre g;
    GC.Spec.Mark.create_graph_wf_from_heap h;
    assert (GC.Spec.HeapGraph.coerce_to_vertex_list (Seq.empty #obj_addr) == Seq.empty);
    SP.lemma_seq_list_bij (Seq.empty #obj_addr);
    assert (Seq.seq_to_list (Seq.empty #obj_addr) == []);
    assert (root_tgts h Seq.empty == []);
    let none (a: nat) : Lemma (~(marked (Seq.create bm_len 0ul) a) /\
                               ~(exists (y: nat). reach p [] y /\ a == y - 8))
      = let bs = Seq.create bm_len 0ul in
        if in_pages a then begin
          widx_bound a;
          zero_bits (widx a % 32)
        end;
        let nr (y: nat) : Lemma (~(reach p [] y))
          = if FStar.IndefiniteDescription.strong_excluded_middle (reach p [] y) then
              eliminate exists (r: reach_t p [] y). True with no_reach_t p y r
        in
        FStar.Classical.forall_intro nr
    in
    FStar.Classical.forall_intro none
#pop-options

let par_gc_correct_applies (g: heap)
  : Lemma (let h = GC.Spec.Pages.Init.init_heap g in
           let (g', st') = GC.collect (with_marks h (Seq.create bm_len 0ul)) GC.Spec.Pages.Init.init_state in
           GC.gc_safe_pages h g' st' Seq.empty /\ GC.gc_live_pages h g' st' Seq.empty)
  = par_witness g;
    let h = GC.Spec.Pages.Init.init_heap g in
    par_gc_correct h GC.Spec.Pages.Init.init_state Seq.empty (hparams h 1 1 1 1 0 1) (Seq.create bm_len 0ul)

/// The terminating theorem applies to the first heap of pages, with two
/// workers under round-robin scheduling.
let par_mark_terminates_applies (g: heap)
  : Lemma (let h = GC.Spec.Pages.Init.init_heap g in
           let p = hparams h 2 4 2 3 1 2 in
           exists (n: nat). par_conclusion h GC.Spec.Pages.Init.init_state Seq.empty
                         (PMT.runf p (init p (Seq.create bm_len 0ul) (root_tgts h Seq.empty))
                                   (GC.Spec.Pages.ParMark.Vacuity.round_robin 2) n))
  = let h = GC.Spec.Pages.Init.init_heap g in
    par_witness g;
    GC.Spec.Pages.ParMark.Vacuity.zero_no_marks ();
    GC.Spec.Pages.ParMark.Vacuity.round_robin_fair 2;
    par_mark_gc_terminates h GC.Spec.Pages.Init.init_state Seq.empty 2 4 2 3 1 2 (Seq.create bm_len 0ul)
      (GC.Spec.Pages.ParMark.Vacuity.round_robin 2)
