/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesStepOk - the page sweep meets the sweep contract
/// ---------------------------------------------------------------------------
///
/// `step_ok`: every clause of `Iface.sweep_step_post` for
/// `PagesSweep.pstep`, from the unit facts of GC.Spec.Top.PagesStep and the
/// reindexed count of GC.Spec.Top.PagesFreed; `pages_sweep_ok`: the whole
/// `Iface.sweep_ok` (start and end from GC.Spec.Top.PagesSweep).

module GC.Spec.Top.PagesStepOk

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.PagesAllocOk
open GC.Spec.Top.PagesInst
open GC.Spec.Top.PagesSweep
open GC.Spec.Top.PagesStep
open GC.Spec.Top.PagesFreed
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module I = GC.Spec.AllocIface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module G = GC.Spec.Pages.Graft
module MS = GC.Spec.Pages.MidSweep
module SA = GC.Spec.Pages.SweepAll
module Incr = GC.Spec.Pages.Incr
module PF = GC.Spec.Top.PagesFree

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The step post, from its clauses.
let post_intro (#t: Type0) (#k: T.sweep_kind) (a: T.allocator t k) (p: k.T.progress) (h: t) (st: a.T.state)
    (p': k.T.progress) (h': t) (st': a.T.state) (res: T.step_result) (m m': M.mheap)
  : Lemma (requires
             (forall (o: nat). k.T.unswept p' o ==> k.T.unswept p o) /\
             (exists (o: nat). o < m.M.size /\ T.region k p p' o) /\
             m'.M.size == m.M.size /\
             (forall (o: nat). T.swept_white a st h m p p' o ==>
                T.in_use a st' h' m' o == false /\ (forall (w: nat). M.covers m o w ==> T.free_word a st' h' m' w)) /\
             (forall (o: nat). T.in_use a st h m o /\ T.region k p p' o /\ M.col_of m o == M.Black ==>
                T.in_use a st' h' m' o /\ M.col_of m' o == M.White /\ M.same_contents m m' o) /\
             (forall (o: nat). T.in_use a st h m o /\ not (T.region k p p' o) ==>
                T.in_use a st' h' m' o /\ M.same_block m m' o) /\
             (forall (o: nat). T.in_use a st' h' m' o ==> T.in_use a st h m o) /\
             (forall (w: nat). T.free_word a st h m w ==> T.free_word a st' h' m' w) /\
             (forall (w: nat). T.free_word a st' h' m' w ==>
                T.free_word a st h m w \/ (exists (o: nat). M.covers m o w /\ T.swept_white a st h m p p' o)) /\
             res.T.freed_words == M.sum m.M.size (T.swept_words a st h m p p') /\
             a.T.inv (T.Sweeping p') h' st' /\ M.well_formed m')
          (ensures T.sweep_step_post a p h st p' h' st' res m m')
  = norm_spec [delta_only [`%T.sweep_step_post]; iota; zeta] (T.sweep_step_post a p h st p' h' st' res m m')

/// The setting of a step: the unit `q` it sweeps.
let sset (p: pprog) (h: heap) (s: pst) (m: M.mheap) (q: nat) : prop =
  brepr m h /\ pinv (T.Sweeping p) h s /\ M.well_formed m /\ q < n_pages /\
  q == nextu s.ps.pm p.cur /\ Incr.sweeps s.ps.pm q /\ Incr.swept_below s.ps.pm q

let sset_intro (p: pprog) (h: heap) (s: pst) (m: M.mheap)
  : Lemma (requires brepr m h /\ pinv (T.Sweeping p) h s /\ M.well_formed m /\ pdone p == false)
          (ensures sset p h s m (nextu s.ps.pm p.cur))
  = swept_upto_iff p.ppm n_pages;
    MS.pages_ok_sw_elim (gl h s) s.ps;
    nextu_spec s.ps.pm p.cur;
    nextu_found s.ps.pm p.cur

/// The page heap after the step is the step's own heap.
let gl_after (g': heap) (st': pstate) : Lemma (gl g' ({ ps = st'; lo = low g' }) == g') = set_low_self g'

/// In use, on both sides, is `used` on the page heaps.
let use_pre (h: heap) (s: pst) (m: M.mheap) (o: nat)
  : Lemma (requires brepr m h) (ensures T.in_use pa s h m o == used (cabs (gl h s)) o)
  = heq_low m h s; cabs_set_low h s.lo; in_use_used m h s (gl h s) o

let use_post (g': heap) (st': pstate) (o: nat)
  : Lemma (T.in_use pa ({ ps = st'; lo = low g' }) g' (cabs g') o == used (cabs g') o)
  = in_use_used (cabs g') g' ({ ps = st'; lo = low g' }) g' o

/// Free words, on both sides.
let fw_pre (h: heap) (s: pst) (m: M.mheap) (w: nat)
  : Lemma (requires brepr m h) (ensures T.free_word pa s h m w <==> fw (gl h s) w)
  = heq_low m h s; cabs_set_low h s.lo;
    FStar.Classical.forall_intro (pfree_blue h s (gl h s))

let fw_post (g': heap) (st': pstate) (w: nat)
  : Lemma (T.free_word pa ({ ps = st'; lo = low g' }) g' (cabs g') w <==> fw g' w)
  = FStar.Classical.forall_intro (pfree_blue g' ({ ps = st'; lo = low g' }) g')

/// The region is the unit.
let region_unit (p: pprog) (h: heap) (s: pst) (m: M.mheap) (q: nat) (o: nat)
  : Lemma (requires sset p h s m q)
          (ensures (let (g', st') = SA.step (gl h s) s.ps q in
                    let p' = { ppm = st'.pm; cur = q + span s.ps.pm q } in
                    T.region pk p p' o == in_u q (span s.ps.pm q) o /\
                    (punswept p' o ==> punswept p o)))
  = unit_facts (gl h s) s.ps q;
    let (g', st') = SA.step (gl h s) s.ps q in
    region_iff s.ps.pm st'.pm (gl h s) g' q (span s.ps.pm q) o;
    MS.uw_same p.ppm s.ps.pm (pos o)

/// The unit's first word is swept: the measure decreases.
let unit_start (q: nat{q < n_pages}) (k: nat)
  : Lemma (requires k >= 1 /\ q + k <= n_pages)
          (ensures (let o = mpos (page_base q) in o < msize /\ pos o == page_base q /\ in_u q k o))
  = page_base_mono q (q + k);
    page_base_mono 0 q;
    pages_end_bound ();
    base_facts ();
    assert (page_base q == base + q * page_bytes);
    assert (q * page_bytes == 8 * (q * page_wsize));
    FStar.Math.Lemmas.lemma_div_exact (q * page_bytes) 8;
    msize_pos (mpos (page_base q))

#push-options "--z3rlimit 40"
let clause_progress (p: pprog) (h: heap) (s: pst) (m: M.mheap) (q: nat)
  : Lemma (requires sset p h s m q)
          (ensures (let (g', st') = SA.step (gl h s) s.ps q in
                    let p' = { ppm = st'.pm; cur = q + span s.ps.pm q } in
                    (forall (o: nat). punswept p' o ==> punswept p o) /\
                    (exists (o: nat). o < m.M.size /\ T.region pk p p' o)))
  = unit_facts (gl h s) s.ps q;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (region_unit p h s m q));
    unit_start q (span s.ps.pm q);
    region_unit p h s m q (mpos (page_base q))
#pop-options

/// Blocks in use.
#push-options "--z3rlimit 40"
let clause_blocks (p: pprog) (h: heap) (s: pst) (m: M.mheap) (q: nat) (o: nat)
  : Lemma (requires sset p h s m q)
          (ensures (let (g', st') = SA.step (gl h s) s.ps q in
                    let p' = { ppm = st'.pm; cur = q + span s.ps.pm q } in
                    let s' = { ps = st'; lo = low g' } in
                    (T.swept_white pa s h m p p' o ==> T.in_use pa s' g' (cabs g') o == false) /\
                    (T.in_use pa s h m o /\ T.region pk p p' o /\ M.col_of m o == M.Black ==>
                       T.in_use pa s' g' (cabs g') o /\ M.col_of (cabs g') o == M.White /\
                       M.same_contents m (cabs g') o) /\
                    (T.in_use pa s h m o /\ not (T.region pk p p' o) ==>
                       T.in_use pa s' g' (cabs g') o /\ M.same_block m (cabs g') o) /\
                    (T.in_use pa s' g' (cabs g') o ==> T.in_use pa s h m o)))
  = let g0 = gl h s in
    let (g', st') = SA.step g0 s.ps q in
    heq_low m h s;
    region_unit p h s m q o;
    use_pre h s m o;
    use_post g' st' o;
    use_after g0 s.ps q o;
    if used (cabs g0) o && in_u q (span s.ps.pm q) o && M.col_of (cabs g0) o = M.Black
    then black_kept g0 s.ps q o;
    if used (cabs g0) o && not (in_u q (span s.ps.pm q) o)
    then kept_out g0 s.ps q o
#pop-options

/// Free words.
#push-options "--z3rlimit 40"
let clause_words (p: pprog) (h: heap) (s: pst) (m: M.mheap) (q: nat) (w: nat)
  : Lemma (requires sset p h s m q)
          (ensures (let (g', st') = SA.step (gl h s) s.ps q in
                    let p' = { ppm = st'.pm; cur = q + span s.ps.pm q } in
                    let s' = { ps = st'; lo = low g' } in
                    (T.free_word pa s h m w ==> T.free_word pa s' g' (cabs g') w) /\
                    (T.free_word pa s' g' (cabs g') w ==>
                       T.free_word pa s h m w \/ (exists (o: nat). M.covers m o w /\ T.swept_white pa s h m p p' o)) /\
                    (forall (o: nat). T.swept_white pa s h m p p' o /\ M.covers m o w ==> T.free_word pa s' g' (cabs g') w)))
  = let g0 = gl h s in
    let (g', st') = SA.step g0 s.ps q in
    heq_low m h s;
    fw_pre h s m w;
    fw_post g' st' w;
    words_step g0 s.ps q w;
    let k = span s.ps.pm q in
    let sw (o: nat) : Lemma (T.swept_white pa s h m p ({ ppm = st'.pm; cur = q + k }) o ==>
                             (used (cabs g0) o /\ in_u q k o /\ M.col_of (cabs g0) o == M.White))
      = region_unit p h s m q o; use_pre h s m o in
    FStar.Classical.forall_intro sw;
    let ws (o: nat) : Lemma (M.covers (cabs g0) o w /\ used (cabs g0) o /\ in_u q k o /\ M.col_of (cabs g0) o == M.White ==>
                             T.swept_white pa s h m p ({ ppm = st'.pm; cur = q + k }) o)
      = region_unit p h s m q o; use_pre h s m o in
    FStar.Classical.forall_intro ws
#pop-options

/// The words freed: the byte-level count is the model's sum.
#push-options "--z3rlimit 40"
let freed_pt (p: pprog) (h: heap) (s: pst) (m: M.mheap) (q: nat) (o: nat)
  : Lemma (requires sset p h s m q)
          (ensures (let (g', st') = SA.step (gl h s) s.ps q in
                    let p' = { ppm = st'.pm; cur = q + span s.ps.pm q } in
                    fcount (gl h s) s.ps.pm q (objects zero_addr (gl h s)) o == T.swept_words pa s h m p p' o))
  = let g0 = gl h s in
    heq_low m h s;
    region_unit p h s m q o;
    use_pre h s m o;
    used_iff g0 o;
    if pos o + 8 < heap_size && Seq.mem (obj_of o) (objects zero_addr g0) then begin
      obj_of_v o;
      abs_is_block g0 o;
      abs_header g0 o;
      is_white_iff (obj_of o) g0
    end
#pop-options

let clause_freed (p: pprog) (h: heap) (s: pst) (m: M.mheap) (q: nat)
  : Lemma (requires sset p h s m q)
          (ensures (let (g', st') = SA.step (gl h s) s.ps q in
                    let p' = { ppm = st'.pm; cur = q + span s.ps.pm q } in
                    PF.freed_words_of (gl h s) s.ps.pm q == M.sum m.M.size (T.swept_words pa s h m p p')))
  = let g0 = gl h s in
    let (g', st') = SA.step g0 s.ps q in
    let p' = { ppm = st'.pm; cur = q + span s.ps.pm q } in
    heq_low m h s;
    freed_reindex g0 s.ps.pm q;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (freed_pt p h s m q));
    sum_ext msize (fcount g0 s.ps.pm q (objects zero_addr g0)) (T.swept_words pa s h m p p')

/// The invariant again, and the cursor past the unit.
let clause_inv (p: pprog) (h: heap) (s: pst) (m: M.mheap) (q: nat)
  : Lemma (requires sset p h s m q)
          (ensures (let (g', st') = SA.step (gl h s) s.ps q in
                    let p' = { ppm = st'.pm; cur = q + span s.ps.pm q } in
                    pa.T.inv (T.Sweeping p') g' ({ ps = st'; lo = low g' }) /\ M.well_formed (cabs g')))
  = let g0 = gl h s in
    let (g', st') = SA.step g0 s.ps q in
    unit_facts g0 s.ps q;
    Incr.cursor_step g0 s.ps q;
    gl_after g' st';
    inv_walk I.Sweeping g' st';
    abs_well_formed g';
    wf_cabs g'

/// **One step.**
#push-options "--z3rlimit 40"
let step_m (p: pprog) (h: heap) (s: pst) (m: M.mheap)
  : Lemma (requires brepr m h /\ T.sweep_step_pre psweep p h s m)
          (ensures (let (p', h', s', res) = pstep p h s in T.sweep_step_post pa p h s p' h' s' res m (cabs h')))
  = sset_intro p h s m;
    let q = nextu s.ps.pm p.cur in
    let g0 = gl h s in
    let (g', st') = SA.step g0 s.ps q in
    let p' = { ppm = st'.pm; cur = q + span s.ps.pm q } in
    let s' = { ps = st'; lo = low g' } in
    let res = { T.units = 1; T.freed_words = PF.freed_words_of g0 s.ps.pm q } in
    assert (pstep p h s == (p', g', s', res));
    clause_progress p h s m q;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (clause_blocks p h s m q));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (clause_words p h s m q));
    clause_freed p h s m q;
    clause_inv p h s m q;
    post_intro pa p h s p' g' s' res m (cabs g')
#pop-options

let step_ok (p: pprog) (h: heap) (s: pst) : Lemma (T.sweep_step_at byte_rep psweep p h s)
  = let (_, h', _, _) = pstep p h s in
    brepr_cabs h';
    FStar.Classical.forall_intro (FStar.Classical.move_requires (step_m p h s))

/// **The page sweep meets the sweep contract.**
let pages_sweep_ok () : Lemma (T.sweep_ok byte_rep psweep)
  = FStar.Classical.forall_intro_2 start_ok;
    FStar.Classical.forall_intro_3 step_ok;
    FStar.Classical.forall_intro_3 done_ok
