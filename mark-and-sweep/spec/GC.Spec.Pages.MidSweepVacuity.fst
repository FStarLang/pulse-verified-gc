/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.MidSweepVacuity - a witness for allocation during the sweep
/// ---------------------------------------------------------------------------
///
/// The vacuity rule (plan §18): the theorems of plan §20.4 have a
/// constructive witness, derived from the shared witness `W`
/// (`GC.Spec.Pages.Witness`: roots `[A]`; A in a pool page; B heading a
/// run, reachable through A; C unreachable) by the theorems themselves.
///
/// From the sweep's start of `W`'s mark (`Vacuity.hm`, `Vacuity.s_sw`),
/// where every page that is not free is unswept:
///
///   0. the start: `pages_ok_sw` (`sw_start`); C is a dead object of an
///      unswept page, not in use mid-sweep, and B is in use;
///   1. the sweep of C's pool page (`step_sw`): that page swept, B's run
///      unswept; the dead object's slot, or the whole page, is now free;
///   2. an allocation in `Sweeping` there succeeds (`alloc_sw_ok`), its new
///      object white in a swept page; the caller clears its field, and the
///      heap is in `pages_ok_sw` with B's run still unswept;
///   3. the sweep of B's run (`step_sw`);
///   4. the rest of the sweep ends in `Idle` (`sweep_rest`, `sw_end`).
///
/// As a run (`MidSweepRun.sw_run`): start, step, allocation, step.

module GC.Spec.Pages.MidSweepVacuity

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
open GC.Spec.Pages.Frame
open GC.Spec.Pages.MidSweep
open GC.Spec.Pages.MidSweepRun

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module W = GC.Spec.Pages.Witness
module V = GC.Spec.Pages.Vacuity
module SA = GC.Spec.Pages.SweepAll
module SS = GC.Spec.Pages.StartSweep
module SST = GC.Spec.Pages.SweepStep
module SP = GC.Spec.Pages.SweepPage
module Pool = GC.Spec.Pages.Pool
module Th = GC.Spec.Pages.Theorems
module R = GC.Spec.Pages.Replace
module MA = GC.Spec.Pages.MidSweepAlloc
module MS = GC.Spec.Pages.MidSweepStep
module Sc = GC.Spec.Pages.Scrub
module G = GC.Spec.Pages.Graft
module Corr = GC.Spec.Correctness
module GcC = GC.Spec.Pages.GcCorrect
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Where C is
/// ---------------------------------------------------------------------------

/// C, the dead object, is in a slot of a pool page of A's class.
#push-options "--z3rlimit 40"
let c_page (g: heap)
  : Lemma (requires W.big_enough)
          (ensures exists (j: nat{j < n_pages}) (k: nat).
                     k < n_slots W.cA /\ W.kind_of (W.w_state g) j == Pool W.cA /\
                     U64.v (W.oC g) == slot_obj j W.cA k)
  = W.step2 g;
    W.step3 g;
    W.sizes ();
    cls_bounds 0;
    let s2 = W.s2 g in
    let g2 = W.g2 g in
    W.alloc_small_is g2 s2 W.wzS;
    W.small_kinds false g2 s2 W.wzS;
    class_of_fits (W.wzS + 1);
    Pool.small_wz_intro W.wzS W.cA;
    if Pool.avail_at s2 W.cA <> 0UL then begin
      W.pop_kinds false g2 s2 W.cA W.wzS;
      Pool.pop_ctx_intro g2 s2 W.cA
    end
#pop-options

/// The page of C at the sweep's start: an unswept pool page of A's class.
let c_page_at_start (g: heap)
  : Lemma (requires W.big_enough)
          (ensures exists (j: nat{j < n_pages}) (k: nat).
                     k < n_slots W.cA /\ (entry (V.s_sw g).pm j).kind == Pool W.cA /\
                     not (entry (V.s_sw g).pm j).swept /\
                     U64.v (W.oC g) == slot_obj j W.cA k)
  = c_page g;
    FStar.Classical.forall_intro (SS.clear_entry (V.st g).pm)

let jc_prop (g: heap) (j: nat{j < n_pages}) : prop =
  exists (k: nat). k < n_slots W.cA /\ (entry (V.s_sw g).pm j).kind == Pool W.cA /\
              not (entry (V.s_sw g).pm j).swept /\ U64.v (W.oC g) == slot_obj j W.cA k

/// C's page.
let jC (g: heap{W.big_enough}) : GTot (j: nat{j < n_pages /\ jc_prop g j}) =
  c_page_at_start g;
  FStar.IndefiniteDescription.indefinite_description_ghost (j: nat{j < n_pages}) (fun j -> jc_prop g j)

/// C's header lies in an unswept page.
let c_uw (g: heap)
  : Lemma (requires W.big_enough) (ensures unswept_at (V.s_sw g).pm (W.oC g))
  = let pm = (V.s_sw g).pm in
    let j = jC g in
    eliminate exists (k: nat). k < n_slots W.cA /\ (entry pm j).kind == Pool W.cA /\
                          not (entry pm j).swept /\ U64.v (W.oC g) == slot_obj j W.cA k
    with begin
      slot_in_page j W.cA k;
      slots_fill_page j W.cA;
      page_uw pm j (U64.v (W.oC g) - 8)
    end

/// ---------------------------------------------------------------------------
/// 0. The start
/// ---------------------------------------------------------------------------

let g0 (g: heap) : GTot heap = V.hm g
let s0 (g: heap) : GTot pstate = V.s_sw g

/// C in the marked heap: an object, white.
let c_white (g: heap)
  : Lemma (requires W.big_enough)
          (ensures Seq.mem (W.oC g) (objects zero_addr (g0 g)) /\ is_white (W.oC g) (g0 g) /\
                   is_black (W.oB g) (g0 g) /\ Seq.mem (W.oB g) (objects zero_addr (g0 g)))
  = W.w_ok g;
    V.marked_facts g;
    GcC.mark_ok (V.h g) (V.st g) (V.rs g);
    Corr.mark_post_elim_blue (V.h g) (V.hm g) (V.rs g) 0UL;
    let c = W.oC g in
    is_white_iff c (g0 g);
    is_black_iff c (g0 g);
    is_gray_iff c (g0 g);
    is_blue_iff c (g0 g)

/// **The start is a mid-sweep state**, where C is a dead object (not in
/// use, though an object) and B is in use.
let start_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures pages_ok_sw (g0 g) (s0 g) /\
                   SA.sweep_ready (g0 g) (s0 g) /\ SA.mark_done (g0 g) /\
                   Seq.mem (W.oC g) (objects zero_addr (g0 g)) /\ dead (g0 g) (s0 g).pm (W.oC g) /\
                   ~(in_use (free_sw (s0 g).pm) (g0 g) (W.oC g)) /\
                   in_use (free_sw (s0 g).pm) (g0 g) (W.oB g) /\
                   L.mem (W.oC g) (dead_list (g0 g) (s0 g).pm) /\
                   V.nontrivial g)
  = V.sweep_witness g;
    MS.sw_start (g0 g) (s0 g);
    c_white g;
    c_uw g;
    is_white_iff (W.oB g) (g0 g);
    is_black_iff (W.oB g) (g0 g);
    is_blue_iff (W.oB g) (g0 g);
    is_white_iff (W.oC g) (g0 g);
    is_blue_iff (W.oC g) (g0 g)

/// The hypotheses of the surrogate (`MidSweep.surrogate`, `alloc_relate`,
/// `alloc_facts`), of `Graft.alloc_agree` and of `NewOnly.alloc_new_only`
/// hold there, with a dead object scrubbed.
let surrogate_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures (let zs = dead_list (g0 g) (s0 g).pm in
                    let gk = Sc.scrub (g0 g) zs in
                    sctx (g0 g) (s0 g) zs /\ L.mem (W.oC g) zs /\
                    pages_ok gk (s0 g) /\ well_formed_heap gk /\
                    (forall (x: hp_addr). not (G.uw (s0 g).pm (U64.v x)) ==> read_word gk x == read_word (g0 g) x)))
  = start_witness g;
    let zs = dead_list (g0 g) (s0 g).pm in
    surrogate (g0 g) (s0 g) zs

/// ---------------------------------------------------------------------------
/// 1. C's page swept
/// ---------------------------------------------------------------------------

let g1 (g: heap{W.big_enough}) : GTot heap = fst (SA.step (g0 g) (s0 g) (jC g))
let s1 (g: heap{W.big_enough}) : GTot pstate = snd (SA.step (g0 g) (s0 g) (jC g))

/// A swept pool page with a free slot counts it.
#push-options "--fuel 1"
let nfree_pos (g': heap) (pm': page_map) (j: nat{j < n_pages}) (c: nat{c < n_cls}) (k: nat)
  : Lemma (requires pool_list_ok g' pm' j /\ (entry pm' j).kind == Pool c /\ (entry pm' j).swept /\
                    k < n_slots c /\ slot_free g' j c k)
          (ensures (entry pm' j).nfree > 0)
  = let e = entry pm' j in
    eliminate exists (ks: list nat).
      slot_chain g' j c e.free_head ks /\ L.noRepeats ks /\
      (forall (k2: nat). k2 < n_slots c ==> (L.mem k2 ks <==> slot_free g' j c k2)) /\
      e.nfree == L.length ks
    with (match ks with [] -> assert (L.mem k ks) | _ -> ())
#pop-options

/// Sweeping a pool page frees a slot whose block was not black: the page
/// keeps a free slot, or goes back as a free page.
#push-options "--z3rlimit 40"
let sweep_frees (gm: heap) (st: pstate) (j: nat{j < n_pages}) (c: nat{c < n_cls}) (k: nat) (x: obj_addr)
  : Lemma (requires Th.marked_pool_page gm st.pm j c /\ k < n_slots c /\ U64.v x == slot_obj j c k /\
                    ~(is_black x gm))
          (ensures (let (_, st') = SA.step gm st j in
                    (entry st'.pm j).kind == Free \/ has_free_slot st'.pm c j))
  = SP.sweep_page_correct ();
    let (g', e) = SP.sweep_page gm st.pm j in
    assert (Th.sweep_page_ok gm st.pm j c g' e);
    let st' = SST.push_avail st j e in
    assert (SA.step gm st j == (g', st'));
    SST.push_frame st j e;
    SST.push_entry st j e;
    assert ((entry st'.pm j).kind == e.kind /\ (entry st'.pm j).swept == e.swept /\
            (entry st'.pm j).nfree == e.nfree);
    hd_address_spec x;
    R.hdr_obj gm x;
    is_black_iff x gm;
    assert (~(slot_used gm j c k /\ color_at gm (slot_base j c k) == Black));
    let pm' = Seq.upd st.pm j e in
    if FStar.IndefiniteDescription.strong_excluded_middle
         (exists (k': nat). k' < n_slots c /\ slot_used gm j c k' /\ color_at gm (slot_base j c k') == Black)
    then nfree_pos g' pm' j c k
#pop-options

let kept_at (pm pm': page_map) (p k: nat) (i: nat{i < n_pages})
  : Lemma (requires MS.kinds_kept pm pm' p k /\ (i < p \/ i >= p + k))
          (ensures (entry pm' i).kind == (entry pm i).kind /\ (entry pm' i).swept == (entry pm i).swept)
  = ()

/// The step, over any heap with the facts it needs.
#push-options "--z3rlimit 40"
let step1_abs (gm: heap) (st: pstate) (j: nat{j < n_pages}) (k: nat) (x: obj_addr) (i: nat{i < n_pages}) (n: pos)
  : Lemma (requires pages_ok_sw gm st /\ (entry st.pm j).kind == Pool W.cA /\ not (entry st.pm j).swept /\
                    k < n_slots W.cA /\ U64.v x == slot_obj j W.cA k /\ ~(is_black x gm) /\
                    (entry st.pm i).kind == LargeHead n /\ not (entry st.pm i).swept)
          (ensures (let (g', st') = SA.step gm st j in
                    pages_ok_sw g' st' /\ (entry st'.pm j).swept /\
                    ((entry st'.pm j).kind == Free \/ has_free_slot st'.pm W.cA j) /\
                    i <> j /\ (entry st'.pm i).kind == LargeHead n /\ not (entry st'.pm i).swept))
  = let pm = st.pm in
    MS.step_sw gm st j;
    pages_ok_sw_elim gm st;
    assert (walk_page pm j /\ span pm j == 1);
    let (_, st') = SA.step gm st j in
    kept_at pm st'.pm j 1 i;
    assert (page_local gm pm j);
    assert (Th.marked_pool_page gm pm j W.cA);
    sweep_frees gm st j W.cA k x
#pop-options

/// The facts of the start the step needs.
let start_facts (g: heap)
  : Lemma (requires W.big_enough)
          (ensures pages_ok_sw (g0 g) (s0 g) /\ ~(is_black (W.oC g) (g0 g)) /\
                   jc_prop g (jC g) /\ W.i0 < n_pages /\
                   (entry (s0 g).pm W.i0).kind == LargeHead W.kL /\ not (entry (s0 g).pm W.i0).swept)
  = start_witness g;
    V.sweep_witness g;
    c_white g;
    is_white_iff (W.oC g) (g0 g);
    is_black_iff (W.oC g) (g0 g)

let step1_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures pages_ok_sw (g1 g) (s1 g) /\
                   (entry (s1 g).pm (jC g)).swept /\
                   ((entry (s1 g).pm (jC g)).kind == Free \/ has_free_slot (s1 g).pm W.cA (jC g)) /\
                   W.i0 < n_pages /\ W.i0 <> jC g /\
                   (entry (s1 g).pm W.i0).kind == LargeHead W.kL /\ not (entry (s1 g).pm W.i0).swept)
  = start_facts g;
    let j = jC g in
    eliminate exists (k: nat). k < n_slots W.cA /\ (entry (s0 g).pm j).kind == Pool W.cA /\
                          not (entry (s0 g).pm j).swept /\ U64.v (W.oC g) == slot_obj j W.cA k
    with step1_abs (g0 g) (s0 g) j k (W.oC g) W.i0 W.kL

/// ---------------------------------------------------------------------------
/// 2. An allocation, with C's page swept and B's run unswept
/// ---------------------------------------------------------------------------

let alloc1 (g: heap{W.big_enough}) : GTot (heap & pstate & U64.t) = PA.alloc I.Sweeping (g1 g) (s1 g) W.wzS
let ga (g: heap{W.big_enough}) : GTot heap = let (a, _, _) = alloc1 g in a
let oN (g: heap{W.big_enough}) : GTot U64.t = let (_, _, o) = alloc1 g in o

/// The caller clears the new object's field.
let g2 (g: heap{W.big_enough}) : GTot heap = GC.Spec.Pages.Blocks.zeros (ga g) (U64.v (oN g)) W.wzS
let s2 (g: heap{W.big_enough}) : GTot pstate = sw_alloc_state (g1 g) (s1 g) W.wzS

/// Clearing writes values that are not free under any definition.
let zeros_written (free: free_def) (g': heap) (x: obj_addr) (n: nat)
  : Lemma (requires U64.v (wosize_of_object x g') == n)
          (ensures I.fields_written_with free g' (GC.Spec.Pages.Blocks.zeros g' (U64.v x) n) x)
  = FStar.Classical.forall_intro (GC.Spec.Pages.Blocks.zeros_read g' (U64.v x) n)

/// The allocation, over any mid-sweep heap with a free page or a free slot
/// of A's class, and an unswept run.
#push-options "--z3rlimit 40"
let alloc_abs (gm: heap) (st: pstate) (j: nat{j < n_pages}) (i: nat{i < n_pages}) (n: pos)
  : Lemma (requires pages_ok_sw gm st /\
                    ((entry st.pm j).kind == Free \/ has_free_slot st.pm W.cA j) /\
                    (entry st.pm i).kind == LargeHead n /\ not (entry st.pm i).swept)
          (ensures (let (g', st', o) = PA.alloc I.Sweeping gm st W.wzS in
                    o =!= 0UL /\ U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                    (let x : obj_addr = o in
                     let g'' = GC.Spec.Pages.Blocks.zeros g' (U64.v x) W.wzS in
                     Seq.mem x (objects zero_addr g') /\ is_white x g' /\
                     not (unswept_at st.pm x) /\
                     in_use (free_sw st'.pm) g' x /\ ~(in_use (free_sw st.pm) gm x) /\
                     sw_allocated gm st W.wzS g'' /\
                     pages_ok_sw g'' st' /\
                     (entry st'.pm i).kind == LargeHead n /\ not (entry st'.pm i).swept)))
  = W.sizes ();
    cls_bounds 0;
    MA.alloc_sw_ok gm st W.wzS;
    let (g', st', o) = PA.alloc I.Sweeping gm st W.wzS in
    if o = 0UL then begin
      assert (Th.no_fit gm st (W.wzS + 1));
      assert (W.cA == class_of (W.wzS + 1))
    end
    else begin
      let x : obj_addr = o in
      zeros_written (free_sw st.pm) g' x W.wzS;
      assert (Th.unswept_unchanged gm g' st st')
    end
#pop-options

let alloc_witness (g: heap)
  : Lemma (requires W.big_enough)
          (ensures (let (g', st', o) = alloc1 g in
                    o =!= 0UL /\ U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                    Seq.mem (o <: obj_addr) (objects zero_addr g') /\ is_white (o <: obj_addr) g' /\
                    not (unswept_at (s1 g).pm (o <: obj_addr)) /\
                    in_use (free_sw st'.pm) g' (o <: obj_addr) /\
                    ~(in_use (free_sw (s1 g).pm) (g1 g) (o <: obj_addr)) /\
                    sw_allocated (g1 g) (s1 g) W.wzS (g2 g) /\
                    pages_ok_sw (g2 g) (s2 g) /\ W.i0 < n_pages /\
                    (entry (s2 g).pm W.i0).kind == LargeHead W.kL /\ not (entry (s2 g).pm W.i0).swept))
  = step1_witness g;
    alloc_abs (g1 g) (s1 g) (jC g) W.i0 W.kL

/// ---------------------------------------------------------------------------
/// 3. B's run swept, and 4. the rest
/// ---------------------------------------------------------------------------

let i0_ok (g: heap) : Lemma (requires W.big_enough) (ensures W.i0 < n_pages) = W.w_ok g

let g3 (g: heap{W.big_enough}) : GTot heap = i0_ok g; fst (SA.step (g2 g) (s2 g) W.i0)
let s3 (g: heap{W.big_enough}) : GTot pstate = i0_ok g; snd (SA.step (g2 g) (s2 g) W.i0)

/// **The run.**
let sw_witness (g: heap{W.big_enough}) : GTot (sw_run (g3 g) (s3 g)) =
  start_witness g;
  alloc_witness g;
  let r0 = SwStart (g0 g) (s0 g) () in
  let r1 : sw_run (g1 g) (s1 g) = SwStep r0 (jC g) in
  let r2 : sw_run (g2 g) (s2 g) = SwAlloc r1 W.wzS (g2 g) () in
  i0_ok g;
  SwStep r2 W.i0

/// **What the run shows**: every theorem of plan §20.4 has its hypotheses
/// met on it, with a pool page swept and a run unswept at the allocation,
/// which succeeds; B's run is swept by a later step; the rest of the sweep
/// ends in `Idle`, where every page is swept (`sw_end`'s hypotheses).
let sw_witness_ok (g: heap)
  : Lemma (requires W.big_enough)
          (ensures pages_ok_sw (g3 g) (s3 g) /\
                   (forall (j: nat{j < n_pages}). W.i0 <= j /\ j < W.i0 + W.kL ==> (entry (s3 g).pm j).swept) /\
                   (let (gf, sf) = SA.sweep_all (g3 g) (s3 g) in
                    pages_ok_sw gf sf /\ GC.Spec.Pages.MarkPhase.all_swept sf /\ PA.inv I.Idle gf sf))
  = alloc_witness g;
    MS.step_sw (g2 g) (s2 g) W.i0;
    pages_ok_sw_elim (g2 g) (s2 g);
    assert (run_ok (s2 g).pm W.i0);
    let r = sw_witness g in
    sw_run_ends r;
    pages_ok_sw_elim (g3 g) (s3 g);
    if n_pages > 0 then assert (cont_ok (s3 g).pm 0);
    MS.sweep_from_sw (g3 g) (s3 g) 0
