/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cycle.Vacuity - a whole page cycle, built
/// ---------------------------------------------------------------------------
///
/// The vacuity rule (plan §18): the theorems of `GC.Spec.Pages.Cycle` are
/// about runs of the page cycle, so they need a run, built, on which they
/// say something.  `run g` is one, from the shared witness state `W`
/// (`GC.Spec.Pages.Witness`: A in a pool page, its field pointing to B, B the
/// head of a run, C in A's pool page), with the roots `[C]`:
///
///   0. **Start** (`PStart`): the page `Idle` invariant, the nursery empty;
///      root darkening greys C.
///   1. **The hand-over**: mark moves -- start scanning C, scan its one
///      field (0, no pointer), blacken C -- leave nothing grey.
///   2. **The sweep starts** (`SStart`) at that heap, with every page that
///      is not free unswept.
///   3. **A's page is swept** (`SStep`): A is dead, so the page gets a free
///      slot or becomes free; B's run is still unswept.
///   4. **An allocation** (`SAlloc`) succeeds, in a swept page, and its field
///      is cleared: it is new.
///   5. **The rest of the sweep** (`SStep`s over every page), and **the end**
///      (`SEnd`).
///
/// It is not trivial (`run_nontrivial`): C is reachable when the cycle
/// starts; B is not, and is not handed out, so the run must free it; the
/// allocation is handed out; and the heap's last word lies in a block
/// unreachable at the start (the tail block, plan §23.5), so
/// `cycle_lossless` speaks of it.  `run_theorems` applies the theorems.
///
/// `run` has no barrier write, no allocation while marking and no write
/// mid-sweep.  `run_all` (the second half of this module) is a run from the
/// same start that has all three, with every hypothesis of every
/// constructor shown; it asks for one page more than `W` (`roomy`).

module GC.Spec.Pages.Cycle.Vacuity

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv
open GC.Spec.Pages.MidSweep

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module S = GC.Spec.MarkPhase.Slice
module HG = GC.Spec.HeapGraph
module MPC = GC.Spec.MarkPhase.Completeness
module GMC = GC.Gen.MarkPhase.Completeness
module GMM = GC.Gen.MarkPhase.Minor
module MStart = GC.Gen.MarkPhase.Start
module MB = GC.Impl.MarkBounded
module MBP = GC.Impl.MarkBoundedPrecondition
module GC_ = GC.Gen.Cycle
module SPC = GC.Spec.SweepPhase.Completeness
module LL = GC.Spec.FusedSweep.Lossless
module W = GC.Spec.Walk
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module PMP = GC.Spec.Pages.MarkPhase
module SA = GC.Spec.Pages.SweepAll
module SS = GC.Spec.Pages.StartSweep
module MS2 = GC.Spec.Pages.MidSweepStep
module MA = GC.Spec.Pages.MidSweepAlloc
module MR = GC.Spec.Pages.MidSweepRun
module Wt = GC.Spec.Pages.Witness
module MSV = GC.Spec.Pages.MidSweepVacuity
module St = GC.Spec.Pages.Step
module TW = GC.Spec.Pages.TailWalk
module CS = GC.Spec.Pages.Cycle.State
module PM = GC.Spec.Pages.Cycle.Mark
module PS = GC.Spec.Pages.Cycle.Sweep
module PC = GC.Spec.Pages.Cycle
module AP = GC.Spec.Pages.AllocPhase
module A = GC.Spec.Pages.Alloc
module F = GC.Spec.Pages.Fill
module B = GC.Spec.Pages.Blocks
module MPA = GC.Spec.MarkPhase.Alloc
module MC = GC.Gen.MarkPhase.Cycle
module GB = GC.Gen.Barrier
module GI = GC.Gen.Incremental
module Ph = GC.Spec.Phase
module SPM = GC.Spec.SweepPhase.Mutator

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The nursery, empty
/// ---------------------------------------------------------------------------

let m_any : minor_state = { data = Seq.create minor_heap_size 0uy; bump = 0UL }

let m0 : minor_state = minor_reset m_any

let m0_reset () : Lemma (minor_reset m0 == m0)
  = let r = minor_reset m0 in
    U64.v_inj r.bump m0.bump;
    assert (r.data == m0.data);
    assert (r == { data = r.data; bump = r.bump });
    assert (m0 == { data = m0.data; bump = m0.bump })

let m0_empty (h: heap) (w: obj_addr) : Lemma (~(GMM.nursery_refs m0 h w))
  = GMM.nursery_refs_reset m_any h w

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

let h (g: heap) : GTot heap = Wt.w_heap g
let st (g: heap) : GTot pstate = Wt.w_state g
let oa (g: heap) : GTot obj_addr = Wt.oA g
let ob (g: heap) : GTot obj_addr = Wt.oB g
let oc (g: heap) : GTot obj_addr = Wt.oC g

/// The roots: C.
let rs (g: heap) : GTot (seq U64.t) = Seq.create 1 (oc g <: U64.t)

/// What `W` gives.
let base (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures PA.inv I.Idle (h g) (st g) /\
                   oc g <> oa g /\ oc g <> ob g /\ oa g <> ob g /\
                   Wt.holds (h g) (oa g) Wt.wzS (Wt.const (ob g)) /\
                   Wt.holds (h g) (ob g) Wt.wzL (Wt.const 0UL) /\
                   Wt.holds (h g) (oc g) Wt.wzS (Wt.const 0UL) /\
                   U64.v (wosize_of_object (oc g) (h g)) == 1 /\ is_white (oc g) (h g) /\
                   ~(is_blue (oc g) (h g)) /\ ~(is_infix (oc g) (h g)) /\ ~(is_no_scan (oc g) (h g)) /\
                   is_white (oa g) (h g) /\ ~(is_blue (ob g) (h g)) /\
                   read_word (h g) (oc g) == 0UL)
  = Wt.step3 g;
    Wt.holds_facts (h g) (oa g) Wt.wzS (Wt.const (ob g));
    Wt.holds_facts (h g) (ob g) Wt.wzL (Wt.const 0UL);
    Wt.holds_facts (h g) (oc g) Wt.wzS (Wt.const 0UL)

/// C is a root that names itself.
let c_root (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures MBP.root_valid_for_darkening (h g) (oc g <: U64.t) /\ is_pointer (oc g <: U64.t) /\
                   resolve_object (oc g) (h g) == oc g /\ U64.v (oc g) >= U64.v zero_addr + 8 /\
                   Seq.index (rs g) 0 == (oc g <: U64.t) /\ Seq.length (rs g) == 1)
  = base g;
    let c = oc g in
    W.objects_mem_iff (h g) zero_addr c;
    resolve_non_infix c (h g);
    is_val_addr_spec (c <: U64.t)

/// The start's precondition.
let start_pre (g: heap)
  : Lemma (requires Wt.big_enough) (ensures PM.pstart_pre m0 (h g) (st g) (rs g))
  = base g;
    c_root g;
    m0_reset ()

/// Root darkening greys C, and only C.
let gd (g: heap) : GTot heap = makeGray (oc g) (h g)

#push-options "--fuel 1 --z3rlimit 30"
let darkened_c (g: heap)
  : Lemma (requires Wt.big_enough) (ensures MStart.darkened (h g) (rs g) == gd g)
  = let c = oc g in
    let r = rs g in
    let h0 = h g in
    base g;
    c_root g;
    MB.darken_roots_bounded_prefix_step h0 Seq.empty r 0 2;
    assert (MB.darken_roots_bounded_prefix_spec h0 Seq.empty r 0 2 == (h0, Seq.empty));
    hd_address_spec c;
    hd_address_bounds c;
    f_hd_roundtrip c;
    assert (U64.sub c mword == hd_address c)
#pop-options

/// ---------------------------------------------------------------------------
/// The mark moves
/// ---------------------------------------------------------------------------

let gm (g: heap) : GTot heap = makeBlack (oc g) (gd g)

let sp1 (g: heap) : GTot MP.scan_pos = { MP.cur = (oc g <: U64.t); MP.fld = 1 }
let sp2 (g: heap) : GTot MP.scan_pos = { MP.cur = (oc g <: U64.t); MP.fld = 2 }

/// C in the darkened heap: a grey block with one field, 0.
#push-options "--z3rlimit 30"
let gd_facts (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures objects zero_addr (gd g) == objects zero_addr (h g) /\
                   Seq.mem (oc g) (objects zero_addr (gd g)) /\ is_gray (oc g) (gd g) /\
                   ~(is_no_scan (oc g) (gd g)) /\ U64.v (wosize_of_object (oc g) (gd g)) == 1 /\
                   HG.get_field (gd g) (oc g) 1UL == 0UL)
  = let c = oc g in
    let h0 = h g in
    base g;
    makeGray_eq c h0;
    color_change_preserves_objects h0 c Header.Gray;
    makeGray_is_gray c h0;
    color_preserves_is_no_scan c h0 Header.Gray;
    wosize_of_object_spec c h0;
    wosize_of_object_spec c (gd g);
    hd_address_spec c;
    set_object_color_read_word c (hd_address c) h0 Header.Gray;
    set_object_color_read_word c (c <: hp_addr) h0 Header.Gray;
    assert (Seq.mem c (objects zero_addr h0))
#pop-options

let not_pointer_zero () : Lemma (~(is_pointer 0UL)) = ()

let move1 (g: heap)
  : Lemma (requires Wt.big_enough) (ensures S.mark_move (gd g) MP.scan_none (gd g) (sp1 g))
  = gd_facts g;
    FStar.Classical.exists_intro
      (fun (x: obj_addr) -> MP.scan_none.MP.cur == 0UL /\ S.scan_target (gd g) x /\
                         gd g == gd g /\ sp1 g == { MP.cur = x; MP.fld = 1 })
      (oc g)

let move2 (g: heap)
  : Lemma (requires Wt.big_enough) (ensures S.mark_move (gd g) (sp1 g) (gd g) (sp2 g))
  = gd_facts g;
    not_pointer_zero ();
    assert (S.scan_field (gd g) (oc g) (U64.uint_to_t 1) == gd g);
    FStar.Classical.exists_intro
      (fun (x: obj_addr) ->
         x == (sp1 g).MP.cur /\ S.scan_target (gd g) x /\ 1 <= (sp1 g).MP.fld /\
         (sp1 g).MP.fld <= U64.v (wosize_of_object x (gd g)) /\
         gd g == S.scan_field (gd g) x (U64.uint_to_t (sp1 g).MP.fld) /\
         sp2 g == { sp1 g with MP.fld = (sp1 g).MP.fld + 1 })
      (oc g)

let move3 (g: heap)
  : Lemma (requires Wt.big_enough) (ensures S.mark_move (gd g) (sp2 g) (gm g) MP.scan_none)
  = gd_facts g;
    FStar.Classical.exists_intro
      (fun (x: obj_addr) ->
         Seq.mem x (objects zero_addr (gd g)) /\ is_gray x (gd g) /\ MP.all_scanned (gd g) (sp2 g) x /\
         gm g == makeBlack x (gd g) /\ MP.scan_none == MP.blackened_pos (sp2 g) x)
      (oc g)

let marks (g: heap)
  : Lemma (requires Wt.big_enough) (ensures S.mark_steps (gd g) MP.scan_none (gm g) MP.scan_none)
  = move1 g; move2 g; move3 g;
    S.mark_steps_move (gd g) (gd g) MP.scan_none (sp1 g);
    S.mark_steps_snoc (gd g) (gd g) (gd g) MP.scan_none (sp1 g) (sp2 g);
    S.mark_steps_snoc (gd g) (gd g) (gm g) MP.scan_none (sp2 g) MP.scan_none

/// Every header but C's is the start heap's.
#push-options "--z3rlimit 30"
let gm_other (g: heap) (x: obj_addr)
  : Lemma (requires Wt.big_enough /\ x <> oc g)
          (ensures read_word (gm g) (hd_address x) == read_word (h g) (hd_address x))
  = let c = oc g in
    hd_address_spec x; hd_address_spec c;
    makeBlack_eq c (gd g);
    makeGray_eq c (h g);
    set_object_color_read_word c (hd_address x) (h g) Header.Gray;
    set_object_color_read_word c (hd_address x) (gd g) Header.Black
#pop-options

/// Nothing is grey after the moves: C is black, every other block has its
/// colour at the start, where nothing is grey.
#push-options "--z3rlimit 30"
let gm_no_grey (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures Mark.noGreyObjects (gm g) /\ objects zero_addr (gm g) == objects zero_addr (h g) /\
                   is_black (oc g) (gm g))
  = let c = oc g in
    base g;
    gd_facts g;
    makeBlack_eq c (gd g);
    color_change_preserves_objects (gd g) c Header.Black;
    makeBlack_is_black c (gd g);
    PM.idle_facts (h g) (st g);
    let one (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr (gm g))) (ensures ~(is_gray x (gm g)))
      = if x = c then Mark.colors_exclusive c (gm g)
        else begin
          gm_other g x;
          color_of_header_eq x (h g) (gm g);
          is_gray_iff x (h g); is_gray_iff x (gm g)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

/// The collector's state at the darkened heap.
#push-options "--z3rlimit 30"
let gd_ok (g: heap)
  : Lemma (requires Wt.big_enough) (ensures PM.pmark_ok m0 (gd g) (st g) MP.scan_none)
  = start_pre g;
    darkened_c g;
    PM.start_facts m0 (h g) (st g) (rs g);
    MP.no_black_tri_color (gd g);
    FStar.Classical.forall_intro_2 m0_empty;
    MP.marking_inv_start (gd g) (GMM.nursery_refs m0 (gd g))
#pop-options

/// The hand-over's hypotheses.
let handover_ok (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures PM.pmark_ok m0 (MStart.darkened (h g) (rs g)) (st g) MP.scan_none /\
                   S.mark_steps (MStart.darkened (h g) (rs g)) MP.scan_none (gm g) MP.scan_none /\
                   Mark.noGreyObjects (gm g) /\
                   SA.sweep_ready (gm g) (SS.start_sweep (st g)) /\ SA.mark_done (gm g))
  = darkened_c g;
    gd_ok g;
    marks g;
    gm_no_grey g;
    CS.mark_steps_inv (st g) (gd g) MP.scan_none (gm g) MP.scan_none;
    FStar.Classical.forall_intro_2 m0_empty;
    S.mark_steps_inv (gd g) (gm g) MP.scan_none MP.scan_none (GMM.nursery_refs m0 (gd g));
    CS.handover_ready (gm g) (st g) (GMM.nursery_refs m0 (gd g)) MP.scan_none

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

let s0 (g: heap) : GTot pstate = SS.start_sweep (st g)

/// A's page and slot, and B's run, at the sweep's start: unswept.
let ia (g: heap{Wt.big_enough}) : GTot (i: nat{i < n_pages}) =
  Wt.step3 g; Wt.first_free (Wt.s1 g)

let i0 (g: heap{Wt.big_enough}) : GTot (i: nat{i < n_pages}) = MSV.i0_ok g; Wt.i0

let a_prop (g: heap{Wt.big_enough}) (k: nat) : prop =
  k < n_slots Wt.cA /\ U64.v (oa g) == slot_obj (ia g) Wt.cA k

let at_start (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures (i0 g) + Wt.kL <= n_pages /\
                   (entry (s0 g).pm (ia g)).kind == Pool Wt.cA /\ not (entry (s0 g).pm (ia g)).swept /\
                   (entry (s0 g).pm (i0 g)).kind == LargeHead Wt.kL /\ not (entry (s0 g).pm (i0 g)).swept /\
                   U64.v (ob g) - 8 == page_base (i0 g) /\
                   (exists (k: nat). a_prop g k))
  = Wt.step3 g;
    FStar.Classical.forall_intro (SS.clear_entry (st g).pm)

let ka (g: heap{Wt.big_enough}) : GTot (k: nat{a_prop g k}) =
  at_start g;
  FStar.IndefiniteDescription.indefinite_description_ghost nat (fun k -> a_prop g k)

/// A is not black at the hand-over.
let a_white (g: heap)
  : Lemma (requires Wt.big_enough) (ensures ~(is_black (oa g) (gm g)))
  = base g;
    gm_other g (oa g);
    color_of_header_eq (oa g) (h g) (gm g);
    Mark.colors_exclusive (oa g) (h g);
    is_black_iff (oa g) (h g); is_black_iff (oa g) (gm g)

/// 3. A's page swept.
let g1 (g: heap{Wt.big_enough}) : GTot heap = at_start g; fst (SA.step (gm g) (s0 g) (ia g))
let s1 (g: heap{Wt.big_enough}) : GTot pstate = at_start g; snd (SA.step (gm g) (s0 g) (ia g))

let step1 (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures pages_ok_sw (gm g) (s0 g) /\
                   pages_ok_sw (g1 g) (s1 g) /\
                   ((entry (s1 g).pm (ia g)).kind == Free \/ has_free_slot (s1 g).pm Wt.cA (ia g)) /\
                   (entry (s1 g).pm (i0 g)).kind == LargeHead Wt.kL /\ not (entry (s1 g).pm (i0 g)).swept)
  = handover_ok g;
    MS2.sw_start (gm g) (s0 g);
    at_start g;
    a_white g;
    MSV.step1_abs (gm g) (s0 g) (ia g) (ka g) (oa g) (i0 g) Wt.kL

/// 4. An allocation, its field cleared.
let alloc1 (g: heap{Wt.big_enough}) : GTot (heap & pstate & U64.t) = PA.alloc I.Sweeping (g1 g) (s1 g) Wt.wzS
let ga (g: heap{Wt.big_enough}) : GTot heap = let (a, _, _) = alloc1 g in a
let s2 (g: heap{Wt.big_enough}) : GTot pstate = let (_, s, _) = alloc1 g in s
let on (g: heap{Wt.big_enough}) : GTot obj_addr = Wt.as_obj (let (_, _, o) = alloc1 g in o)
let g2 (g: heap{Wt.big_enough}) : GTot heap = GC.Spec.Pages.Blocks.zeros (ga g) (U64.v (on g)) Wt.wzS

#push-options "--z3rlimit 30"
let alloc_ok (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures alloc1 g == (ga g, s2 g, (on g <: U64.t)) /\
                   I.fields_written_with (free_sw (s1 g).pm) (ga g) (g2 g) (on g) /\
                   pages_ok_sw (g2 g) (s2 g) /\
                   not (unswept_at (s1 g).pm (on g)) /\
                   (entry (s2 g).pm (i0 g)).kind == LargeHead Wt.kL /\ not (entry (s2 g).pm (i0 g)).swept)
  = step1 g;
    at_start g;
    MSV.alloc_abs (g1 g) (s1 g) (ia g) (i0 g) Wt.kL
#pop-options

/// 5. The rest of the sweep: a step at every unit, from page `p` on.
#push-options "--fuel 1 --ifuel 1"
let rec rest (#g0 #g: heap) (#s: pstate) (#since: obj_addr -> prop)
             (r: PS.psweep g0 g s I.Sweeping since) (p: nat)
  : Ghost (PS.psweep g0 (fst (SA.sweep_from g s p)) (snd (SA.sweep_from g s p)) I.Sweeping since)
          (requires pages_ok_sw g s)
          (ensures fun r' -> PC.sweep_start_st r' == PC.sweep_start_st r)
          (decreases (if p < n_pages then n_pages - p else 0))
  = if p >= n_pages then r
    else begin
      MS2.step_sw g s p;
      let k = span s.pm p in
      rest (PS.SStep r p ()) (p + k)
    end
#pop-options

let gf (g: heap{Wt.big_enough}) : GTot heap = fst (SA.sweep_from (g2 g) (s2 g) 0)
let sf (g: heap{Wt.big_enough}) : GTot pstate = snd (SA.sweep_from (g2 g) (s2 g) 0)

let rest_ends (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures pages_ok_sw (gf g) (sf g) /\ PMP.all_swept (sf g))
  = alloc_ok g;
    pages_ok_sw_elim (g2 g) (s2 g);
    if n_pages > 0 then assert (cont_ok (s2 g).pm 0);
    MS2.sweep_from_sw (g2 g) (s2 g) 0

/// The addresses the run hands out: the allocation.
let since (g: heap{Wt.big_enough}) : obj_addr -> prop =
  GC_.union SPC.nothing_new (SPC.with_new SPC.nothing_new (on g <: U64.t))

/// **The run.**
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let run (g: heap{Wt.big_enough}) : GTot (PC.pcycle (h g) (rs g) (gf g) (sf g) I.Idle (since g)) =
  start_pre g;
  handover_ok g;
  step1 g;
  alloc_ok g;
  rest_ends g;
  let rm : PM.pmarking (h g) (rs g) (MStart.darkened (h g) (rs g)) (st g) MP.scan_none SPC.nothing_new =
    PM.PStart m0 (st g) () in
  let r0 : PS.psweep (gm g) (gm g) (s0 g) I.Sweeping SPC.nothing_new = PS.SStart (s0 g) () in
  at_start g;
  let r1 : PS.psweep (gm g) (g1 g) (s1 g) I.Sweeping SPC.nothing_new = PS.SStep r0 (ia g) () in
  let r2 : PS.psweep (gm g) (g2 g) (s2 g) I.Sweeping (SPC.with_new SPC.nothing_new (on g <: U64.t)) =
    PS.SAlloc r1 Wt.wzS (ga g) (s2 g) (on g) () (g2 g) () in
  let r3 = rest r2 0 in
  let r4 : PS.psweep (gm g) (gf g) (sf g) I.Idle (SPC.with_new SPC.nothing_new (on g <: U64.t)) =
    PS.SEnd r3 () in
  assert (PC.sweep_start_st r0 == s0 g);
  assert (PC.sweep_start_st r1 == PC.sweep_start_st r0);
  assert (PC.sweep_start_st r2 == PC.sweep_start_st r1);
  assert (PC.sweep_start_st r4 == PC.sweep_start_st r3);
  PC.PSweep rm m0 (gm g) MP.scan_none () r4 ()
#pop-options

/// ---------------------------------------------------------------------------
/// It is not trivial
/// ---------------------------------------------------------------------------

/// An object with one field, 0, points nowhere.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let one_zero_field (h0: heap) (c w: obj_addr)
  : Lemma (requires wosize_of_object c h0 == 1UL /\ read_word h0 (c <: hp_addr) == 0UL)
          (ensures ~(points_to h0 c w))
  = assert (U64.mul_mod 0UL mword == 0UL);
    assert (U64.add_mod c 0UL == c);
    assert (points_to h0 c w == exists_field_pointing_to_unchecked h0 c 1UL w);
    assert (~(is_pointer_to 0UL w))
#pop-options

/// The roots name only C, and C's field is no pointer: what is reachable
/// at the start is C alone.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let only_c (g: heap) (x: obj_addr)
  : Lemma (requires Wt.big_enough /\ GMC.reachable_at_start (h g) (rs g) x) (ensures x == oc g)
  = let c = oc g in
    let h0 = h g in
    base g;
    c_root g;
    GMC.reachable_at_start_eq h0 (rs g);
    let root (r: obj_addr) : Lemma (requires GMM.root_refs h0 (rs g) r) (ensures r == c)
      = eliminate exists (q: U64.t). Seq.mem q (rs g) /\ is_pointer q /\ resolve_object (q <: obj_addr) h0 == r
        with begin
          let _ = FStar.Seq.Properties.index_mem q (rs g) in
          ()
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires root);
    let edge (u v: obj_addr) : Lemma (requires u == c /\ MP.field_edge h0 u v) (ensures v == c)
      = eliminate exists (w: obj_addr). points_to h0 u w /\ resolve_object w h0 == v
        with begin
          wosize_of_object_bound c h0;
          assert (wosize_of_object c h0 == 1UL);
          assert (read_word h0 (c <: hp_addr) == 0UL);
          one_zero_field h0 c w
        end
    in
    FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (edge u));
    MPC.reachable_closed h0 (GMM.root_refs h0 (rs g)) (fun v -> v == c) x
#pop-options

/// B lies in its run, unswept when the allocation is made, which is in a
/// swept page: B is not the new object.
let b_not_new (g: heap)
  : Lemma (requires Wt.big_enough) (ensures ob g <> on g)
  = alloc_ok g;
    at_start g;
    page_base_mono (i0 g) ((i0 g) + 1);
    FStar.Math.Lemmas.distributivity_add_left (i0 g) 1 page_bytes;
    page_uw (s1 g).pm (i0 g) (U64.v (ob g) - 8);
    step1 g

/// The tail block is an object of the start heap, free, and over the heap's
/// last word.
let tail_start (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures pages_end + 16 <= heap_size /\ (pages_end + 8) % 8 == 0 /\
                   (let t : obj_addr = mk_hp_addr (pages_end + 8) in
                    Seq.mem t (objects zero_addr (h g)) /\ is_blue t (h g) /\
                    LL.in_extent (h g) t (heap_size - 8)))
  = base g;
    TW.tail_room ();
    FStar.Math.Lemmas.lemma_mod_plus pages_end 1 8;
    St.pages_ok_elim (h g) (st g);
    TW.tail_object (h g) (st g).pm

/// **The run is not trivial**: C is reachable when the cycle starts; B is
/// not, and the run does not hand it out; the run hands out the allocation;
/// the heap's last word lies in a block unreachable at the start.
let run_nontrivial (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures GMC.reachable_at_start (h g) (rs g) (oc g) /\
                   Seq.mem (ob g) (objects zero_addr (h g)) /\ ~(is_blue (ob g) (h g)) /\
                   ~(GMC.reachable_at_start (h g) (rs g) (ob g)) /\ ~(since g (ob g)) /\
                   since g (on g) /\
                   GC_.unreachable_covered (h g) (rs g) (heap_size - 8))
  = base g;
    c_root g;
    Wt.step3 g;
    GMC.reachable_at_start_eq (h g) (rs g);
    let _ = FStar.Seq.Properties.mem_index (oc g <: U64.t) (rs g) in
    assert (GMM.root_refs (h g) (rs g) (oc g));
    MPC.reachable_outside_refs (h g) (GMM.root_refs (h g) (rs g)) (oc g);
    FStar.Classical.move_requires (only_c g) (ob g);
    b_not_new g;
    tail_start g;
    TW.tail_room ();
    let t : obj_addr = mk_hp_addr (pages_end + 8) in
    Wt.holds_facts (h g) (oc g) Wt.wzS (Wt.const 0UL);
    FStar.Classical.move_requires (only_c g) t;
    assert (~(GMC.reachable_at_start (h g) (rs g) t))

/// **The theorems on it**: C survives; B is freed; the heap's last word is
/// free or in the new object at the end.
let run_theorems (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures Seq.mem (oc g) (objects zero_addr (gf g)) /\ ~(is_blue (oc g) (gf g)) /\
                   SPC.freed (gf g) (ob g) /\
                   (LL.blue_covered (gf g) (heap_size - 8) \/ SPC.new_covered (since g) (gf g) (heap_size - 8)))
  = run_nontrivial g;
    let r = run g in
    PC.cycle_survives r;
    PC.cycle_frees_unreachable r;
    PC.cycle_lossless r

/// ===========================================================================
/// A run with every event: a barrier write and an allocation while marking,
/// a program write mid-sweep
/// ===========================================================================
///
/// `run_all g` is a second run from the same start, which also has the
/// events `run` lacks:
///
///   0. **Start** (`PStart`) and 1. **a mark slice** (`PSlice`): the moves
///      of `run` (C scanned and blackened), nothing grey after them;
///   2. **An allocation while marking** (`PAlloc`): N, one field, black,
///      handed out from a free page or a free slot; its initialising write
///      (`MC.Init_write`) stores 0;
///   3. **A barrier write** (`PWrite`): N's field gets a pointer to C (the
///      barrier darkens the old value, 0, which is no pointer);
///   4. **The hand-over** at that heap (no further moves); 5. **the sweep
///      starts**; 6. **A's page is swept**; 7. **an allocation**, its field
///      cleared;
///   8. **A program write mid-sweep** (`SWrite`): the new object's field
///      gets 1 (an OCaml integer);
///   9. **the rest of the sweep** and **the end**.
///
/// An allocation while marking needs a free page or a free slot of its
/// class in the start state.  With abstract size classes a pool page may
/// hold one slot, so `W`'s room (B's run and two pages) may leave neither;
/// `roomy` asks for one page more.  `run` keeps the weaker hypothesis.

/// One page more than `W` asks for.
let roomy : prop = Wt.kL + 3 <= n_pages

/// ---------------------------------------------------------------------------
/// A free page at the start
/// ---------------------------------------------------------------------------

/// Three pages outside B's run.
let out_page (k: nat{k < 3}) : nat = if k < Wt.i0 then k else Wt.kL + k

let out_facts (g: heap) (k: nat{k < 3})
  : Lemma (requires roomy)
          (ensures out_page k < n_pages /\ (out_page k < Wt.i0 \/ out_page k >= Wt.i0 + Wt.kL))
  = Wt.step1 g

/// A page outside B's run that neither A's nor C's allocation took is free.
#push-options "--z3rlimit 40"
let w_kinds (g: heap) (j: nat{j < n_pages})
  : Lemma (requires roomy /\ (j < Wt.i0 \/ j >= Wt.i0 + Wt.kL) /\ j <> Wt.first_free (Wt.s1 g) /\
                    j <> Wt.first_free (Wt.s2 g))
          (ensures Wt.kind_of (st g) j == Free)
  = Wt.step1 g;
    Wt.step2 g;
    Wt.step3 g;
    Wt.sizes ();
    Wt.alloc_small_is (Wt.g2 g) (Wt.s2 g) Wt.wzS;
    Wt.small_kinds false (Wt.g2 g) (Wt.s2 g) Wt.wzS
#pop-options

let w_free (g: heap)
  : Lemma (requires roomy) (ensures exists (j: nat{j < n_pages}). Wt.kind_of (st g) j == Free)
  = let a = Wt.first_free (Wt.s1 g) in
    let b = Wt.first_free (Wt.s2 g) in
    out_facts g 0; out_facts g 1; out_facts g 2;
    let pick (k: nat{k < 3})
      : Lemma (requires out_page k <> a /\ out_page k <> b)
              (ensures exists (j: nat{j < n_pages}). Wt.kind_of (st g) j == Free)
      = out_facts g k;
        w_kinds g (out_page k)
    in
    if out_page 0 <> a && out_page 0 <> b then pick 0
    else if out_page 1 <> a && out_page 1 <> b then pick 1
    else pick 2

/// ---------------------------------------------------------------------------
/// An allocation while marking
/// ---------------------------------------------------------------------------

/// A new object's header, recoloured black: tag 0.
let new_hdr (ga: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr ga) /\ read_word ga (hd_address x) == B.ohdr Wt.wzS)
          (ensures (let gc = set_object_color x ga Header.Black in
                    ~(is_closure x gc) /\ ~(is_no_scan x gc) /\ ~(is_infix x gc)))
  = let gc = set_object_color x ga Header.Black in
    Wt.holds_facts ga x Wt.wzS (fun b -> read_word ga b);
    color_preserves_tag x ga Header.Black;
    color_preserves_is_no_scan x ga Header.Black;
    is_infix_spec x ga; is_infix_spec x gc;
    is_closure_spec x ga; is_closure_spec x gc

/// An allocation at `Marking` with a free page succeeds; the new object is
/// black, of one field, neither a closure nor no-scan; no page that is not
/// free changes kind.
#push-options "--z3rlimit 40"
let malloc_ok (gx: heap) (stx: pstate) (j: nat{j < n_pages})
  : Lemma (requires PMP.mark_inv gx stx /\ Wt.kind_of stx j == Free)
          (ensures (let (gb, sb, o) = PA.alloc I.Marking gx stx Wt.wzS in
                    o =!= 0UL /\ U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                    (let x : obj_addr = o in
                     Seq.mem x (objects zero_addr gb) /\ is_black x gb /\
                     U64.v (wosize_of_object x gb) == 1 /\
                     ~(is_closure x gb) /\ ~(is_no_scan x gb) /\ ~(is_infix x gb)) /\
                    (forall (i: nat{i < n_pages}). Wt.kind_of stx i =!= Free ==> Wt.kind_of sb i == Wt.kind_of stx i)))
  = Wt.sizes ();
    PMP.mark_inv_alloc gx stx Wt.wzS;
    CS.mark_alloc_facts gx stx Wt.wzS;
    assert (PA.alloc I.Marking gx stx Wt.wzS == AP.alloc_col Header.Black gx stx Wt.wzS);
    eliminate exists (ys: list obj_addr). GC.Spec.Pages.ColourFacts.live_list gx ys /\
                                       pages_ok (GC.Spec.Pages.Recolour.whiten gx ys) stx
    with begin
      AP.base gx ys stx Wt.wzS;
      let gw = GC.Spec.Pages.Recolour.whiten gx ys in
      AP.mc_of_ok gw stx;
      AP.alloc_col_white gw stx Wt.wzS;
      Wt.alloc_small_is gw stx Wt.wzS;
      Wt.small_kinds false gw stx Wt.wzS;
      Wt.alloc_fresh gw stx Wt.wzS;
      let (ga, sa, o) = A.alloc gx stx Wt.wzS in
      assert (A.alloc gw stx Wt.wzS == (GC.Spec.Pages.Recolour.whiten ga ys, sa, o));
      if o <> 0UL then begin
        AP.new_facts gx ys stx Wt.wzS Header.Black;
        let x : obj_addr = o in
        hd_address_spec x;
        assert (read_word ga (hd_address x) == B.ohdr Wt.wzS);
        new_hdr ga x
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Writing the one field of an object
/// ---------------------------------------------------------------------------

/// A word of the body of a one-field object is its field.
let body_one (x: obj_addr) (a: hp_addr)
  : Lemma (requires U64.v x <= U64.v a /\ U64.v a < U64.v x + 1 * 8) (ensures a == (x <: hp_addr))
  = U64.v_inj a x

/// Writing the one field of `x` keeps every other word, the objects, and
/// every header.
#push-options "--z3rlimit 30"
let write_one (g: heap) (x: obj_addr) (v: U64.t)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ U64.v (wosize_of_object x g) == 1)
          (ensures (let g' = write_word g (x <: hp_addr) v in
                    F.fctx g g' x /\ SPM.in_body g x (x <: hp_addr) /\
                    read_word g' (x <: hp_addr) == v /\
                    (forall (a: hp_addr). a =!= (x <: hp_addr) ==> read_word g' a == read_word g a) /\
                    (forall (y: obj_addr). (Seq.mem y (objects zero_addr g') <==> Seq.mem y (objects zero_addr g)) /\
                       (Seq.mem y (objects zero_addr g) ==> read_word g' (hd_address y) == read_word g (hd_address y)))))
  = let g' = write_word g (x <: hp_addr) v in
    read_write_same g (x <: hp_addr) v;
    let other (a: hp_addr) : Lemma (a =!= (x <: hp_addr) ==> read_word g' a == read_word g a)
      = if a <> (x <: hp_addr) then read_write_different g (x <: hp_addr) a v
    in
    FStar.Classical.forall_intro other;
    let out (a: hp_addr)
      : Lemma (U64.v a < U64.v x \/ U64.v a >= F.fields_end g x ==> read_word g' a == read_word g a)
      = other a
    in
    FStar.Classical.forall_intro out;
    assert (F.fctx g g' x);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (F.obj_same g g' x))
#pop-options

/// Two heaps that agree on the header of `y`.
let same_hdr (g g': heap) (y: obj_addr)
  : Lemma (requires read_word g' (hd_address y) == read_word g (hd_address y))
          (ensures (is_black y g' <==> is_black y g) /\ (is_white y g' <==> is_white y g) /\
                   (is_gray y g' <==> is_gray y g) /\ (is_blue y g' <==> is_blue y g) /\
                   is_no_scan y g' == is_no_scan y g /\ is_closure y g' == is_closure y g /\
                   is_infix y g' == is_infix y g /\
                   wosize_of_object y g' == wosize_of_object y g)
  = MM.header_kept_facts g g' y;
    tag_of_object_spec y g;
    tag_of_object_spec y g';
    is_infix_spec y g;
    is_infix_spec y g'

/// ---------------------------------------------------------------------------
/// The marking side
/// ---------------------------------------------------------------------------

/// The collector's state after the slice.
let gm_ok (g: heap)
  : Lemma (requires Wt.big_enough) (ensures PM.pmark_ok m0 (gm g) (st g) MP.scan_none)
  = handover_ok g;
    CS.mark_steps_inv (st g) (MStart.darkened (h g) (rs g)) MP.scan_none (gm g) MP.scan_none;
    FStar.Classical.forall_intro_2 m0_empty;
    S.mark_steps_inv (MStart.darkened (h g) (rs g)) (gm g) MP.scan_none MP.scan_none
      (GMM.nursery_refs m0 (MStart.darkened (h g) (rs g)))

/// A free page at the start, chosen.
let jf (g: heap{roomy}) : GTot (j: nat{j < n_pages /\ Wt.kind_of (st g) j == Free}) =
  w_free g;
  FStar.IndefiniteDescription.indefinite_description_ghost (j: nat{j < n_pages})
    (fun j -> Wt.kind_of (st g) j == Free)

/// 2. The allocation while marking, and its initialising write.
let mal (g: heap) : GTot (heap & pstate & U64.t) = PA.alloc I.Marking (gm g) (st g) Wt.wzS
let gb (g: heap) : GTot heap = let (a, _, _) = mal g in a
let sb (g: heap) : GTot pstate = let (_, s, _) = mal g in s
let n1 (g: heap) : GTot obj_addr = Wt.as_obj (let (_, _, o) = mal g in o)
let gz (g: heap) : GTot heap = write_word (gb g) (n1 g <: hp_addr) 0UL

/// C at the end of marking: a black object of one field, at its address.
#push-options "--z3rlimit 30"
let c_gm (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures Seq.mem (oc g) (objects zero_addr (gm g)) /\ is_black (oc g) (gm g) /\
                   ~(is_infix (oc g) (gm g)) /\ ~(is_closure (oc g) (gm g)) /\
                   ~(is_no_scan (oc g) (gm g)) /\ U64.v (wosize_of_object (oc g) (gm g)) == 1)
  = let c = oc g in
    base g;
    gm_no_grey g;
    Wt.step3 g;
    Wt.holds_facts (h g) c Wt.wzS (Wt.const 0UL);
    makeGray_eq c (h g);
    makeBlack_eq c (gd g);
    color_preserves_tag c (h g) Header.Gray;
    color_preserves_tag c (gd g) Header.Black;
    color_preserves_wosize c (h g) Header.Gray;
    color_preserves_wosize c (gd g) Header.Black;
    is_infix_spec c (h g); is_infix_spec c (gm g);
    is_closure_spec c (h g); is_closure_spec c (gm g);
    is_no_scan_spec c (h g); is_no_scan_spec c (gm g)
#pop-options

/// What the allocation gives.
#push-options "--z3rlimit 40"
let mal_ok (g: heap)
  : Lemma (requires roomy)
          (ensures mal g == (gb g, sb g, (n1 g <: U64.t)) /\
                   Seq.mem (n1 g) (objects zero_addr (gb g)) /\ is_black (n1 g) (gb g) /\
                   U64.v (wosize_of_object (n1 g) (gb g)) == 1 /\
                   ~(is_closure (n1 g) (gb g)) /\ ~(is_no_scan (n1 g) (gb g)) /\ ~(is_infix (n1 g) (gb g)) /\
                   PM.alloc_facts (gm g) (gb g) (n1 g) /\
                   (forall (g'': heap). I.fields_written (gb g) g'' (n1 g) ==> PMP.mark_inv g'' (sb g)) /\
                   (forall (i: nat{i < n_pages}). Wt.kind_of (st g) i =!= Free ==> Wt.kind_of (sb g) i == Wt.kind_of (st g) i))
  = gm_ok g;
    malloc_ok (gm g) (st g) (jf g);
    PMP.mark_inv_alloc (gm g) (st g) Wt.wzS;
    CS.mark_alloc_facts (gm g) (st g) Wt.wzS;
    assert (PA.alloc I.Marking (gm g) (st g) Wt.wzS == AP.alloc_col Header.Black (gm g) (st g) Wt.wzS)
#pop-options

/// A block in use at the end of marking keeps its header to `gz`; so does N.
#push-options "--z3rlimit 30"
let keep_gz (g: heap) (y: obj_addr)
  : Lemma (requires roomy /\ ((Seq.mem y (objects zero_addr (gm g)) /\ ~(is_blue y (gm g))) \/ y == n1 g))
          (ensures Seq.mem y (objects zero_addr (gz g)) /\ Seq.mem y (objects zero_addr (gb g)) /\
                   read_word (gz g) (hd_address y) == read_word (gb g) (hd_address y) /\
                   (y =!= n1 g ==> read_word (gb g) (hd_address y) == read_word (gm g) (hd_address y)))
  = mal_ok g;
    write_one (gb g) (n1 g) 0UL
#pop-options

/// The collector's state after the initialising write.
#push-options "--z3rlimit 40"
let gz_ok (g: heap)
  : Lemma (requires roomy)
          (ensures SPM.in_body (gb g) (n1 g) (n1 g <: hp_addr) /\
                   read_word (gz g) (n1 g <: hp_addr) == 0UL /\
                   I.fields_written (gb g) (gz g) (n1 g) /\
                   Seq.mem (n1 g) (objects zero_addr (gz g)) /\ is_black (n1 g) (gz g) /\
                   U64.v (wosize_of_object (n1 g) (gz g)) == 1 /\
                   ~(is_closure (n1 g) (gz g)) /\ ~(is_no_scan (n1 g) (gz g)) /\
                   PM.pmark_ok m0 (gz g) (sb g) MP.scan_none)
  = let x = n1 g in
    let a : hp_addr = x in
    mal_ok g;
    gm_ok g;
    write_one (gb g) x 0UL;
    keep_gz g x;
    same_hdr (gb g) (gz g) x;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (body_one x));
    assert (I.fields_written (gb g) (gz g) x);
    FStar.Classical.forall_intro_2 m0_empty;
    let o = GMM.nursery_refs m0 (gm g) in
    PM.fresh_of_facts (gm g) (gb g) o MP.scan_none x;
    MPA.marking_fresh_write (gb g) o MP.scan_none x a 0UL;
    assert (SPM.field_val (gz g) x 0 == 0UL);
    MPA.marking_fresh_close (gz g) o MP.scan_none x
#pop-options

/// The initialising write.
let iw (g: heap{roomy}) : GTot (MC.init_writes (n1 g) (gb g) (gz g)) =
  gz_ok g;
  MC.Init_write (MC.Init_done (gb g)) (n1 g <: hp_addr) 0UL (gz g) ()

let since_m (g: heap) : obj_addr -> prop = SPC.with_new SPC.nothing_new (n1 g)

/// 3. The barrier write: N's field gets C.
let gw (g: heap) : GTot heap = GB.modify_heap Ph.Marking (gz g) (n1 g <: hp_addr) (oc g <: U64.t)

/// C after the allocation: black, at its address, in `gz`.
#push-options "--z3rlimit 30"
let c_gz (g: heap)
  : Lemma (requires roomy)
          (ensures Seq.mem (oc g) (objects zero_addr (gz g)) /\ is_black (oc g) (gz g) /\
                   ~(is_infix (oc g) (gz g)) /\ U64.v (wosize_of_object (oc g) (gz g)) == 1 /\
                   is_pointer (oc g <: U64.t) /\ resolve_object (oc g) (gz g) == oc g /\
                   infix_addr_wf (gz g) (objects zero_addr (gz g)) (oc g) /\ oc g <> n1 g)
  = c_gm g;
    c_root g;
    mal_ok g;
    keep_gz g (oc g);
    same_hdr (gm g) (gz g) (oc g);
    resolve_non_infix (oc g) (gz g);
    infix_addr_wf_intro (gz g) (objects zero_addr (gz g)) (oc g)
#pop-options

/// The barrier's hypotheses, and the heap after it.
#push-options "--z3rlimit 40"
let write_ok (g: heap)
  : Lemma (requires roomy)
          (ensures GB.modify_ok Ph.Marking m0 (gz g) MP.scan_none (n1 g) (n1 g <: hp_addr) (oc g <: U64.t) /\
                   MPC.cycle_write (MC.snapshot (h g) (rs g) (since_m g)) (gz g) (n1 g) (n1 g <: hp_addr) (oc g <: U64.t) /\
                   gw g == write_word (gz g) (n1 g <: hp_addr) (oc g <: U64.t))
  = gz_ok g;
    c_gz g;
    GI.phase_free_marking ();
    not_pointer_zero ();
    Mark.colors_exclusive (n1 g) (gz g);
    Mark.colors_exclusive (oc g) (gz g)
#pop-options

/// The collector's state after the barrier; nothing is grey.
#push-options "--z3rlimit 40"
let gw_ok (g: heap)
  : Lemma (requires roomy)
          (ensures PM.pmark_ok m0 (gw g) (sb g) MP.scan_none /\ Mark.noGreyObjects (gw g) /\
                   read_word (gw g) (n1 g <: hp_addr) == (oc g <: U64.t) /\
                   (forall (y: obj_addr). (Seq.mem y (objects zero_addr (gw g)) <==> Seq.mem y (objects zero_addr (gz g))) /\
                      (Seq.mem y (objects zero_addr (gz g)) ==> read_word (gw g) (hd_address y) == read_word (gz g) (hd_address y))))
  = let x = n1 g in
    let c = oc g in
    let a : hp_addr = x in
    write_ok g;
    gz_ok g;
    c_gz g;
    mal_ok g;
    write_one (gb g) x 0UL;
    write_one (gz g) x (c <: U64.t);
    let gw' = gw g in
    (* the pages: N's field written with a pointer to C *)
    same_hdr (gz g) gw' c;
    resolve_non_infix c gw';
    infix_addr_wf_intro gw' (objects zero_addr gw') c;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (body_one x));
    assert (I.field_ok gw' (c <: U64.t));
    assert (I.fields_written (gb g) gw' x);
    (* the marking invariant: akhil's barrier lemma *)
    FStar.Classical.forall_intro_2 m0_empty;
    MM.marking_write_barrier (gz g) (GMM.nursery_refs m0 (gz g)) MP.scan_none x a (c <: U64.t);
    (* nothing grey *)
    gm_no_grey g;
    let ng (y: obj_addr) : Lemma (requires Seq.mem y (objects zero_addr gw')) (ensures ~(is_gray y gw'))
      = assert (Seq.mem y (objects zero_addr (gb g)));
        same_hdr (gb g) gw' y;
        if y = x then Mark.colors_exclusive x (gb g)
        else if is_gray y (gb g) then begin
          Mark.colors_exclusive y (gb g);
          assert (in_use (MPA.free_or_new x) (gb g) y);
          assert (in_use free_stw (gm g) y);
          same_hdr (gm g) (gb g) y
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ng)
#pop-options

/// N's field holds 0 when it is handed out: storable for any snapshot.
let zero_storable (fr: free_def) (g: heap) (x: obj_addr)
  : Lemma (requires U64.v (wosize_of_object x g) == 1 /\ read_word g (x <: hp_addr) == 0UL)
          (ensures SPM.fields_storable fr g x)
  = not_pointer_zero ();
    assert (SPM.field_val g x 0 == 0UL)

let n1_storable (g: heap)
  : Lemma (requires roomy)
          (ensures SPM.fields_storable (MPC.outside_snapshot (MC.snapshot (h g) (rs g) (since_m g))) (gz g) (n1 g))
  = gz_ok g;
    zero_storable (MPC.outside_snapshot (MC.snapshot (h g) (rs g) (since_m g))) (gz g) (n1 g)

/// ---------------------------------------------------------------------------
/// The sweeping side
/// ---------------------------------------------------------------------------

let s0e (g: heap) : GTot pstate = SS.start_sweep (sb g)

/// A's page and B's run at this sweep's start: unswept, as in `run`; the
/// allocation while marking changed neither page.
let at_start_e (g: heap)
  : Lemma (requires roomy)
          (ensures (entry (s0e g).pm (ia g)).kind == Pool Wt.cA /\ not (entry (s0e g).pm (ia g)).swept /\
                   (entry (s0e g).pm (i0 g)).kind == LargeHead Wt.kL /\ not (entry (s0e g).pm (i0 g)).swept)
  = Wt.step3 g;
    mal_ok g;
    FStar.Classical.forall_intro (SS.clear_entry (sb g).pm)

/// A is still white when marking ends.
#push-options "--z3rlimit 30"
let a_white_e (g: heap)
  : Lemma (requires roomy) (ensures ~(is_black (oa g) (gw g)))
  = let a = oa g in
    base g;
    gm_no_grey g;
    gm_other g a;
    same_hdr (h g) (gm g) a;
    mal_ok g;
    keep_gz g a;
    gw_ok g;
    same_hdr (gm g) (gb g) a;
    same_hdr (gb g) (gz g) a;
    same_hdr (gz g) (gw g) a;
    Mark.colors_exclusive a (h g)
#pop-options

/// 6. A's page swept.
let g1e (g: heap{roomy}) : GTot heap = fst (SA.step (gw g) (s0e g) (ia g))
let s1e (g: heap{roomy}) : GTot pstate = snd (SA.step (gw g) (s0e g) (ia g))

let step1e (g: heap)
  : Lemma (requires roomy)
          (ensures SA.sweep_ready (gw g) (s0e g) /\ SA.mark_done (gw g) /\
                   pages_ok_sw (gw g) (s0e g) /\ pages_ok_sw (g1e g) (s1e g) /\
                   ((entry (s1e g).pm (ia g)).kind == Free \/ has_free_slot (s1e g).pm Wt.cA (ia g)) /\
                   (entry (s1e g).pm (i0 g)).kind == LargeHead Wt.kL /\ not (entry (s1e g).pm (i0 g)).swept)
  = gw_ok g;
    CS.handover_ready (gw g) (sb g) (GMM.nursery_refs m0 (gw g)) MP.scan_none;
    MS2.sw_start (gw g) (s0e g);
    at_start_e g;
    at_start g;
    a_white_e g;
    MSV.step1_abs (gw g) (s0e g) (ia g) (ka g) (oa g) (i0 g) Wt.kL

/// 7. An allocation, its field cleared.
let alloc1e (g: heap{roomy}) : GTot (heap & pstate & U64.t) = PA.alloc I.Sweeping (g1e g) (s1e g) Wt.wzS
let gae (g: heap{roomy}) : GTot heap = let (a, _, _) = alloc1e g in a
let s2e (g: heap{roomy}) : GTot pstate = let (_, s, _) = alloc1e g in s
let one (g: heap{roomy}) : GTot obj_addr = Wt.as_obj (let (_, _, o) = alloc1e g in o)
let g2e (g: heap{roomy}) : GTot heap = B.zeros (gae g) (U64.v (one g)) Wt.wzS

#push-options "--z3rlimit 30"
let alloc_ok_e (g: heap)
  : Lemma (requires roomy)
          (ensures alloc1e g == (gae g, s2e g, (one g <: U64.t)) /\
                   I.fields_written_with (free_sw (s1e g).pm) (gae g) (g2e g) (one g) /\
                   pages_ok_sw (g2e g) (s2e g) /\
                   not (unswept_at (s1e g).pm (one g)) /\
                   (entry (s2e g).pm (i0 g)).kind == LargeHead Wt.kL /\ not (entry (s2e g).pm (i0 g)).swept)
  = step1e g;
    at_start_e g;
    MSV.alloc_abs (g1e g) (s1e g) (ia g) (i0 g) Wt.kL
#pop-options

/// 8. The program write mid-sweep: the new object's field gets 1.
let g3e (g: heap{roomy}) : GTot heap = write_word (g2e g) (one g <: hp_addr) 1UL

let not_pointer_one () : Lemma (~(is_pointer 1UL)) = ()

#push-options "--z3rlimit 40"
let swrite_ok (g: heap)
  : Lemma (requires roomy)
          (ensures pages_ok_sw (g2e g) (s2e g) /\ Seq.mem (one g) (objects zero_addr (g2e g)) /\
                   ~(is_blue (one g) (g2e g)) /\ SPM.in_body (g2e g) (one g) (one g <: hp_addr) /\
                   read_word (g2e g) (one g <: hp_addr) == 0UL /\
                   read_word (g3e g) (one g <: hp_addr) == 1UL /\
                   pages_ok_sw (g3e g) (s2e g))
  = let x = one g in
    step1e g;
    alloc_ok_e g;
    MA.alloc_sw_ok (g1e g) (s1e g) Wt.wzS;
    let ga' = gae g in
    FStar.Classical.forall_intro (B.zeros_read ga' (U64.v x) Wt.wzS);
    assert (F.fctx ga' (g2e g) x);
    F.obj_same ga' (g2e g) x x;
    same_hdr ga' (g2e g) x;
    write_one (g2e g) x 1UL;
    not_pointer_one ();
    FStar.Classical.forall_intro (FStar.Classical.move_requires (body_one x));
    assert (I.fields_written_with (free_sw (s1e g).pm) ga' (g3e g) x)
#pop-options

/// 9. The rest of the sweep, and the end.
let gfe (g: heap{roomy}) : GTot heap = fst (SA.sweep_from (g3e g) (s2e g) 0)
let sfe (g: heap{roomy}) : GTot pstate = snd (SA.sweep_from (g3e g) (s2e g) 0)

let rest_ends_e (g: heap)
  : Lemma (requires roomy)
          (ensures pages_ok_sw (gfe g) (sfe g) /\ PMP.all_swept (sfe g))
  = swrite_ok g;
    pages_ok_sw_elim (g3e g) (s2e g);
    if n_pages > 0 then assert (cont_ok (s2e g).pm 0);
    MS2.sweep_from_sw (g3e g) (s2e g) 0

/// The addresses the run hands out: N while marking, the allocation mid-sweep.
let since_e (g: heap{roomy}) : obj_addr -> prop =
  GC_.union (since_m g) (SPC.with_new SPC.nothing_new (one g <: U64.t))

/// **The run, with every event.**
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let run_all (g: heap{roomy}) : GTot (PC.pcycle (h g) (rs g) (gfe g) (sfe g) I.Idle (since_e g)) =
  start_pre g;
  handover_ok g;
  gm_ok g;
  mal_ok g;
  gz_ok g;
  n1_storable g;
  write_ok g;
  gw_ok g;
  step1e g;
  at_start_e g;
  alloc_ok_e g;
  swrite_ok g;
  rest_ends_e g;
  S.mark_steps_refl (gw g) MP.scan_none;
  let rm0 : PM.pmarking (h g) (rs g) (MStart.darkened (h g) (rs g)) (st g) MP.scan_none SPC.nothing_new =
    PM.PStart m0 (st g) () in
  let rm1 : PM.pmarking (h g) (rs g) (gm g) (st g) MP.scan_none SPC.nothing_new =
    PM.PSlice rm0 m0 (gm g) MP.scan_none () in
  let rm2 : PM.pmarking (h g) (rs g) (gz g) (sb g) MP.scan_none (since_m g) =
    PM.PAlloc rm1 m0 Wt.wzS (gb g) (sb g) (n1 g) () (gz g) (iw g) () in
  let rm3 : PM.pmarking (h g) (rs g) (gw g) (sb g) MP.scan_none (since_m g) =
    PM.PWrite rm2 m0 (n1 g) (n1 g <: hp_addr) (oc g <: U64.t) () in
  let r0 : PS.psweep (gw g) (gw g) (s0e g) I.Sweeping SPC.nothing_new = PS.SStart (s0e g) () in
  let r1 : PS.psweep (gw g) (g1e g) (s1e g) I.Sweeping SPC.nothing_new = PS.SStep r0 (ia g) () in
  let r2 : PS.psweep (gw g) (g2e g) (s2e g) I.Sweeping (SPC.with_new SPC.nothing_new (one g <: U64.t)) =
    PS.SAlloc r1 Wt.wzS (gae g) (s2e g) (one g) () (g2e g) () in
  let r3 : PS.psweep (gw g) (g3e g) (s2e g) I.Sweeping (SPC.with_new SPC.nothing_new (one g <: U64.t)) =
    PS.SWrite r2 (one g) (one g <: hp_addr) 1UL () in
  let r4 = rest r3 0 in
  let r5 : PS.psweep (gw g) (gfe g) (sfe g) I.Idle (SPC.with_new SPC.nothing_new (one g <: U64.t)) =
    PS.SEnd r4 () in
  assert (PC.sweep_start_st r0 == s0e g);
  assert (PC.sweep_start_st r1 == PC.sweep_start_st r0);
  assert (PC.sweep_start_st r2 == PC.sweep_start_st r1);
  assert (PC.sweep_start_st r3 == PC.sweep_start_st r2);
  assert (PC.sweep_start_st r5 == PC.sweep_start_st r4);
  PC.PSweep rm3 m0 (gw g) MP.scan_none () r5 ()
#pop-options

/// ---------------------------------------------------------------------------
/// It is not trivial
/// ---------------------------------------------------------------------------

/// B is neither allocation.
let b_not_new_e (g: heap)
  : Lemma (requires roomy) (ensures ob g <> n1 g /\ ob g <> one g)
  = base g;
    gm_no_grey g;
    gm_other g (ob g);
    same_hdr (h g) (gm g) (ob g);
    Wt.step3 g;
    mal_ok g;
    alloc_ok_e g;
    at_start g;
    at_start_e g;
    page_base_mono (i0 g) ((i0 g) + 1);
    FStar.Math.Lemmas.distributivity_add_left (i0 g) 1 page_bytes;
    page_uw (s1e g).pm (i0 g) (U64.v (ob g) - 8);
    step1e g

/// **The run is not trivial**: what `run` shows of the start, and every
/// event changes something.  N was not a block in use when it was handed
/// out; the barrier write replaces its field's 0 with a pointer to C; the
/// write mid-sweep replaces the new object's 0 with 1; B is neither
/// allocation, so the run must free it.
let run_all_nontrivial (g: heap)
  : Lemma (requires roomy)
          (ensures GMC.reachable_at_start (h g) (rs g) (oc g) /\
                   Seq.mem (ob g) (objects zero_addr (h g)) /\ ~(is_blue (ob g) (h g)) /\
                   ~(GMC.reachable_at_start (h g) (rs g) (ob g)) /\ ~(since_e g (ob g)) /\
                   since_e g (n1 g) /\ since_e g (one g) /\
                   GC_.unreachable_covered (h g) (rs g) (heap_size - 8) /\
                   ~(Seq.mem (n1 g) (objects zero_addr (gm g)) /\ ~(is_blue (n1 g) (gm g))) /\
                   read_word (gz g) (n1 g <: hp_addr) == 0UL /\ ~(is_pointer 0UL) /\
                   read_word (gw g) (n1 g <: hp_addr) == (oc g <: U64.t) /\ is_pointer (oc g <: U64.t) /\
                   read_word (g2e g) (one g <: hp_addr) == 0UL /\
                   read_word (g3e g) (one g <: hp_addr) == 1UL)
  = run_nontrivial g;
    b_not_new_e g;
    mal_ok g;
    gz_ok g;
    gw_ok g;
    c_root g;
    not_pointer_zero ();
    swrite_ok g

/// **The theorems on it**: C survives; B is freed; the heap's last word is
/// free or in an object the run handed out.
let run_all_theorems (g: heap)
  : Lemma (requires roomy)
          (ensures Seq.mem (oc g) (objects zero_addr (gfe g)) /\ ~(is_blue (oc g) (gfe g)) /\
                   SPC.freed (gfe g) (ob g) /\
                   (LL.blue_covered (gfe g) (heap_size - 8) \/ SPC.new_covered (since_e g) (gfe g) (heap_size - 8)))
  = run_all_nontrivial g;
    let r = run_all g in
    PC.cycle_survives r;
    PC.cycle_frees_unreachable r;
    PC.cycle_lossless r
