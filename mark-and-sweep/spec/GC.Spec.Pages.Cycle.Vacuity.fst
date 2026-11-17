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
/// The run has no barrier write, no allocation while marking and no write
/// mid-sweep: those constructors' hypotheses are not shown satisfiable here.

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

let m0_empty (w: obj_addr) : Lemma (~(GMM.nursery_refs m0 w))
  = GMM.nursery_refs_reset m_any w

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
    FStar.Classical.forall_intro m0_empty;
    MP.marking_inv_start (gd g) (GMM.nursery_refs m0)
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
    S.mark_steps_inv (gd g) (gm g) MP.scan_none MP.scan_none (GMM.nursery_refs m0);
    CS.handover_ready (gm g) (st g) (GMM.nursery_refs m0) MP.scan_none

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
