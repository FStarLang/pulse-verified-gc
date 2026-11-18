/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cycle.VacuityDark - a page cycle whose barrier darkens
/// ---------------------------------------------------------------------------
///
/// The vacuity rule (plan §18), for the branches `Cycle.Vacuity.run_all`
/// does not take: there the barrier write overwrites 0, which is no
/// pointer, so it darkens nothing, and the write mid-sweep stores an
/// integer.  Neither can be changed in that run: its roots are `[C]`, whose
/// one field is 0, so what is reachable at the start is C alone, and C is
/// grey once marking starts.  A value the barrier finds pointing at a white
/// object must point into the snapshot (akhil's account), so at a white
/// object reachable at the start.
///
/// `run_dark g` is a run from the same start `W` with `W`'s own roots,
/// `[A]` (A's field points to B, B's fields are 0, C is unreachable):
///
///   0. **Start** (`PStart`): A greyed; B is white and reachable at the
///      start;
///   1. **An allocation while marking** (`PAlloc`): N, one field, black;
///      its initialising write stores 0;
///   2. **The barrier write** (`PWrite`): A's field, which points to the
///      white B, gets a pointer to N.  The barrier darkens the old value:
///      **B turns grey**.  The collector's state after it is
///      `Cycle.Write.pwrite_keeps` (plan §23.2 M-b);
///   3. **The hand-over**: the mark moves scan A (its field, N, is black)
///      and blacken it, then scan B's fields (all 0) and blacken it;
///      nothing is grey;
///   4. **the sweep starts**; 5. **C's page is swept** (A's page: C is
///      dead, A black); 6. **an allocation**, O, its field cleared;
///   7. **A program write mid-sweep** (`SWrite`) into A, a block older than
///      the sweep: A's field gets **a pointer to O**.  The mid-sweep
///      invariant after it is `Cycle.Write.swrite_keeps` (§23.3 S-g);
///   8. **the rest of the sweep** and **the end**.
///
/// `run_dark_nontrivial`: B is reachable at the start and is white when the
/// barrier overwrites A's pointer to it, grey after; A's field goes from a
/// pointer to B to a pointer to N, and mid-sweep to a pointer to O; N and O
/// are handed out.  `run_dark_theorems`: A and B survive the cycle -- B
/// although the program cut A's pointer to it while marking.

module GC.Spec.Pages.Cycle.VacuityDark

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
module SPI = GC.Spec.SweepPhase.Intrinsic
module W = GC.Spec.Walk
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module PMP = GC.Spec.Pages.MarkPhase
module SA = GC.Spec.Pages.SweepAll
module SS = GC.Spec.Pages.StartSweep
module MS2 = GC.Spec.Pages.MidSweepStep
module MA = GC.Spec.Pages.MidSweepAlloc
module Wt = GC.Spec.Pages.Witness
module MSV = GC.Spec.Pages.MidSweepVacuity
module Th = GC.Spec.Pages.Theorems
module CS = GC.Spec.Pages.Cycle.State
module PM = GC.Spec.Pages.Cycle.Mark
module PS = GC.Spec.Pages.Cycle.Sweep
module PC = GC.Spec.Pages.Cycle
module PW = GC.Spec.Pages.Cycle.Write
module V = GC.Spec.Pages.Cycle.Vacuity
module AP = GC.Spec.Pages.AllocPhase
module F = GC.Spec.Pages.Fill
module B = GC.Spec.Pages.Blocks
module MPA = GC.Spec.MarkPhase.Alloc
module MC = GC.Gen.MarkPhase.Cycle
module GB = GC.Gen.Barrier
module GI = GC.Gen.Incremental
module Ph = GC.Spec.Phase
module SPM = GC.Spec.SweepPhase.Mutator
module Within = GC.Spec.Graph.Within

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The start: `W` with its roots, `[A]`
/// ---------------------------------------------------------------------------

let h (g: heap) : GTot heap = V.h g
let st (g: heap) : GTot pstate = V.st g
let oa (g: heap) : GTot obj_addr = V.oa g
let ob (g: heap) : GTot obj_addr = V.ob g
let oc (g: heap) : GTot obj_addr = V.oc g

/// The roots: A.
let rs (g: heap) : GTot (seq U64.t) = Seq.create 1 (oa g <: U64.t)

/// An object of a heap is a pointer.
let obj_pointer (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g)) (ensures is_pointer (x <: U64.t))
  = W.objects_mem_iff g zero_addr x;
    is_val_addr_spec (x <: U64.t)

/// What `W` gives of A and B.
let base (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures PA.inv I.Idle (h g) (st g) /\
                   oc g <> oa g /\ oc g <> ob g /\ oa g <> ob g /\
                   Seq.mem (oa g) (objects zero_addr (h g)) /\ Seq.mem (ob g) (objects zero_addr (h g)) /\
                   Seq.mem (oc g) (objects zero_addr (h g)) /\
                   U64.v (wosize_of_object (oa g) (h g)) == 1 /\ is_white (oa g) (h g) /\
                   ~(is_blue (oa g) (h g)) /\ ~(is_infix (oa g) (h g)) /\ ~(is_no_scan (oa g) (h g)) /\
                   ~(is_closure (oa g) (h g)) /\
                   U64.v (wosize_of_object (ob g) (h g)) == Wt.wzL /\ is_white (ob g) (h g) /\
                   ~(is_blue (ob g) (h g)) /\ ~(is_infix (ob g) (h g)) /\ ~(is_no_scan (ob g) (h g)) /\
                   is_white (oc g) (h g) /\
                   read_word (h g) (oa g <: hp_addr) == (ob g <: U64.t) /\
                   (forall (b: hp_addr). U64.v (ob g) <= U64.v b /\ U64.v b < U64.v (ob g) + Wt.wzL * 8 ==>
                      read_word (h g) b == 0UL))
  = Wt.step3 g;
    Wt.holds_facts (h g) (oa g) Wt.wzS (Wt.const (ob g));
    Wt.holds_facts (h g) (ob g) Wt.wzL (Wt.const 0UL);
    Wt.holds_facts (h g) (oc g) Wt.wzS (Wt.const 0UL)

/// A is a root that names itself.
let a_root (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures MBP.root_valid_for_darkening (h g) (oa g <: U64.t) /\ is_pointer (oa g <: U64.t) /\
                   resolve_object (oa g) (h g) == oa g /\ U64.v (oa g) >= U64.v zero_addr + 8 /\
                   Seq.index (rs g) 0 == (oa g <: U64.t) /\ Seq.length (rs g) == 1)
  = base g;
    let a = oa g in
    W.objects_mem_iff (h g) zero_addr a;
    resolve_non_infix a (h g);
    is_val_addr_spec (a <: U64.t)

/// The start's precondition.
let start_pre (g: heap)
  : Lemma (requires Wt.big_enough) (ensures PM.pstart_pre V.m0 (h g) (st g) (rs g))
  = base g;
    a_root g;
    V.m0_reset ()

/// Root darkening greys A, and only A.
let gd (g: heap) : GTot heap = makeGray (oa g) (h g)

#push-options "--fuel 1 --z3rlimit 30"
let darkened_a (g: heap)
  : Lemma (requires Wt.big_enough) (ensures MStart.darkened (h g) (rs g) == gd g)
  = let a = oa g in
    let r = rs g in
    let h0 = h g in
    base g;
    a_root g;
    MB.darken_roots_bounded_prefix_step h0 Seq.empty r 0 2;
    assert (MB.darken_roots_bounded_prefix_spec h0 Seq.empty r 0 2 == (h0, Seq.empty));
    hd_address_spec a;
    hd_address_bounds a;
    f_hd_roundtrip a;
    assert (U64.sub a mword == hd_address a)
#pop-options

/// Recolouring `x` keeps every word but `x`'s header, and the objects.
let recolour_word (x: obj_addr) (g: heap) (c: Header.color_sem) (b: hp_addr)
  : Lemma (requires b <> hd_address x)
          (ensures read_word (set_object_color x g c) b == read_word g b)
  = set_object_color_read_word x b g c

/// A's field and B's fields are no header.
let away (g: heap) (b: hp_addr)
  : Lemma (requires Wt.big_enough /\
                    (b == (oa g <: hp_addr) \/
                     (U64.v (ob g) <= U64.v b /\ U64.v b < U64.v (ob g) + Wt.wzL * 8)))
          (ensures b <> hd_address (oa g) /\ b <> hd_address (ob g) /\
                   (U64.v (ob g) <= U64.v b /\ U64.v b < U64.v (ob g) + Wt.wzL * 8 ==> b <> (oa g <: hp_addr)))
  = base g;
    hd_address_spec (oa g);
    hd_address_spec (ob g);
    F.other_apart (h g) (oa g) (ob g);
    F.other_apart (h g) (ob g) (oa g)

/// The darkened heap: A grey; every other header, and every field word, as
/// at the start.
#push-options "--z3rlimit 30"
let gd_facts (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures objects zero_addr (gd g) == objects zero_addr (h g) /\
                   is_gray (oa g) (gd g) /\ ~(is_no_scan (oa g) (gd g)) /\ ~(is_closure (oa g) (gd g)) /\
                   ~(is_infix (oa g) (gd g)) /\ U64.v (wosize_of_object (oa g) (gd g)) == 1 /\
                   (forall (b: hp_addr). b <> hd_address (oa g) ==> read_word (gd g) b == read_word (h g) b))
  = let a = oa g in
    let h0 = h g in
    base g;
    makeGray_eq a h0;
    color_change_preserves_objects h0 a Header.Gray;
    makeGray_is_gray a h0;
    color_preserves_is_no_scan a h0 Header.Gray;
    color_change_preserves_is_closure a a h0 Header.Gray;
    color_preserves_wosize a h0 Header.Gray;
    color_change_preserves_is_infix a a h0 Header.Gray;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (recolour_word a h0 Header.Gray))
#pop-options

/// Nothing but A is grey or black in the darkened heap.
#push-options "--z3rlimit 30"
let gd_colours (g: heap) (y: obj_addr)
  : Lemma (requires Wt.big_enough /\ Seq.mem y (objects zero_addr (gd g)) /\ y <> oa g)
          (ensures ~(is_gray y (gd g)) /\ ~(is_black y (gd g)) /\
                   read_word (gd g) (hd_address y) == read_word (h g) (hd_address y))
  = base g;
    gd_facts g;
    PM.idle_facts (h g) (st g);
    hd_address_spec y; hd_address_spec (oa g);
    color_of_header_eq y (h g) (gd g);
    is_gray_iff y (h g); is_gray_iff y (gd g);
    is_black_iff y (h g); is_black_iff y (gd g)
#pop-options

/// The collector's state at the darkened heap.
#push-options "--z3rlimit 30"
let gd_ok (g: heap)
  : Lemma (requires Wt.big_enough) (ensures PM.pmark_ok V.m0 (gd g) (st g) MP.scan_none)
  = start_pre g;
    darkened_a g;
    PM.start_facts V.m0 (h g) (st g) (rs g);
    MP.no_black_tri_color (gd g);
    FStar.Classical.forall_intro V.m0_empty;
    MP.marking_inv_start (gd g) (GMM.nursery_refs V.m0)
#pop-options

/// ---------------------------------------------------------------------------
/// 1. An allocation while marking
/// ---------------------------------------------------------------------------

let mal (g: heap) : GTot (heap & pstate & U64.t) = PA.alloc I.Marking (gd g) (st g) Wt.wzS
let gb (g: heap) : GTot heap = let (a, _, _) = mal g in a
let sb (g: heap) : GTot pstate = let (_, s, _) = mal g in s
let n1 (g: heap) : GTot obj_addr = Wt.as_obj (let (_, _, o) = mal g in o)
let gz (g: heap) : GTot heap = write_word (gb g) (n1 g <: hp_addr) 0UL

/// What the allocation gives.
#push-options "--z3rlimit 40"
let mal_ok (g: heap)
  : Lemma (requires V.roomy)
          (ensures mal g == (gb g, sb g, (n1 g <: U64.t)) /\
                   Seq.mem (n1 g) (objects zero_addr (gb g)) /\ is_black (n1 g) (gb g) /\
                   U64.v (wosize_of_object (n1 g) (gb g)) == 1 /\
                   ~(is_closure (n1 g) (gb g)) /\ ~(is_no_scan (n1 g) (gb g)) /\ ~(is_infix (n1 g) (gb g)) /\
                   PM.alloc_facts (gd g) (gb g) (n1 g) /\
                   (forall (i: nat{i < n_pages}). Wt.kind_of (st g) i =!= Free ==> Wt.kind_of (sb g) i == Wt.kind_of (st g) i))
  = gd_ok g;
    V.malloc_ok (gd g) (st g) (V.jf g);
    CS.mark_alloc_facts (gd g) (st g) Wt.wzS;
    assert (PA.alloc I.Marking (gd g) (st g) Wt.wzS == AP.alloc_col Header.Black (gd g) (st g) Wt.wzS)
#pop-options

/// A block in use in the darkened heap keeps its header, and its fields,
/// to `gz`; N keeps its header.
#push-options "--z3rlimit 30"
let keep_gz (g: heap) (y: obj_addr)
  : Lemma (requires V.roomy /\ ((Seq.mem y (objects zero_addr (gd g)) /\ ~(is_blue y (gd g))) \/ y == n1 g))
          (ensures Seq.mem y (objects zero_addr (gz g)) /\ Seq.mem y (objects zero_addr (gb g)) /\
                   read_word (gz g) (hd_address y) == read_word (gb g) (hd_address y) /\
                   (y =!= n1 g ==>
                      read_word (gb g) (hd_address y) == read_word (gd g) (hd_address y) /\
                      SPI.same_block (gd g) (gb g) (hd_address y)))
  = mal_ok g;
    V.write_one (gb g) (n1 g) 0UL
#pop-options

/// The collector's state after the initialising write.
#push-options "--z3rlimit 40"
let gz_ok (g: heap)
  : Lemma (requires V.roomy)
          (ensures SPM.in_body (gb g) (n1 g) (n1 g <: hp_addr) /\
                   read_word (gz g) (n1 g <: hp_addr) == 0UL /\
                   Seq.mem (n1 g) (objects zero_addr (gz g)) /\ is_black (n1 g) (gz g) /\
                   U64.v (wosize_of_object (n1 g) (gz g)) == 1 /\
                   ~(is_closure (n1 g) (gz g)) /\ ~(is_no_scan (n1 g) (gz g)) /\ ~(is_infix (n1 g) (gz g)) /\
                   PM.pmark_ok V.m0 (gz g) (sb g) MP.scan_none)
  = let x = n1 g in
    let a : hp_addr = x in
    mal_ok g;
    gd_ok g;
    V.write_one (gb g) x 0UL;
    keep_gz g x;
    V.same_hdr (gb g) (gz g) x;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (V.body_one x));
    assert (I.fields_written (gb g) (gz g) x);
    PMP.mark_inv_alloc (gd g) (st g) Wt.wzS;
    assert (PA.alloc I.Marking (gd g) (st g) Wt.wzS == AP.alloc_col Header.Black (gd g) (st g) Wt.wzS);
    let o = GMM.nursery_refs V.m0 in
    PM.fresh_of_facts (gd g) (gb g) o MP.scan_none x;
    MPA.marking_fresh_write (gb g) o MP.scan_none x a 0UL;
    assert (SPM.field_val (gz g) x 0 == 0UL);
    V.zero_storable free_stw (gz g) x;
    MPA.marking_fresh_close (gz g) o MP.scan_none x
#pop-options

/// The initialising write.
let iw (g: heap{V.roomy}) : GTot (MC.init_writes (n1 g) (gb g) (gz g)) =
  gz_ok g;
  MC.Init_write (MC.Init_done (gb g)) (n1 g <: hp_addr) 0UL (gz g) ()

let since_m (g: heap) : obj_addr -> prop = SPC.with_new SPC.nothing_new (n1 g)

let n1_storable (g: heap)
  : Lemma (requires V.roomy)
          (ensures SPM.fields_storable (MPC.outside_snapshot (MC.snapshot (h g) (rs g) (since_m g))) (gz g) (n1 g))
  = gz_ok g;
    V.zero_storable (MPC.outside_snapshot (MC.snapshot (h g) (rs g) (since_m g))) (gz g) (n1 g)

/// A and B after the allocation: A grey, B white, at their addresses, with
/// their fields; N is neither.
#push-options "--z3rlimit 40"
let ab_gz (g: heap)
  : Lemma (requires V.roomy)
          (ensures Seq.mem (oa g) (objects zero_addr (gz g)) /\ is_gray (oa g) (gz g) /\
                   ~(is_no_scan (oa g) (gz g)) /\ ~(is_closure (oa g) (gz g)) /\ ~(is_infix (oa g) (gz g)) /\
                   U64.v (wosize_of_object (oa g) (gz g)) == 1 /\
                   Seq.mem (ob g) (objects zero_addr (gz g)) /\ is_white (ob g) (gz g) /\
                   ~(is_no_scan (ob g) (gz g)) /\ ~(is_infix (ob g) (gz g)) /\
                   U64.v (wosize_of_object (ob g) (gz g)) == Wt.wzL /\
                   oa g <> n1 g /\ ob g <> n1 g /\
                   read_word (gz g) (oa g <: hp_addr) == (ob g <: U64.t) /\
                   (forall (b: hp_addr). U64.v (ob g) <= U64.v b /\ U64.v b < U64.v (ob g) + Wt.wzL * 8 ==>
                      read_word (gz g) b == 0UL))
  = let a = oa g in
    let bb = ob g in
    let x = n1 g in
    base g;
    gd_facts g;
    mal_ok g;
    hd_address_spec a; hd_address_spec bb;
    gd_colours g bb;
    color_of_header_eq bb (h g) (gd g);
    is_white_iff bb (h g); is_white_iff bb (gd g);
    is_blue_iff bb (h g); is_blue_iff bb (gd g);
    Mark.colors_exclusive a (gd g);
    keep_gz g a;
    keep_gz g bb;
    V.same_hdr (gd g) (gz g) a;
    V.same_hdr (gb g) (gz g) a;
    V.same_hdr (gd g) (gb g) a;
    V.same_hdr (h g) (gd g) bb;
    V.same_hdr (gd g) (gb g) bb;
    V.same_hdr (gb g) (gz g) bb;
    (* the field words: kept by the allocation (same block), and by N's write *)
    V.write_one (gb g) x 0UL;
    SPM.in_body_block (gd g) a (a <: hp_addr);
    F.other_apart (gb g) x a;
    F.other_apart (gb g) x bb;
    hd_address_spec x;
    let bw (b: hp_addr)
      : Lemma (requires U64.v bb <= U64.v b /\ U64.v b < U64.v bb + Wt.wzL * 8)
              (ensures read_word (gz g) b == 0UL)
      = away g b;
        SPM.in_body_block (gd g) bb b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires bw);
    away g (a <: hp_addr)
#pop-options

/// ---------------------------------------------------------------------------
/// 2. The barrier write: A's field, which points to the white B, gets N
/// ---------------------------------------------------------------------------

let gw (g: heap) : GTot heap = GB.modify_heap Ph.Marking (gz g) (oa g <: hp_addr) (n1 g <: U64.t)

/// The barrier greys B, A's old target.
let gzb (g: heap) : GTot heap = makeGray (ob g) (gz g)

let darken_b (g: heap)
  : Lemma (requires V.roomy)
          (ensures MM.darken (gz g) (read_word (gz g) (oa g <: hp_addr)) == gzb g /\
                   gw g == write_word (gzb g) (oa g <: hp_addr) (n1 g <: U64.t))
  = ab_gz g;
    obj_pointer (gz g) (ob g);
    resolve_non_infix (ob g) (gz g)

/// The barrier's hypotheses: a program write of N, black, into A, grey.
#push-options "--z3rlimit 40"
let write_ok (g: heap)
  : Lemma (requires V.roomy)
          (ensures GB.modify_ok Ph.Marking V.m0 (gz g) MP.scan_none (oa g) (oa g <: hp_addr) (n1 g <: U64.t) /\
                   MPC.cycle_write (MC.snapshot (h g) (rs g) (since_m g)) (gz g) (oa g) (oa g <: hp_addr) (n1 g <: U64.t))
  = gz_ok g;
    ab_gz g;
    obj_pointer (gz g) (n1 g);
    resolve_non_infix (n1 g) (gz g);
    infix_addr_wf_intro (gz g) (objects zero_addr (gz g)) (n1 g);
    GI.phase_free_marking ();
    Mark.colors_exclusive (n1 g) (gz g);
    Mark.colors_exclusive (oa g) (gz g);
    MPC.in_use_outside_snapshot (MC.snapshot (h g) (rs g) (since_m g)) (gz g) (oa g);
    MPC.in_use_outside_snapshot (MC.snapshot (h g) (rs g) (since_m g)) (gz g) (n1 g)
#pop-options

/// **The collector's state after the barrier**: discharged by
/// `Cycle.Write.pwrite_keeps`, from the event's own hypotheses.
let gw_ok (g: heap)
  : Lemma (requires V.roomy) (ensures PM.pmark_ok V.m0 (gw g) (sb g) MP.scan_none)
  = gz_ok g;
    write_ok g;
    PW.pwrite_keeps V.m0 (gz g) (sb g) MP.scan_none (oa g) (oa g <: hp_addr) (n1 g <: U64.t)

/// The heap after the barrier: B grey, A's field N; every other header and
/// word as before.
#push-options "--z3rlimit 40"
let gw_facts (g: heap)
  : Lemma (requires V.roomy)
          (ensures (forall (y: obj_addr). Seq.mem y (objects zero_addr (gw g)) <==> Seq.mem y (objects zero_addr (gz g))) /\
                   (forall (y: obj_addr). Seq.mem y (objects zero_addr (gz g)) /\ y =!= ob g ==>
                      read_word (gw g) (hd_address y) == read_word (gz g) (hd_address y)) /\
                   Seq.mem (oa g) (objects zero_addr (gw g)) /\ is_gray (oa g) (gw g) /\
                   ~(is_no_scan (oa g) (gw g)) /\ ~(is_closure (oa g) (gw g)) /\ ~(is_infix (oa g) (gw g)) /\
                   U64.v (wosize_of_object (oa g) (gw g)) == 1 /\
                   Seq.mem (ob g) (objects zero_addr (gw g)) /\ is_gray (ob g) (gw g) /\
                   ~(is_no_scan (ob g) (gw g)) /\ U64.v (wosize_of_object (ob g) (gw g)) == Wt.wzL /\
                   Seq.mem (n1 g) (objects zero_addr (gw g)) /\ is_black (n1 g) (gw g) /\ ~(is_infix (n1 g) (gw g)) /\
                   read_word (gw g) (oa g <: hp_addr) == (n1 g <: U64.t) /\
                   (forall (b: hp_addr). U64.v (ob g) <= U64.v b /\ U64.v b < U64.v (ob g) + Wt.wzL * 8 ==>
                      read_word (gw g) b == 0UL))
  = let a = oa g in
    let bb = ob g in
    let x = n1 g in
    let g0 = gz g in
    let g1 = gzb g in
    ab_gz g;
    gz_ok g;
    darken_b g;
    makeGray_eq bb g0;
    color_change_preserves_objects g0 bb Header.Gray;
    makeGray_is_gray bb g0;
    color_preserves_is_no_scan bb g0 Header.Gray;
    color_preserves_wosize bb g0 Header.Gray;
    hd_address_spec a; hd_address_spec bb; hd_address_spec x;
    let hdr (y: obj_addr) : Lemma (y <> bb ==> read_word g1 (hd_address y) == read_word g0 (hd_address y))
      = if y <> bb then begin hd_address_spec y; recolour_word bb g0 Header.Gray (hd_address y) end
    in
    FStar.Classical.forall_intro hdr;
    V.same_hdr g0 g1 a;
    V.same_hdr g0 g1 x;
    V.write_one g1 a (x <: U64.t);
    V.same_hdr g1 (gw g) a;
    V.same_hdr g1 (gw g) bb;
    V.same_hdr g1 (gw g) x;
    let bw (b: hp_addr)
      : Lemma (requires U64.v bb <= U64.v b /\ U64.v b < U64.v bb + Wt.wzL * 8)
              (ensures read_word (gw g) b == 0UL)
      = away g b;
        recolour_word bb g0 Header.Gray b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires bw)
#pop-options

/// ---------------------------------------------------------------------------
/// 3. The hand-over: scan A, then B
/// ---------------------------------------------------------------------------

let ga1 (g: heap) : GTot heap = makeBlack (oa g) (gw g)
let gh (g: heap) : GTot heap = makeBlack (ob g) (ga1 g)

let spa (g: heap) (k: nat) : GTot MP.scan_pos = { MP.cur = (oa g <: U64.t); MP.fld = k }
let spb (g: heap) (k: nat) : GTot MP.scan_pos = { MP.cur = (ob g <: U64.t); MP.fld = k }

/// A's one field, N, is black: scanning it changes nothing.
#push-options "--z3rlimit 30"
let a_field (g: heap)
  : Lemma (requires V.roomy)
          (ensures HG.get_field (gw g) (oa g) 1UL == (n1 g <: U64.t) /\
                   S.scan_field (gw g) (oa g) 1UL == gw g)
  = gw_facts g;
    hd_address_spec (oa g);
    obj_pointer (gw g) (n1 g);
    resolve_non_infix (n1 g) (gw g);
    Mark.colors_exclusive (n1 g) (gw g)
#pop-options

let move_a1 (g: heap)
  : Lemma (requires V.roomy) (ensures S.mark_move (gw g) MP.scan_none (gw g) (spa g 1))
  = gw_facts g;
    FStar.Classical.exists_intro
      (fun (x: obj_addr) -> MP.scan_none.MP.cur == 0UL /\ S.scan_target (gw g) x /\
                         gw g == gw g /\ spa g 1 == { MP.cur = x; MP.fld = 1 })
      (oa g)

let move_a2 (g: heap)
  : Lemma (requires V.roomy) (ensures S.mark_move (gw g) (spa g 1) (gw g) (spa g 2))
  = gw_facts g;
    a_field g;
    assert (U64.uint_to_t 1 == 1UL);
    FStar.Classical.exists_intro
      (fun (x: obj_addr) ->
         x == (spa g 1).MP.cur /\ S.scan_target (gw g) x /\ 1 <= (spa g 1).MP.fld /\
         (spa g 1).MP.fld <= U64.v (wosize_of_object x (gw g)) /\
         gw g == S.scan_field (gw g) x (U64.uint_to_t (spa g 1).MP.fld) /\
         spa g 2 == { spa g 1 with MP.fld = (spa g 1).MP.fld + 1 })
      (oa g)

let move_a3 (g: heap)
  : Lemma (requires V.roomy) (ensures S.mark_move (gw g) (spa g 2) (ga1 g) MP.scan_none)
  = gw_facts g;
    FStar.Classical.exists_intro
      (fun (x: obj_addr) ->
         Seq.mem x (objects zero_addr (gw g)) /\ is_gray x (gw g) /\ MP.all_scanned (gw g) (spa g 2) x /\
         ga1 g == makeBlack x (gw g) /\ MP.scan_none == MP.blackened_pos (spa g 2) x)
      (oa g)

/// After A is blackened: B grey, with its fields 0.
#push-options "--z3rlimit 30"
let ga1_facts (g: heap)
  : Lemma (requires V.roomy)
          (ensures (forall (y: obj_addr). Seq.mem y (objects zero_addr (ga1 g)) <==> Seq.mem y (objects zero_addr (gw g))) /\
                   (forall (y: obj_addr). y =!= oa g ==> read_word (ga1 g) (hd_address y) == read_word (gw g) (hd_address y)) /\
                   is_black (oa g) (ga1 g) /\
                   Seq.mem (ob g) (objects zero_addr (ga1 g)) /\ is_gray (ob g) (ga1 g) /\
                   ~(is_no_scan (ob g) (ga1 g)) /\ U64.v (wosize_of_object (ob g) (ga1 g)) == Wt.wzL /\
                   read_word (ga1 g) (oa g <: hp_addr) == (n1 g <: U64.t) /\
                   (forall (b: hp_addr). U64.v (ob g) <= U64.v b /\ U64.v b < U64.v (ob g) + Wt.wzL * 8 ==>
                      read_word (ga1 g) b == 0UL))
  = let a = oa g in
    let bb = ob g in
    let g0 = gw g in
    gw_facts g;
    makeBlack_eq a g0;
    color_change_preserves_objects g0 a Header.Black;
    makeBlack_is_black a g0;
    hd_address_spec a; hd_address_spec bb;
    let hdr (y: obj_addr) : Lemma (y <> a ==> read_word (ga1 g) (hd_address y) == read_word g0 (hd_address y))
      = if y <> a then begin hd_address_spec y; recolour_word a g0 Header.Black (hd_address y) end
    in
    FStar.Classical.forall_intro hdr;
    V.same_hdr g0 (ga1 g) bb;
    recolour_word a g0 Header.Black (a <: hp_addr);
    let bw (b: hp_addr)
      : Lemma (requires U64.v bb <= U64.v b /\ U64.v b < U64.v bb + Wt.wzL * 8)
              (ensures read_word (ga1 g) b == 0UL)
      = away g b;
        recolour_word a g0 Header.Black b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires bw)
#pop-options

/// B's fields are 0.
#push-options "--z3rlimit 30"
let b_field (g: heap) (k: U64.t{U64.v k >= 1})
  : Lemma (requires V.roomy /\ U64.v k <= Wt.wzL)
          (ensures HG.get_field (ga1 g) (ob g) k == 0UL /\ S.scan_field (ga1 g) (ob g) k == ga1 g)
  = ga1_facts g;
    V.not_pointer_zero ();
    hd_address_spec (ob g);
    let hd = hd_address (ob g) in
    Wt.sizes ();
    assert_norm (8 * pow2 54 < pow2 64);
    if U64.v hd + U64.v mword * U64.v k + U64.v mword <= heap_size then begin
      let m = U64.mul mword k in
      assert (U64.v m == 8 * U64.v k);
      let fa = U64.add hd m in
      assert (U64.v fa == U64.v hd + 8 * U64.v k);
      assert (U64.v hd % 8 == 0);
      FStar.Math.Lemmas.lemma_mod_plus (U64.v hd) (U64.v k) 8;
      assert (U64.v fa % 8 == 0);
      let fb : hp_addr = fa in
      assert (U64.v (ob g) <= U64.v fb /\ U64.v fb < U64.v (ob g) + Wt.wzL * 8);
      assert (read_word (ga1 g) fb == 0UL)
    end
#pop-options

let move_b1 (g: heap)
  : Lemma (requires V.roomy) (ensures S.mark_move (ga1 g) MP.scan_none (ga1 g) (spb g 1))
  = ga1_facts g;
    FStar.Classical.exists_intro
      (fun (x: obj_addr) -> MP.scan_none.MP.cur == 0UL /\ S.scan_target (ga1 g) x /\
                         ga1 g == ga1 g /\ spb g 1 == { MP.cur = x; MP.fld = 1 })
      (ob g)

/// The moves over B's fields `k .. wzL`.
#push-options "--fuel 1 --z3rlimit 30"
let rec scan_b (g: heap) (k: nat)
  : Lemma (requires V.roomy /\ 1 <= k /\ k <= Wt.wzL + 1)
          (ensures S.mark_steps (ga1 g) (spb g k) (ga1 g) (spb g (Wt.wzL + 1)))
          (decreases (Wt.wzL + 1 - k))
  = if k = Wt.wzL + 1 then S.mark_steps_refl (ga1 g) (spb g k)
    else begin
      assert (k <= Wt.wzL);
      Wt.sizes ();
      assert_norm (pow2 54 < pow2 64);
      assert (U64.v (U64.uint_to_t k) == k);
      b_field g (U64.uint_to_t k);
      ga1_facts g;
      FStar.Classical.exists_intro
        (fun (x: obj_addr) ->
           x == (spb g k).MP.cur /\ S.scan_target (ga1 g) x /\ 1 <= (spb g k).MP.fld /\
           (spb g k).MP.fld <= U64.v (wosize_of_object x (ga1 g)) /\
           ga1 g == S.scan_field (ga1 g) x (U64.uint_to_t (spb g k).MP.fld) /\
           spb g (k + 1) == { spb g k with MP.fld = (spb g k).MP.fld + 1 })
        (ob g);
      S.mark_steps_move (ga1 g) (ga1 g) (spb g k) (spb g (k + 1));
      scan_b g (k + 1);
      S.mark_steps_trans (ga1 g) (ga1 g) (ga1 g) (spb g k) (spb g (k + 1)) (spb g (Wt.wzL + 1))
    end
#pop-options

let move_b2 (g: heap)
  : Lemma (requires V.roomy) (ensures S.mark_move (ga1 g) (spb g (Wt.wzL + 1)) (gh g) MP.scan_none)
  = ga1_facts g;
    FStar.Classical.exists_intro
      (fun (x: obj_addr) ->
         Seq.mem x (objects zero_addr (ga1 g)) /\ is_gray x (ga1 g) /\
         MP.all_scanned (ga1 g) (spb g (Wt.wzL + 1)) x /\
         gh g == makeBlack x (ga1 g) /\ MP.scan_none == MP.blackened_pos (spb g (Wt.wzL + 1)) x)
      (ob g)

/// **The mark moves** of the hand-over.
let marks (g: heap)
  : Lemma (requires V.roomy) (ensures S.mark_steps (gw g) MP.scan_none (gh g) MP.scan_none)
  = move_a1 g; move_a2 g; move_a3 g; move_b1 g; scan_b g 1; move_b2 g;
    S.mark_steps_move (gw g) (gw g) MP.scan_none (spa g 1);
    S.mark_steps_snoc (gw g) (gw g) (gw g) MP.scan_none (spa g 1) (spa g 2);
    S.mark_steps_snoc (gw g) (gw g) (ga1 g) MP.scan_none (spa g 2) MP.scan_none;
    S.mark_steps_snoc (gw g) (ga1 g) (ga1 g) MP.scan_none MP.scan_none (spb g 1);
    S.mark_steps_trans (gw g) (ga1 g) (ga1 g) MP.scan_none (spb g 1) (spb g (Wt.wzL + 1));
    S.mark_steps_snoc (gw g) (ga1 g) (gh g) MP.scan_none (spb g (Wt.wzL + 1)) MP.scan_none

/// The hand-over heap: A and B black; every other header as after the
/// allocation.
#push-options "--z3rlimit 40"
let gh_facts (g: heap)
  : Lemma (requires V.roomy)
          (ensures (forall (y: obj_addr). Seq.mem y (objects zero_addr (gh g)) <==> Seq.mem y (objects zero_addr (gz g))) /\
                   (forall (y: obj_addr). Seq.mem y (objects zero_addr (gz g)) /\ y =!= oa g /\ y =!= ob g ==>
                      read_word (gh g) (hd_address y) == read_word (gz g) (hd_address y)) /\
                   Seq.mem (oa g) (objects zero_addr (gh g)) /\ is_black (oa g) (gh g) /\
                   Seq.mem (ob g) (objects zero_addr (gh g)) /\ is_black (ob g) (gh g) /\
                   U64.v (wosize_of_object (oa g) (gh g)) == 1 /\
                   ~(is_closure (oa g) (gh g)) /\ ~(is_no_scan (oa g) (gh g)) /\
                   read_word (gh g) (oa g <: hp_addr) == (n1 g <: U64.t))
  = let a = oa g in
    let bb = ob g in
    let g0 = ga1 g in
    gw_facts g;
    ga1_facts g;
    makeBlack_eq a (gw g);
    color_preserves_wosize a (gw g) Header.Black;
    color_change_preserves_is_closure a a (gw g) Header.Black;
    color_preserves_is_no_scan a (gw g) Header.Black;
    makeBlack_eq bb g0;
    color_change_preserves_objects g0 bb Header.Black;
    makeBlack_is_black bb g0;
    hd_address_spec a; hd_address_spec bb;
    let hdr (y: obj_addr) : Lemma (y <> bb ==> read_word (gh g) (hd_address y) == read_word g0 (hd_address y))
      = if y <> bb then begin hd_address_spec y; recolour_word bb g0 Header.Black (hd_address y) end
    in
    FStar.Classical.forall_intro hdr;
    V.same_hdr g0 (gh g) a;
    away g (a <: hp_addr);
    recolour_word bb g0 Header.Black (a <: hp_addr)
#pop-options

/// Every block in use in the darkened heap but A, B and N keeps its header
/// to the hand-over.
#push-options "--z3rlimit 30"
let other_gh (g: heap) (y: obj_addr)
  : Lemma (requires V.roomy /\ Seq.mem y (objects zero_addr (gd g)) /\ ~(is_blue y (gd g)) /\
                    y <> oa g /\ y <> ob g)
          (ensures y <> n1 g /\ Seq.mem y (objects zero_addr (gh g)) /\
                   read_word (gh g) (hd_address y) == read_word (h g) (hd_address y))
  = mal_ok g;
    keep_gz g y;
    gh_facts g;
    gd_colours g y
#pop-options

/// Nothing is grey at the hand-over; C is still white.
#push-options "--z3rlimit 40"
let gh_no_grey (g: heap)
  : Lemma (requires V.roomy)
          (ensures Mark.noGreyObjects (gh g) /\ ~(is_black (oc g) (gh g)))
  = let a = oa g in
    let bb = ob g in
    let x = n1 g in
    base g;
    gd_facts g;
    gh_facts g;
    mal_ok g;
    gz_ok g;
    V.write_one (gb g) x 0UL;
    Mark.colors_exclusive a (gh g);
    Mark.colors_exclusive bb (gh g);
    let ng (y: obj_addr) : Lemma (requires Seq.mem y (objects zero_addr (gh g))) (ensures ~(is_gray y (gh g)))
      = if y = a || y = bb then ()
        else begin
          V.same_hdr (gz g) (gh g) y;
          V.same_hdr (gb g) (gz g) y;
          if y = x then Mark.colors_exclusive x (gz g)
          else if is_gray y (gb g) then begin
            Mark.colors_exclusive y (gb g);
            assert (in_use (MPA.free_or_new x) (gb g) y);
            assert (in_use free_stw (gd g) y);
            keep_gz g y;
            V.same_hdr (gd g) (gb g) y;
            gd_colours g y
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ng);
    let c = oc g in
    gd_colours g c;
    V.same_hdr (h g) (gd g) c;
    other_gh g c;
    V.same_hdr (h g) (gh g) c;
    Mark.colors_exclusive c (h g)
#pop-options

/// The collector's state at the hand-over, and the sweep's precondition.
let gh_ok (g: heap)
  : Lemma (requires V.roomy)
          (ensures PM.pmark_ok V.m0 (gh g) (sb g) MP.scan_none /\
                   SA.sweep_ready (gh g) (SS.start_sweep (sb g)) /\ SA.mark_done (gh g))
  = gw_ok g;
    marks g;
    gh_no_grey g;
    CS.mark_steps_inv (sb g) (gw g) MP.scan_none (gh g) MP.scan_none;
    S.mark_steps_inv (gw g) (gh g) MP.scan_none MP.scan_none (GMM.nursery_refs V.m0);
    CS.handover_ready (gh g) (sb g) (GMM.nursery_refs V.m0) MP.scan_none

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

let s0 (g: heap) : GTot pstate = SS.start_sweep (sb g)

/// C's page (A's): a pool page of A's class.
let c_prop (g: heap) (j: nat{j < n_pages}) : prop =
  exists (k: nat). k < n_slots Wt.cA /\ Wt.kind_of (st g) j == Pool Wt.cA /\ U64.v (oc g) == slot_obj j Wt.cA k

let jc (g: heap{Wt.big_enough}) : GTot (j: nat{j < n_pages /\ c_prop g j}) =
  MSV.c_page g;
  FStar.IndefiniteDescription.indefinite_description_ghost (j: nat{j < n_pages}) (fun j -> c_prop g j)

let kc (g: heap{Wt.big_enough}) : GTot (k: nat{k < n_slots Wt.cA /\ U64.v (oc g) == slot_obj (jc g) Wt.cA k}) =
  FStar.IndefiniteDescription.indefinite_description_ghost nat
    (fun k -> k < n_slots Wt.cA /\ U64.v (oc g) == slot_obj (jc g) Wt.cA k)

/// C's page and B's run at the sweep's start: unswept.
let at_start (g: heap)
  : Lemma (requires V.roomy)
          (ensures (entry (s0 g).pm (jc g)).kind == Pool Wt.cA /\ not (entry (s0 g).pm (jc g)).swept /\
                   (entry (s0 g).pm (V.i0 g)).kind == LargeHead Wt.kL /\ not (entry (s0 g).pm (V.i0 g)).swept)
  = Wt.step3 g;
    mal_ok g;
    FStar.Classical.forall_intro (SS.clear_entry (sb g).pm)

/// 5. C's page swept.
let g1 (g: heap{V.roomy}) : GTot heap = fst (SA.step (gh g) (s0 g) (jc g))
let s1 (g: heap{V.roomy}) : GTot pstate = snd (SA.step (gh g) (s0 g) (jc g))

let step1 (g: heap)
  : Lemma (requires V.roomy)
          (ensures SA.sweep_ready (gh g) (s0 g) /\ SA.mark_done (gh g) /\
                   pages_ok_sw (gh g) (s0 g) /\ pages_ok_sw (g1 g) (s1 g) /\
                   ((entry (s1 g).pm (jc g)).kind == Free \/ has_free_slot (s1 g).pm Wt.cA (jc g)) /\
                   (entry (s1 g).pm (V.i0 g)).kind == LargeHead Wt.kL /\ not (entry (s1 g).pm (V.i0 g)).swept /\
                   MS2.use_kept (gh g) (g1 g) (s0 g).pm (s1 g).pm)
  = gh_ok g;
    gh_no_grey g;
    MS2.sw_start (gh g) (s0 g);
    at_start g;
    MSV.step1_abs (gh g) (s0 g) (jc g) (kc g) (oc g) (V.i0 g) Wt.kL;
    MS2.step_sw (gh g) (s0 g) (jc g)

/// 6. An allocation, O, its field cleared.
let alloc1 (g: heap{V.roomy}) : GTot (heap & pstate & U64.t) = PA.alloc I.Sweeping (g1 g) (s1 g) Wt.wzS
let ga (g: heap{V.roomy}) : GTot heap = let (a, _, _) = alloc1 g in a
let s2 (g: heap{V.roomy}) : GTot pstate = let (_, s, _) = alloc1 g in s
let oo (g: heap{V.roomy}) : GTot obj_addr = Wt.as_obj (let (_, _, o) = alloc1 g in o)
let g2 (g: heap{V.roomy}) : GTot heap = B.zeros (ga g) (U64.v (oo g)) Wt.wzS

#push-options "--z3rlimit 40"
let alloc_ok (g: heap)
  : Lemma (requires V.roomy)
          (ensures alloc1 g == (ga g, s2 g, (oo g <: U64.t)) /\
                   I.fields_written_with (free_sw (s1 g).pm) (ga g) (g2 g) (oo g) /\
                   pages_ok_sw (g2 g) (s2 g) /\
                   Seq.mem (oo g) (objects zero_addr (ga g)) /\
                   in_use (free_sw (s2 g).pm) (ga g) (oo g) /\ ~(in_use (free_sw (s1 g).pm) (g1 g) (oo g)) /\
                   (forall (y: obj_addr). in_use (free_sw (s2 g).pm) (ga g) y ==
                                     (in_use (free_sw (s1 g).pm) (g1 g) y || y = oo g)) /\
                   Th.others_unchanged (g1 g) (ga g) /\
                   (entry (s2 g).pm (V.i0 g)).kind == LargeHead Wt.kL /\ not (entry (s2 g).pm (V.i0 g)).swept)
  = step1 g;
    at_start g;
    MSV.alloc_abs (g1 g) (s1 g) (jc g) (V.i0 g) Wt.kL;
    MA.alloc_sw_ok (g1 g) (s1 g) Wt.wzS
#pop-options

/// Clearing O's field keeps every other object, its header and its fields.
#push-options "--z3rlimit 30"
let zeros_keep (g: heap) (y: obj_addr)
  : Lemma (requires V.roomy /\ Seq.mem y (objects zero_addr (ga g)) /\ y <> oo g)
          (ensures Seq.mem y (objects zero_addr (g2 g)) /\
                   read_word (g2 g) (hd_address y) == read_word (ga g) (hd_address y) /\
                   (forall (b: hp_addr). U64.v y <= U64.v b /\ U64.v b < F.fields_end (ga g) y ==>
                      read_word (g2 g) b == read_word (ga g) b))
  = alloc_ok g;
    assert (F.fctx (ga g) (g2 g) (oo g));
    F.obj_same (ga g) (g2 g) (oo g) y;
    F.other_apart (ga g) (oo g) y
#pop-options

/// O, after its field is cleared: a block in use, at its address.
#push-options "--z3rlimit 30"
let oo_g2 (g: heap)
  : Lemma (requires V.roomy)
          (ensures Seq.mem (oo g) (objects zero_addr (g2 g)) /\ in_use (free_sw (s2 g).pm) (g2 g) (oo g) /\
                   is_pointer (oo g <: U64.t) /\ resolve_object (oo g) (g2 g) == oo g /\
                   infix_addr_wf (g2 g) (objects zero_addr (g2 g)) (oo g))
  = let x = oo g in
    alloc_ok g;
    assert (F.fctx (ga g) (g2 g) x);
    F.obj_same (ga g) (g2 g) x x;
    V.same_hdr (ga g) (g2 g) x;
    obj_pointer (g2 g) x;
    pages_ok_sw_elim (g2 g) (s2 g);
    wf_with_parts ();
    assert (no_infix_block (g2 g));
    resolve_non_infix x (g2 g);
    infix_addr_wf_intro (g2 g) (objects zero_addr (g2 g)) x
#pop-options

/// Two headers with the same tag and size give the same closure, no-scan
/// and size facts.
let same_tag (g g': heap) (y: obj_addr)
  : Lemma (requires getTag (read_word g' (hd_address y)) == getTag (read_word g (hd_address y)) /\
                    getWosize (read_word g' (hd_address y)) == getWosize (read_word g (hd_address y)))
          (ensures is_closure y g' == is_closure y g /\ is_no_scan y g' == is_no_scan y g /\
                   wosize_of_object y g' == wosize_of_object y g)
  = tag_of_object_spec y g; tag_of_object_spec y g';
    is_closure_spec y g; is_closure_spec y g';
    is_no_scan_spec y g; is_no_scan_spec y g';
    wosize_of_object_spec y g; wosize_of_object_spec y g'

/// A through the sweep of its page and the allocation: in use, of one
/// field, not a closure, with N in its field.
#push-options "--z3rlimit 40"
let a_g2 (g: heap)
  : Lemma (requires V.roomy)
          (ensures Seq.mem (oa g) (objects zero_addr (g2 g)) /\ in_use (free_sw (s2 g).pm) (g2 g) (oa g) /\
                   ~(is_blue (oa g) (g2 g)) /\
                   ~(is_closure (oa g) (g2 g)) /\ ~(is_no_scan (oa g) (g2 g)) /\
                   U64.v (wosize_of_object (oa g) (g2 g)) == 1 /\
                   read_word (g2 g) (oa g <: hp_addr) == (n1 g <: U64.t) /\ oa g <> oo g)
  = let a = oa g in
    let fa : hp_addr = a in
    gh_facts g;
    step1 g;
    alloc_ok g;
    Mark.colors_exclusive a (gh g);
    (* in use mid-sweep: black *)
    assert (in_use (free_sw (s0 g).pm) (gh g) a);
    (* the sweep of A's page keeps A's block *)
    assert (in_use (free_sw (s1 g).pm) (g1 g) a);
    assert (SPI.same_block (gh g) (g1 g) (hd_address a));
    SPM.in_body_block (gh g) a fa;
    same_tag (gh g) (g1 g) a;
    (* the allocation keeps it *)
    assert (a <> oo g);
    assert (read_word (ga g) (hd_address a) == read_word (g1 g) (hd_address a));
    assert (read_word (ga g) fa == read_word (g1 g) fa);
    V.same_hdr (g1 g) (ga g) a;
    (* clearing O's field keeps it *)
    zeros_keep g a;
    V.same_hdr (ga g) (g2 g) a
#pop-options

/// 7. The program write mid-sweep: A's field gets a pointer to O.
let g3 (g: heap{V.roomy}) : GTot heap = write_word (g2 g) (oa g <: hp_addr) (oo g <: U64.t)

/// **Its hypotheses, and the mid-sweep invariant after it**, discharged by
/// `Cycle.Write.swrite_keeps`: a program write at `free_sw`, of a pointer
/// to a block in use, into a block older than the sweep.
#push-options "--z3rlimit 40"
let swrite_ok (g: heap)
  : Lemma (requires V.roomy)
          (ensures pages_ok_sw (g2 g) (s2 g) /\
                   SPM.program_write (free_sw (s2 g).pm) (g2 g) (oa g) (oa g <: hp_addr) (oo g <: U64.t) /\
                   Seq.mem (oa g) (objects zero_addr (g2 g)) /\ ~(is_blue (oa g) (g2 g)) /\
                   SPM.in_body (g2 g) (oa g) (oa g <: hp_addr) /\
                   read_word (g2 g) (oa g <: hp_addr) == (n1 g <: U64.t) /\
                   read_word (g3 g) (oa g <: hp_addr) == (oo g <: U64.t) /\
                   pages_ok_sw (g3 g) (s2 g))
  = alloc_ok g;
    a_g2 g;
    oo_g2 g;
    read_write_same (g2 g) (oa g <: hp_addr) (oo g <: U64.t);
    PW.swrite_keeps (g2 g) (s2 g) (oa g) (oa g <: hp_addr) (oo g <: U64.t)
#pop-options

/// 8. The rest of the sweep, and the end.
let gf (g: heap{V.roomy}) : GTot heap = fst (SA.sweep_from (g3 g) (s2 g) 0)
let sf (g: heap{V.roomy}) : GTot pstate = snd (SA.sweep_from (g3 g) (s2 g) 0)

let rest_ends (g: heap)
  : Lemma (requires V.roomy)
          (ensures pages_ok_sw (gf g) (sf g) /\ PMP.all_swept (sf g))
  = swrite_ok g;
    pages_ok_sw_elim (g3 g) (s2 g);
    if n_pages > 0 then assert (cont_ok (s2 g).pm 0);
    MS2.sweep_from_sw (g3 g) (s2 g) 0

/// The addresses the run hands out: N while marking, O mid-sweep.
let since_d (g: heap{V.roomy}) : obj_addr -> prop =
  GC_.union (since_m g) (SPC.with_new SPC.nothing_new (oo g <: U64.t))

/// **The run.**
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let run_dark (g: heap{V.roomy}) : GTot (PC.pcycle (h g) (rs g) (gf g) (sf g) I.Idle (since_d g)) =
  start_pre g;
  darkened_a g;
  gd_ok g;
  mal_ok g;
  gz_ok g;
  n1_storable g;
  write_ok g;
  gw_ok g;
  marks g;
  gh_no_grey g;
  step1 g;
  at_start g;
  alloc_ok g;
  swrite_ok g;
  rest_ends g;
  let rm0 : PM.pmarking (h g) (rs g) (MStart.darkened (h g) (rs g)) (st g) MP.scan_none SPC.nothing_new =
    PM.PStart V.m0 (st g) () in
  let rm1 : PM.pmarking (h g) (rs g) (gz g) (sb g) MP.scan_none (since_m g) =
    PM.PAlloc rm0 V.m0 Wt.wzS (gb g) (sb g) (n1 g) () (gz g) (iw g) () in
  let rm2 : PM.pmarking (h g) (rs g) (gw g) (sb g) MP.scan_none (since_m g) =
    PM.PWrite rm1 V.m0 (oa g) (oa g <: hp_addr) (n1 g <: U64.t) () in
  let r0 : PS.psweep (gh g) (gh g) (s0 g) I.Sweeping SPC.nothing_new = PS.SStart (s0 g) () in
  let r1 : PS.psweep (gh g) (g1 g) (s1 g) I.Sweeping SPC.nothing_new = PS.SStep r0 (jc g) () in
  let r2 : PS.psweep (gh g) (g2 g) (s2 g) I.Sweeping (SPC.with_new SPC.nothing_new (oo g <: U64.t)) =
    PS.SAlloc r1 Wt.wzS (ga g) (s2 g) (oo g) () (g2 g) () in
  let r3 : PS.psweep (gh g) (g3 g) (s2 g) I.Sweeping (SPC.with_new SPC.nothing_new (oo g <: U64.t)) =
    PS.SWrite r2 (oa g) (oa g <: hp_addr) (oo g <: U64.t) () in
  let r4 = V.rest r3 0 in
  let r5 : PS.psweep (gh g) (gf g) (sf g) I.Idle (SPC.with_new SPC.nothing_new (oo g <: U64.t)) =
    PS.SEnd r4 () in
  assert (PC.sweep_start_st r0 == s0 g);
  assert (PC.sweep_start_st r1 == PC.sweep_start_st r0);
  assert (PC.sweep_start_st r2 == PC.sweep_start_st r1);
  assert (PC.sweep_start_st r3 == PC.sweep_start_st r2);
  assert (PC.sweep_start_st r5 == PC.sweep_start_st r4);
  PC.PSweep rm2 V.m0 (gh g) MP.scan_none () r5 ()
#pop-options

/// ---------------------------------------------------------------------------
/// It is not trivial
/// ---------------------------------------------------------------------------

/// An object with one field, a pointer to `t`, points to `t`.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let one_field_points (h0: heap) (a t: obj_addr)
  : Lemma (requires wosize_of_object a h0 == 1UL /\ read_word h0 (a <: hp_addr) == (t <: U64.t) /\
                    is_pointer (t <: U64.t))
          (ensures points_to h0 a t)
  = assert (U64.mul_mod 0UL mword == 0UL);
    assert (U64.add_mod a 0UL == a);
    hd_address_spec t;
    assert (is_pointer_to (t <: U64.t) t);
    assert (points_to h0 a t == exists_field_pointing_to_unchecked h0 a 1UL t)
#pop-options

/// A's one field points to B at the start: an edge.
let a_to_b (g: heap)
  : Lemma (requires Wt.big_enough) (ensures MP.field_edge (h g) (oa g) (ob g))
  = let h0 = h g in
    let a = oa g in
    let bb = ob g in
    base g;
    wosize_of_object_bound a h0;
    assert (wosize_of_object a h0 == 1UL);
    obj_pointer h0 bb;
    one_field_points h0 a bb;
    resolve_non_infix bb h0

/// **A and B are reachable at the start**: A is the root, B its field's
/// target.
#push-options "--z3rlimit 30"
let reach_ab (g: heap)
  : Lemma (requires Wt.big_enough)
          (ensures GMC.reachable_at_start (h g) (rs g) (oa g) /\ GMC.reachable_at_start (h g) (rs g) (ob g))
  = let h0 = h g in
    let refs = GMM.root_refs h0 (rs g) in
    base g;
    a_root g;
    GMC.reachable_at_start_eq h0 (rs g);
    let _ = FStar.Seq.Properties.mem_index (oa g <: U64.t) (rs g) in
    assert (refs (oa g));
    MPC.reachable_outside_refs h0 refs (oa g);
    a_to_b g;
    let p : obj_addr -> prop = fun _ -> True in
    Within.reach_within_edge (MP.field_edge h0) p (oa g) (ob g);
    assert (MPC.reachable h0 refs (ob g))
#pop-options

/// **The run is not trivial**: B is reachable at the start, and white when
/// the barrier overwrites A's pointer to it, grey after; A's field goes
/// from a pointer to B to a pointer to N, and, mid-sweep, to a pointer to
/// O; N was not a block in use when handed out, nor O; both are handed out.
#push-options "--z3rlimit 40"
let run_dark_nontrivial (g: heap)
  : Lemma (requires V.roomy)
          (ensures GMC.reachable_at_start (h g) (rs g) (oa g) /\
                   GMC.reachable_at_start (h g) (rs g) (ob g) /\
                   read_word (gz g) (oa g <: hp_addr) == (ob g <: U64.t) /\ is_pointer (ob g <: U64.t) /\
                   is_white (ob g) (gz g) /\ is_gray (ob g) (gw g) /\
                   read_word (gw g) (oa g <: hp_addr) == (n1 g <: U64.t) /\ is_pointer (n1 g <: U64.t) /\
                   read_word (g2 g) (oa g <: hp_addr) == (n1 g <: U64.t) /\
                   read_word (g3 g) (oa g <: hp_addr) == (oo g <: U64.t) /\ is_pointer (oo g <: U64.t) /\
                   ~(Seq.mem (n1 g) (objects zero_addr (gd g)) /\ ~(is_blue (n1 g) (gd g))) /\
                   ~(in_use (free_sw (s1 g).pm) (g1 g) (oo g)) /\
                   since_d g (n1 g) /\ since_d g (oo g))
  = reach_ab g;
    ab_gz g;
    gz_ok g;
    obj_pointer (gz g) (ob g);
    obj_pointer (gz g) (n1 g);
    gw_facts g;
    mal_ok g;
    alloc_ok g;
    oo_g2 g;
    swrite_ok g
#pop-options

/// **The theorems on it**: A and B survive the cycle -- B although the
/// program overwrote A's pointer to it while marking -- and neither is
/// handed out.
let run_dark_theorems (g: heap)
  : Lemma (requires V.roomy)
          (ensures Seq.mem (oa g) (objects zero_addr (gf g)) /\ ~(is_blue (oa g) (gf g)) /\
                   Seq.mem (ob g) (objects zero_addr (gf g)) /\ ~(is_blue (ob g) (gf g)) /\
                   ~(since_d g (oa g)) /\ ~(since_d g (ob g)))
  = reach_ab g;
    PC.cycle_survives (run_dark g)
