/// ---------------------------------------------------------------------------
/// GC.SPOT.MarkPhaseCycleAlloc - a run of the marking phase that allocates
/// ---------------------------------------------------------------------------
///
/// A run of the marking phase (`GC.Gen.MarkPhase.Cycle.marking`) with an
/// allocation, so that the run's new addresses are not empty, on the heap
/// of `GC.SPOT.CycleHeap`:
///
///     A -> B      B      U -> A      C          roots [A; C], all white,
///                                               then a free block
///
/// in the idle collector's state with an empty nursery.  The run:
///
///   1. start the cycle (`Start`): the roots `A` and `C` darkened;
///   2. allocate a one-field object while marking (`Alloc`): the free block
///      is big enough, so the object is real, and black;
///   3. initialise its field to 0 (`init_writes`, one write into its body):
///      an immediate, so a value in the snapshot.
///
/// The run fixes `since` to the one allocated object, so the cycle's
/// snapshot is `A`, `B`, `C` (reachable from the roots) and the new object,
/// and not `U` (`CycleHeap.u_unreachable`; the new object is a block that
/// was not one in use, so it is not `U`).  What the run carries
/// (`MC.mark_run_account`) then says, at its end (`mark_alloc_spot`):
///
///   * `U` is a white block: nothing outside the snapshot was greyed, and
///     nothing will be -- `U` points at `A`, but nothing reachable points at
///     `U`;
///   * `A`, `B` and `C` are blocks that are not free, and each, if white, is
///     one the marker will reach (snapshot-at-the-beginning): in particular
///     `B`, which no root names, is reached through `A`.

module GC.SPOT.MarkPhaseCycleAlloc

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph.Within
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module MPA = GC.Spec.MarkPhase.Alloc
module MPC = GC.Spec.MarkPhase.Completeness
module GI = GC.Gen.Incremental
module GMC = GC.Gen.MarkPhase.Completeness
module GMS = GC.Gen.MarkPhase.Safety
module MStart = GC.Gen.MarkPhase.Start
module MC = GC.Gen.MarkPhase.Cycle
module SPC = GC.Spec.SweepPhase.Completeness
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Oom = GC.Spec.Allocator.Oom
module FLA = GC.Spec.FreeList.Ascending
module GenInv = GC.Gen.HeapInvariant
module MPH = GC.SPOT.MarkPhaseHeap
module CH = GC.SPOT.CycleHeap
module InfixPre = GC.SPOT.InfixPre
module SPF = GC.SPOT.SweepPhasePendingFree

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

let g0 (r: unit{MPH.room}) : heap = CH.h0 r
let rs (r: unit{MPH.room}) : seq U64.t = CH.roots0 r
let fp0 (r: unit{MPH.room}) : U64.t = CH.fp0 r

/// The darkened heap.
let gd (r: unit{MPH.room}) : GTot heap = MStart.darkened (g0 r) (rs r)

/// `start_cycle`'s precondition, and the collector's state after it.
let start_facts (r: unit{MPH.room})
  : Lemma (MC.start_pre CH.minor0 (g0 r) (fp0 r) (rs r) /\
           GI.phase_shape CH.minor0 (gd r) (fp0 r) Ph.Marking MP.scan_none)
  = CH.shape r;
    InfixPre.spot_infix_minor_is_reset CH.minor0;
    CH.roots_valid_darkening r;
    MStart.mark_start_shape CH.minor0 (g0 r) (fp0 r) (rs r)

/// ---------------------------------------------------------------------------
/// The allocation and the initialisation
/// ---------------------------------------------------------------------------

/// Allocate one field, tag 0, while marking.
let ra (r: unit{MPH.room}) : GTot SA.alloc_result = AC.alloc_phase (gd r) (fp0 r) Ph.Marking 1 0UL
let obj (r: unit{MPH.room}) : GTot U64.t = (ra r).SA.obj_out
let ga (r: unit{MPH.room}) : GTot heap = (ra r).SA.heap_out
let fpa (r: unit{MPH.room}) : GTot U64.t = (ra r).SA.fp_out

/// Its field set to 0.
let gw (r: unit{MPH.room}) : GTot heap =
  if GC.Spec.FusedSweep.is_obj (obj r) then write_word (ga r) (obj r <: hp_addr) 0UL else ga r

/// The allocation succeeds: the free block has a word; the object is a
/// block of one field that was not a block in use, and every block in use
/// stays one.
#push-options "--z3rlimit 40"
let alloc_facts (r: unit{MPH.room})
  : Lemma (obj r <> 0UL /\ GC.Spec.FusedSweep.is_obj (obj r) /\
           (let o : obj_addr = obj r in
            Seq.mem o (objects zero_addr (ga r)) /\
            U64.v (wosize_of_object o (ga r)) == 1 /\
            ~(in_use free_stw (gd r) o) /\
            SPM.in_body (ga r) o (o <: hp_addr) /\
            gw r == write_word (ga r) (o <: hp_addr) 0UL /\
            SPM.fields_storable (MPC.outside_snapshot (MC.snapshot (g0 r) (rs r) (SPC.with_new SPC.nothing_new o))) (gw r) o /\
            (forall (y: obj_addr). in_use free_stw (gd r) y ==>
               in_use free_stw (gw r) y /\ read_word (gw r) (hd_address y) == read_word (gd r) (hd_address y))))
  = start_facts r;
    let g = gd r in
    let fp = fp0 r in
    GI.phase_shape_marking CH.minor0 g fp MP.scan_none;
    GenInv.collection_shape_with_elim Ph.Marking free_stw CH.minor0 g fp;
    GenInv.major_shape_with_elim Ph.Marking free_stw g fp;
    infix_tag_val ();
    // it does not fail: the free block of the darkened heap has a word
    if obj r = 0UL then begin
      AC.alloc_phase_fields g fp Ph.Marking 1 0UL;
      FLA.fl_ascending_valid g fp;
      FLA.fl_ascending_exact g fp;
      Oom.alloc_spec_oom_no_fit g fp 1 0UL;
      CH.shape r; CH.roots_valid_darkening r;
      GMS.start_keeps_blocks CH.minor0 (g0 r) fp (rs r);
      CH.facts r;
      MPH.free_block r CH.col0 CH.tg0;
      let f = MPH.free_obj r in
      wosize_of_object_spec f (g0 r); wosize_of_object_spec f g;
      assert (Seq.mem f (objects zero_addr g) /\ is_blue f g);
      assert (U64.v (wosize_of_object f g) >= 1)
    end;
    MPA.marking_alloc g (GC.Gen.MarkPhase.Minor.nursery_refs CH.minor0) MP.scan_none fp 1 0UL;
    let o : obj_addr = obj r in
    let a : hp_addr = o in
    let g1 = ga r in
    hd_address_spec o;
    assert (SPM.in_body g1 o a);
    let g' = write_word g1 a 0UL in
    GC.Spec.MarkPhase.Mutator.write_heads g1 o a 0UL;
    let keep (y: obj_addr)
      : Lemma (requires in_use free_stw g y)
              (ensures in_use free_stw g' y /\ read_word g' (hd_address y) == read_word g (hd_address y))
      = GC.Spec.MarkPhase.Mutator.header_kept_facts g g1 y;
        GC.Spec.MarkPhase.Mutator.header_kept_facts g1 g' y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires keep);
    wosize_of_object_spec o g1; wosize_of_object_spec o g';
    read_write_same g1 a 0UL;
    assert (SPM.field_val g' o 0 == 0UL);
    SPF.one_field_storable (MPC.outside_snapshot (MC.snapshot (g0 r) (rs r) (SPC.with_new SPC.nothing_new o))) g' o
#pop-options

/// ---------------------------------------------------------------------------
/// The run
/// ---------------------------------------------------------------------------

/// The run's new addresses: the allocated object.
let since1 (r: unit{MPH.room}) : obj_addr -> prop = SPC.with_new SPC.nothing_new (obj r)

/// **The run.**
let run (r: unit{MPH.room}) : GTot (MC.marking (g0 r) (rs r) (gw r) (fpa r) MP.scan_none (since1 r)) =
  start_facts r;
  alloc_facts r;
  infix_tag_val ();
  let o : obj_addr = obj r in
  let r0 : MC.marking (g0 r) (rs r) (gd r) (fp0 r) MP.scan_none SPC.nothing_new =
    MC.Start CH.minor0 (fp0 r) () in
  let w : MC.init_writes o (ga r) (gw r) =
    MC.Init_write (MC.Init_done (ga r)) (o <: hp_addr) 0UL (gw r) () in
  MC.Alloc r0 CH.minor0 1 0UL (ga r) (fpa r) o () (gw r) w ()

/// `B` is reachable from the roots, through `A`.
let b_reachable (r: unit{MPH.room})
  : Lemma (GMC.reachable_at_start (g0 r) (rs r) (CH.obj_b r))
  = let g = g0 r in
    GMC.reachable_at_start_eq g (rs r);
    CH.root_refs_iff r (CH.obj_a r);
    MPH.field_edge_iff r CH.col0 CH.tg0 1 (CH.obj_b r);
    reach_within_edge (MP.field_edge g) (fun _ -> True) (CH.obj_a r) (CH.obj_b r)

/// **The SPOT.**  At the end of the run the snapshot is `A`, `B`, `C` and
/// the new object, not `U`; `U` is still a white block; and `A`, `B` and `C`
/// are blocks that are not free and, if white, ones the marker will reach.
#push-options "--z3rlimit 40"
let mark_alloc_spot (r: unit{MPH.room})
  : Lemma (obj r <> 0UL /\ GC.Spec.FusedSweep.is_obj (obj r) /\
           (let g = gw r in
            let o : obj_addr = (alloc_facts r; obj r) in
            let s = MC.snapshot (g0 r) (rs r) (since1 r) in
            s (CH.obj_a r) /\ s (CH.obj_b r) /\ s (CH.obj_c r) /\ s o /\ ~(s (CH.obj_u r)) /\
            Seq.mem (CH.obj_u r) (objects zero_addr g) /\ is_white (CH.obj_u r) g /\
            (forall (x: obj_addr). x == CH.obj_a r \/ x == CH.obj_b r \/ x == CH.obj_c r ==>
               in_use free_stw g x /\ (is_white x g ==> MP.marker_will_reach g MP.scan_none x))))
  = alloc_facts r;
    start_facts r;
    let g = gw r in
    let o : obj_addr = obj r in
    let u = CH.obj_u r in
    MC.mark_run_account (run r);
    // what was reachable
    GMC.reachable_at_start_eq (g0 r) (rs r);
    CH.roots_reachable r;
    b_reachable r;
    CH.u_unreachable r;
    // `U` is a block in use, in the darkened heap and after
    CH.shape r; CH.roots_valid_darkening r; CH.facts r;
    GMS.start_keeps_blocks CH.minor0 (g0 r) (fp0 r) (rs r);
    assert (in_use free_stw (gd r) u);
    assert (in_use free_stw g u);
    // so not the new object, so not in the snapshot, so not dark
    assert (u <> o);
    Mark.color_exhaustive u g;
    Mark.colors_exclusive u g
#pop-options
