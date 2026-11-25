/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cycle.Carried - the page cycle with the page invariant
/// carried by the run
/// ---------------------------------------------------------------------------
///
/// Plan §26.  The runs of `GC.Spec.Pages.Cycle` take the page invariant at
/// every event as a hypothesis (`PM.pmark_ok`'s page part `PMP.mark_inv`,
/// `MS.pages_ok_sw`), as akhil's take `phase_shape` and `sweep_shape`.  The
/// runs here do not: **the run carries it**.  Their events take only what
/// the program and akhil's collector owe:
///
///   * marking (`cmarking`): root darkening from the page `Idle` invariant;
///     mark moves, the barrier write and the allocation each with akhil's
///     marking invariant (`MP.marking_inv`, the collector's state that is
///     not the allocator's) and his obligations word for word; the
///     allocation's initialising writes with any values he allows
///     (`SPM.fields_storable` for the snapshot);
///   * the sweep (`csweep`): the sweep's start, page steps and its end with
///     no hypothesis but "every page swept" at the end; an allocation with
///     the caller's field writes (`fields_written_with free_sw`); a write
///     that is a **program write** (`SPM.program_write (MS.free_sw st.pm)`):
///     the program cannot reach a dead object;
///   * the cycle (`ccycle`): marking, then the hand-over (akhil's marking
///     invariant, mark moves to nothing grey) and the sweep from the page
///     state marking left;
///   * plan §29: the program's allocations with any tag but the infix tag
///     (`CAllocT`, `CSAllocT`), and minor collections once the cycle is
///     idle again (`CSIMinor`).
///
/// **`ccycle_inv`**: every state of a run is in the page invariant of its
/// phase (`cinv`: `PMP.mark_inv`, `MS.pages_ok_sw`, `PA.inv I.Idle`), and
/// in akhil's account.  **`ccycle_correct`**: once a run is idle again, the
/// page `Idle` invariant holds (the next cycle may start) and akhil's
/// cycle theorems hold, word for word.
///
/// Both are derived from the theorems of `GC.Spec.Pages.Cycle` (which are
/// not changed): every run here is a run there (`to_pcycle`), whose event
/// hypotheses are the carried invariant and the event's own, discharged by
/// the page lemmas -- `Cycle.State.mark_steps_inv`, `handover_ready`,
/// `Cycle.Write.barrier_mark_inv` and `swrite_keeps`, `MidSweepStep`'s
/// `sw_start`, `step_sw` and `sw_end`, `MidSweepAlloc.alloc_sw_ok`, and the
/// allocation while marking with any initialising values (`alloc_mark_inv`,
/// plan §23.2 M-e).

module GC.Spec.Pages.Cycle.Carried

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module Ph = GC.Spec.Phase
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module S = GC.Spec.MarkPhase.Slice
module MPC = GC.Spec.MarkPhase.Completeness
module GMC = GC.Gen.MarkPhase.Completeness
module GMM = GC.Gen.MarkPhase.Minor
module MStart = GC.Gen.MarkPhase.Start
module MC = GC.Gen.MarkPhase.Cycle
module GC_ = GC.Gen.Cycle
module GB = GC.Gen.Barrier
module GI = GC.Gen.Incremental
module SPC = GC.Spec.SweepPhase.Completeness
module SPM = GC.Spec.SweepPhase.Mutator
module SPI = GC.Spec.SweepPhase.Intrinsic
module LL = GC.Spec.FusedSweep.Lossless
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module A = GC.Spec.Pages.Alloc
module AP = GC.Spec.Pages.AllocPhase
module PMP = GC.Spec.Pages.MarkPhase
module Rc = GC.Spec.Pages.Recolour
module CF = GC.Spec.Pages.ColourFacts
module B = GC.Spec.Pages.Blocks
module F = GC.Spec.Pages.Fill
module Wt = GC.Spec.Pages.Witness
module SA = GC.Spec.Pages.SweepAll
module SS = GC.Spec.Pages.StartSweep
module MS = GC.Spec.Pages.MidSweep
module MS2 = GC.Spec.Pages.MidSweepStep
module MA = GC.Spec.Pages.MidSweepAlloc
module CS = GC.Spec.Pages.Cycle.State
module PM = GC.Spec.Pages.Cycle.Mark
module PS = GC.Spec.Pages.Cycle.Sweep
module PC = GC.Spec.Pages.Cycle
module PW = GC.Spec.Pages.Cycle.Write
module GenInv = GC.Gen.HeapInvariant
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module Promote = GC.Spec.Pages.Promote
module PMk = GC.Spec.Pages.Promote.Mark
module PSw = GC.Spec.Pages.Promote.Sweep
module PId = GC.Spec.Pages.Promote.Idle
module AT = GC.Spec.Pages.AllocTag
module ATO = GC.Spec.Pages.AllocTagOk
module TF = GC.Spec.Pages.Cycle.AllocTagged

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The allocation while marking, with any initialising values (M-e)
/// ---------------------------------------------------------------------------

/// A new object's header, recoloured black: tag 0, so neither a closure,
/// nor no-scan, nor infix.
#push-options "--z3rlimit 30"
let new_hdr (ga: heap) (x: obj_addr) (wz: nat{wz < pow2 54})
  : Lemma (requires Seq.mem x (objects zero_addr ga) /\ read_word ga (hd_address x) == B.ohdr wz)
          (ensures (let gc = set_object_color x ga Header.Black in
                    ~(is_closure x gc) /\ ~(is_no_scan x gc) /\ ~(is_infix x gc)))
  = let gc = set_object_color x ga Header.Black in
    Wt.holds_facts ga x wz (fun b -> read_word ga b);
    color_preserves_tag x ga Header.Black;
    color_preserves_is_no_scan x ga Header.Black;
    is_infix_spec x ga; is_infix_spec x gc;
    is_closure_spec x ga; is_closure_spec x gc
#pop-options

/// An allocation at `Marking` that succeeds gives an object of `wz`
/// fields, scannable, neither a closure nor infix.
#push-options "--z3rlimit 40 --ifuel 1"
let malloc_new (gx: heap) (stx: pstate) (wz: nat)
  : Lemma (requires PMP.mark_inv gx stx /\ (let (_, _, o) = PA.alloc I.Marking gx stx wz in o =!= 0UL))
          (ensures (let (gb, _, o) = PA.alloc I.Marking gx stx wz in
                    U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                    (let x : obj_addr = o in
                     Seq.mem x (objects zero_addr gb) /\ U64.v (wosize_of_object x gb) == wz /\
                     ~(is_closure x gb) /\ ~(is_no_scan x gb) /\ ~(is_infix x gb))))
  = PMP.mark_inv_alloc gx stx wz;
    assert (PA.alloc I.Marking gx stx wz == AP.alloc_col Header.Black gx stx wz);
    if wz + 1 >= pow2 54 then assert (A.alloc gx stx wz == (gx, stx, 0UL))
    else
    eliminate exists (ys: list obj_addr). CF.live_list gx ys /\ pages_ok (Rc.whiten gx ys) stx
    with begin
      AP.base gx ys stx wz;
      let gw = Rc.whiten gx ys in
      AP.mc_of_ok gw stx;
      AP.alloc_col_white gw stx wz;
      Wt.alloc_fresh gw stx wz;
      let (ga, sa, o) = A.alloc gx stx wz in
      assert (A.alloc gw stx wz == (Rc.whiten ga ys, sa, o));
      AP.new_facts gx ys stx wz Header.Black;
      let x : obj_addr = o in
      hd_address_spec x;
      assert (read_word ga (hd_address x) == B.ohdr wz);
      new_hdr ga x wz
    end
#pop-options

/// The writes that initialise `obj` keep its header and every word outside
/// its body.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let rec init_frame (#obj: obj_addr) (#g1 #g': heap) (w: MC.init_writes obj g1 g')
  : Lemma (requires Seq.mem obj (objects zero_addr g1))
          (ensures Seq.mem obj (objects zero_addr g') /\
                   read_word g' (hd_address obj) == read_word g1 (hd_address obj) /\
                   (forall (b: hp_addr). U64.v b < U64.v obj \/ U64.v b >= F.fields_end g1 obj ==>
                      read_word g' b == read_word g1 b))
          (decreases w)
  = match w with
    | MC.Init_done _ -> ()
    | MC.Init_write #_ #_ #gm w' a v g2 _ ->
      init_frame w';
      wosize_of_object_spec obj g1;
      wosize_of_object_spec obj gm;
      PW.write_fctx gm obj a v;
      F.obj_same gm g2 obj obj
#pop-options

/// A value storable for the snapshot is one `fields_written` allows.
let storable_field_ok (s: obj_addr -> prop) (g: heap) (v: U64.t)
  : Lemma (requires SPI.storable (MPC.outside_snapshot s) g v) (ensures I.field_ok g v)
  = ()

/// Every body word of `obj` holds a storable value.
#push-options "--z3rlimit 30"
let body_ok (s: obj_addr -> prop) (g': heap) (obj: obj_addr) (a: hp_addr)
  : Lemma (requires SPM.fields_storable (MPC.outside_snapshot s) g' obj /\ ~(is_no_scan obj g') /\
                    U64.v obj <= U64.v a /\ U64.v a < U64.v obj + U64.v (wosize_of_object obj g') * 8)
          (ensures I.field_ok g' (read_word g' a))
  = let d = U64.v a - U64.v obj in
    let i = d / 8 in
    assert (d % 8 == 0);
    FStar.Math.Lemmas.lemma_div_exact d 8;
    assert (U64.v obj + i * 8 == U64.v a);
    U64.uv_inv a;
    assert (SPM.field_val g' obj i == read_word g' a);
    storable_field_ok s g' (read_word g' a)
#pop-options

/// **M-e: an allocation while marking and its initialising writes keep the
/// page `Marking` invariant**, for any values the snapshot allows.
#push-options "--z3rlimit 40"
let alloc_mark_inv (g: heap) (st: pstate) (wz: nat) (g1: heap) (st1: pstate) (obj: obj_addr)
                   (g': heap) (w: MC.init_writes obj g1 g') (s: obj_addr -> prop)
  : Lemma (requires PMP.mark_inv g st /\ PA.alloc I.Marking g st wz == (g1, st1, (obj <: U64.t)) /\
                    SPM.fields_storable (MPC.outside_snapshot s) g' obj)
          (ensures PMP.mark_inv g' st1)
  = malloc_new g st wz;
    PMP.mark_inv_alloc g st wz;
    assert (PA.alloc I.Marking g st wz == AP.alloc_col Header.Black g st wz);
    init_frame w;
    wosize_of_object_spec obj g1;
    wosize_of_object_spec obj g';
    tag_of_object_spec obj g1; tag_of_object_spec obj g';
    is_no_scan_spec obj g1; is_no_scan_spec obj g';
    FStar.Classical.forall_intro (FStar.Classical.move_requires (body_ok s g' obj));
    assert (I.fields_written g1 g' obj)
#pop-options

/// The program's writes to the fields of a scannable new object point
/// nowhere into its own body (`AT.away`; plan §29.2).
let away_body (g1 g': heap) (x: obj_addr) : prop =
  ~(is_no_scan x g1) ==>
  (forall (a: hp_addr). U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g1) * 8 ==>
     AT.away x (U64.v (wosize_of_object x g1)) (read_word g' a))

/// **An allocation with a tag while marking and its initialising writes
/// keep the page `Marking` invariant**, for any values the snapshot allows
/// that point nowhere into the new object's body.
#push-options "--z3rlimit 40"
let alloc_mark_tag_inv (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
                       (g1: heap) (st1: pstate) (obj: obj_addr)
                       (g': heap) (w: MC.init_writes obj g1 g') (s: obj_addr -> prop)
  : Lemma (requires PMP.mark_inv g st /\ U64.v tag <> 249 /\
                    AT.alloc_tag I.Marking g st wz tag == (g1, st1, (obj <: U64.t)) /\
                    SPM.fields_storable (MPC.outside_snapshot s) g' obj /\ away_body g1 g' obj)
          (ensures PMP.mark_inv g' st1)
  = ATO.alloc_tag_marking g st wz tag;
    init_frame w;
    wosize_of_object_spec obj g1;
    wosize_of_object_spec obj g';
    tag_of_object_spec obj g1; tag_of_object_spec obj g';
    is_no_scan_spec obj g1; is_no_scan_spec obj g';
    FStar.Classical.forall_intro (FStar.Classical.move_requires (body_ok s g' obj));
    assert (AT.fields_written_away free_stw g1 g' obj);
    TF.mark_tag_inv g st wz tag g1 st1 obj g'
#pop-options

/// ---------------------------------------------------------------------------
/// The runs
/// ---------------------------------------------------------------------------

/// **Marking**, the page invariant carried.
noeq type cmarking (g0: heap) (rs: seq U64.t) : heap -> pstate -> MP.scan_pos -> (obj_addr -> prop) -> Type =
  // Root darkening, from the idle heap with the nursery empty.
  | CStart :
      minor: minor_state -> st0: pstate ->
      squash (PM.pstart_pre minor g0 st0 rs) ->
      cmarking g0 rs (MStart.darkened g0 rs) st0 MP.scan_none SPC.nothing_new
  // Mark moves.
  | CSlice :
      #g: heap -> #st: pstate -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      cmarking g0 rs g st sp since ->
      minor: minor_state -> g': heap -> sp': MP.scan_pos ->
      squash (MP.marking_inv g (GMM.nursery_refs minor g) sp /\ S.mark_steps g sp g' sp') ->
      cmarking g0 rs g' st sp' since
  // The barrier write of `v` at `a`, a body word of `x`.
  | CWrite :
      #g: heap -> #st: pstate -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      cmarking g0 rs g st sp since ->
      minor: minor_state -> x: obj_addr -> a: hp_addr -> v: U64.t ->
      squash (MP.marking_inv g (GMM.nursery_refs minor g) sp /\
              GB.modify_ok Ph.Marking minor g sp x a v /\
              MPC.cycle_write (MC.snapshot g0 rs since) g x a v) ->
      cmarking g0 rs (GB.modify_heap Ph.Marking g a v) st sp since
  // An allocation at `Marking` that hands out `obj`, and the writes that
  // initialise it, with values in the snapshot.
  | CAlloc :
      #g: heap -> #st: pstate -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      cmarking g0 rs g st sp since ->
      minor: minor_state -> wz: nat -> g1: heap -> st1: pstate -> obj: obj_addr ->
      squash (MP.marking_inv g (GMM.nursery_refs minor g) sp /\
              PA.alloc I.Marking g st wz == (g1, st1, (obj <: U64.t))) ->
      g': heap -> MC.init_writes obj g1 g' ->
      squash (SPM.fields_storable (MPC.outside_snapshot (MC.snapshot g0 rs (SPC.with_new since obj))) g' obj) ->
      cmarking g0 rs g' st1 sp (SPC.with_new since obj)
  // The same with a tag, any but the infix tag (plan §29.2), the values
  // also pointing nowhere into the new object's body.
  | CAllocT :
      #g: heap -> #st: pstate -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      cmarking g0 rs g st sp since ->
      minor: minor_state -> wz: nat -> tag: AT.tag_t -> g1: heap -> st1: pstate -> obj: obj_addr ->
      squash (MP.marking_inv g (GMM.nursery_refs minor g) sp /\ U64.v tag <> 249 /\
              AT.alloc_tag I.Marking g st wz tag == (g1, st1, (obj <: U64.t))) ->
      g': heap -> MC.init_writes obj g1 g' ->
      squash (SPM.fields_storable (MPC.outside_snapshot (MC.snapshot g0 rs (SPC.with_new since obj))) g' obj /\
              away_body g1 g' obj) ->
      cmarking g0 rs g' st1 sp (SPC.with_new since obj)
  // A minor collection (plan §27.4), its copies allocated black with their
  // tags.
  | CMinor :
      #g: heap -> #st: pstate -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      cmarking g0 rs g st sp since ->
      minor: minor_state -> roots: seq U64.t ->
      squash (MP.marking_inv g (GMM.nursery_refs minor g) sp /\ GenInv.minor_heap_shape minor /\
              MCFH.roots_valid_for_minor_collection minor g roots /\
              MP.outside_refs_reached g sp (GMM.root_refs g roots) /\
              GenInv.minor_major_fields_not_free (MPC.outside_snapshot (MC.snapshot g0 rs since)) minor g) ->
      cmarking g0 rs (PMk.gm minor g st roots) (PMk.mcollect minor g st roots).Promote.rst sp
                     (GMC.with_new_blocks since g (PMk.gm minor g st roots))

/// **The sweep**, from the marked heap `g0`, the page invariant carried.
noeq type csweep (g0: heap) : heap -> pstate -> I.phase -> (obj_addr -> prop) -> Type =
  // The sweep starts at the marked heap.
  | CSStart :
      st0: pstate ->
      csweep g0 g0 st0 I.Sweeping SPC.nothing_new
  // One page sweep step.
  | CSStep :
      #g: heap -> #st: pstate -> #since: (obj_addr -> prop) ->
      csweep g0 g st I.Sweeping since ->
      p: nat{p < n_pages} ->
      csweep g0 (fst (SA.step g st p)) (snd (SA.step g st p)) I.Sweeping since
  // An allocation, and the caller's writes to its fields.
  | CSAlloc :
      #g: heap -> #st: pstate -> #since: (obj_addr -> prop) ->
      csweep g0 g st I.Sweeping since ->
      wz: nat -> g1: heap -> st1: pstate -> obj: obj_addr ->
      squash (PA.alloc I.Sweeping g st wz == (g1, st1, (obj <: U64.t))) ->
      g': heap ->
      squash (I.fields_written_with (MS.free_sw st.pm) g1 g' obj) ->
      csweep g0 g' st1 I.Sweeping (SPC.with_new since obj)
  // The same with a tag, any but the infix tag (plan §29.2), and the
  // caller's writes as `AT.fields_written_away` allows.
  | CSAllocT :
      #g: heap -> #st: pstate -> #since: (obj_addr -> prop) ->
      csweep g0 g st I.Sweeping since ->
      wz: nat -> tag: AT.tag_t -> g1: heap -> st1: pstate -> obj: obj_addr ->
      squash (U64.v tag <> 249 /\ AT.alloc_tag I.Sweeping g st wz tag == (g1, st1, (obj <: U64.t))) ->
      g': heap ->
      squash (AT.fields_written_away (MS.free_sw st.pm) g1 g' obj) ->
      csweep g0 g' st1 I.Sweeping (SPC.with_new since obj)
  // A program write: into a block in use, of a value that is not free.
  | CSWrite :
      #g: heap -> #st: pstate -> #since: (obj_addr -> prop) ->
      csweep g0 g st I.Sweeping since ->
      x: obj_addr -> a: hp_addr -> v: U64.t ->
      squash (SPM.program_write (MS.free_sw st.pm) g x a v) ->
      csweep g0 (write_word g a v) st I.Sweeping since
  // A minor collection mid-sweep (plan §27.5), free meaning `free_sw`.
  | CSMinor :
      #g: heap -> #st: pstate -> #since: (obj_addr -> prop) ->
      csweep g0 g st I.Sweeping since ->
      minor: minor_state -> roots: seq U64.t ->
      squash (GenInv.minor_heap_shape minor /\ GenInv.minor_major_fields_not_free (MS.free_sw st.pm) minor g) ->
      csweep g0 (PSw.scollect minor g st roots).Promote.rmajor (PSw.scollect minor g st roots).Promote.rst
             I.Sweeping (PSw.with_made st.pm since g (PSw.scollect minor g st roots).Promote.rmajor)
  // Every page swept: the cycle is idle again.
  | CSEnd :
      #g: heap -> #st: pstate -> #since: (obj_addr -> prop) ->
      csweep g0 g st I.Sweeping since ->
      squash (PMP.all_swept st) ->
      csweep g0 g st I.Idle since
  // A minor collection once the cycle is idle (plan §29.1), free meaning
  // blue.
  | CSIMinor :
      #g: heap -> #st: pstate -> #since: (obj_addr -> prop) ->
      csweep g0 g st I.Idle since ->
      minor: minor_state -> roots: seq U64.t ->
      squash (GenInv.minor_heap_shape minor /\ GenInv.minor_major_fields_not_free free_stw minor g) ->
      csweep g0 (PId.icollect minor g st roots).Promote.rmajor (PId.icollect minor g st roots).Promote.rst
             I.Idle (PId.with_made since g (PId.icollect minor g st roots).Promote.rmajor)

/// The page state a sweep run started from.
#push-options "--ifuel 1"
let rec cstart_st (#gh #g: heap) (#st: pstate) (#ph: I.phase) (#since: obj_addr -> prop)
                  (r: csweep gh g st ph since)
  : GTot pstate (decreases r)
  = match r with
    | CSStart st0 -> st0
    | CSStep r1 _ -> cstart_st r1
    | CSAlloc r1 _ _ _ _ _ _ _ -> cstart_st r1
    | CSAllocT r1 _ _ _ _ _ _ _ _ -> cstart_st r1
    | CSWrite r1 _ _ _ _ -> cstart_st r1
    | CSMinor r1 _ _ _ -> cstart_st r1
    | CSEnd r1 _ -> cstart_st r1
    | CSIMinor r1 _ _ _ -> cstart_st r1
#pop-options

/// **The cycle**: marking; or marking, the mark moves that leave nothing
/// grey, and the sweep from the heap they leave and the page state marking
/// left.
noeq type ccycle (g0: heap) (rs: seq U64.t) : heap -> pstate -> I.phase -> (obj_addr -> prop) -> Type =
  | CMark :
      #g: heap -> #st: pstate -> #sp: MP.scan_pos -> #since: (obj_addr -> prop) ->
      cmarking g0 rs g st sp since ->
      ccycle g0 rs g st I.Marking since
  | CSweep :
      #g: heap -> #st: pstate -> #sp: MP.scan_pos -> #sm: (obj_addr -> prop) ->
      cmarking g0 rs g st sp sm ->
      minor: minor_state -> gh: heap -> sp': MP.scan_pos ->
      squash (MP.marking_inv g (GMM.nursery_refs minor g) sp /\ S.mark_steps g sp gh sp' /\
              Mark.noGreyObjects gh /\ sp' == MP.scan_none) ->
      #g': heap -> #st': pstate -> #ph: I.phase -> #ss: (obj_addr -> prop) ->
      sr: csweep gh g' st' ph ss ->
      squash (cstart_st sr == SS.start_sweep st) ->
      ccycle g0 rs g' st' ph (GC_.union sm ss)

/// **The page invariant of each phase.**
#push-options "--ifuel 1"
let cinv (g: heap) (st: pstate) (ph: I.phase) : prop =
  match ph with
  | I.Marking -> PMP.mark_inv g st
  | I.Sweeping -> MS.pages_ok_sw g st
  | I.Idle -> PA.inv I.Idle g st
#pop-options

/// ---------------------------------------------------------------------------
/// Every run here is a run of `GC.Spec.Pages.Cycle`
/// ---------------------------------------------------------------------------

/// A marking run, with the page invariant at its end.
#push-options "--ifuel 1 --z3rlimit 30"
let rec to_pmarking (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#sp: MP.scan_pos)
                    (#since: obj_addr -> prop) (r: cmarking g0 rs g st sp since)
  : Ghost (PM.pmarking g0 rs g st sp since) (requires True) (ensures fun _ -> PMP.mark_inv g st) (decreases r)
  = match r with
    | CStart minor st0 _ ->
        PM.start_facts minor g0 st0 rs;
        PM.PStart minor st0 ()
    | CSlice #_ #_ #g1 #st1 #sp1 #since1 r1 minor g' sp' _ ->
        let r1' = to_pmarking r1 in
        CS.mark_steps_inv st1 g1 sp1 g' sp';
        PM.PSlice r1' minor g' sp' ()
    | CWrite #_ #_ #g1 #st1 #sp1 #since1 r1 minor x a v _ ->
        let r1' = to_pmarking r1 in
        GI.phase_free_marking ();
        PW.barrier_mark_inv g1 st1 x a v;
        PM.PWrite r1' minor x a v ()
    | CAlloc #_ #_ #g1 #st1 #sp1 #since1 r1 minor wz ga sa obj _ g' w _ ->
        let r1' = to_pmarking r1 in
        alloc_mark_inv g1 st1 wz ga sa obj g' w (MC.snapshot g0 rs (SPC.with_new since1 obj));
        PM.PAlloc r1' minor wz ga sa obj () g' w ()
    | CAllocT #_ #_ #g1 #st1 #sp1 #since1 r1 minor wz tag ga sa obj _ g' w _ ->
        let r1' = to_pmarking r1 in
        alloc_mark_tag_inv g1 st1 wz tag ga sa obj g' w (MC.snapshot g0 rs (SPC.with_new since1 obj));
        PM.PAllocT r1' minor wz tag ga sa obj () g' w ()
    | CMinor #_ #_ #g1 #st1 #sp1 #since1 r1 minor roots _ ->
        let r1' = to_pmarking r1 in
        PM.nursery_stw minor g1 (MC.snapshot g0 rs since1);
        PMk.m_mark_inv minor g1 st1 roots;
        PM.PMinor r1' minor roots ()
#pop-options

/// The page invariant mid-sweep, and at its end.
#push-options "--ifuel 1"
let csw_inv (g: heap) (st: pstate) (ph: I.phase) : prop =
  match ph with
  | I.Sweeping -> MS.pages_ok_sw g st
  | I.Idle -> MS.pages_ok_sw g st /\ PMP.all_swept st
  | I.Marking -> False
#pop-options

/// A sweep run, from a marked heap ready to sweep.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let rec to_psweep (#gh #g: heap) (#st: pstate) (#ph: I.phase) (#since: obj_addr -> prop)
                  (r: csweep gh g st ph since)
  : Ghost (PS.psweep gh g st ph since)
          (requires SA.sweep_ready gh (cstart_st r) /\ SA.mark_done gh)
          (ensures fun r' -> PC.sweep_start_st r' == cstart_st r /\ csw_inv g st ph)
          (decreases r)
  = match r with
    | CSStart st0 ->
        MS2.sw_start gh st0;
        PS.SStart st0 ()
    | CSStep #_ #g1 #st1 #since1 r1 p ->
        let r1' = to_psweep r1 in
        MS2.step_sw g1 st1 p;
        PS.SStep r1' p ()
    | CSAlloc #_ #g1 #st1 #since1 r1 wz ga sa obj _ g' _ ->
        let r1' = to_psweep r1 in
        MA.alloc_sw_ok g1 st1 wz;
        PS.SAlloc r1' wz ga sa obj () g' ()
    | CSAllocT #_ #g1 #st1 #since1 r1 wz tag ga sa obj _ g' _ ->
        let r1' = to_psweep r1 in
        TF.sw_tag_inv g1 st1 wz tag ga sa obj g';
        PS.SAllocT r1' wz tag ga sa obj () g' ()
    | CSWrite #_ #g1 #st1 #since1 r1 x a v _ ->
        let r1' = to_psweep r1 in
        PW.swrite_keeps g1 st1 x a v;
        PS.SWrite r1' x a v ()
    | CSMinor #_ #g1 #st1 #since1 r1 minor roots _ ->
        let r1' = to_psweep r1 in
        PSw.s_facts minor g1 st1 roots;
        PS.SMinor r1' minor roots ()
    | CSEnd #_ #g1 #st1 #since1 r1 _ ->
        let r1' = to_psweep r1 in
        PS.SEnd r1' ()
    | CSIMinor #_ #g1 #st1 #since1 r1 minor roots _ ->
        let r1' = to_psweep r1 in
        MS2.sw_end g1 st1;
        PId.i_facts minor g1 st1 roots;
        let r = PId.icollect minor g1 st1 roots in
        PId.idle_sw r.Promote.rmajor r.Promote.rst;
        PS.SIMinor r1' minor roots ()
#pop-options

/// **A run of the cycle**, with the page invariant at its end.
#push-options "--ifuel 1 --z3rlimit 30"
let to_pcycle (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#ph: I.phase)
              (#since: obj_addr -> prop) (r: ccycle g0 rs g st ph since)
  : Ghost (PC.pcycle g0 rs g st ph since) (requires True) (ensures fun _ -> cinv g st ph)
  = match r with
    | CMark rm -> PC.PMark (to_pmarking rm)
    | CSweep #_ #_ #gm #stm #sp #sm rm minor gh sp' _ #g' #st' #ph' #ss sr _ ->
        let rm' = to_pmarking rm in
        CS.mark_steps_inv stm gm sp gh sp';
        S.mark_steps_inv gm gh sp sp' (GMM.nursery_refs minor gm);
        CS.handover_ready gh stm (GMM.nursery_refs minor gm) sp';
        let sr' = to_psweep sr in
        (if I.Idle? ph' then MS2.sw_end g' st');
        PC.PSweep rm' minor gh sp' () sr' ()
#pop-options

/// ---------------------------------------------------------------------------
/// The theorems
/// ---------------------------------------------------------------------------

/// **Every state of a run** is in the page invariant of its phase and in
/// akhil's account of the snapshot.
let ccycle_inv (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#ph: I.phase)
               (#since: obj_addr -> prop) (r: ccycle g0 rs g st ph since)
  : Lemma (ensures cinv g st ph /\ PC.pcycle_account (MC.snapshot g0 rs since) g st ph)
  = let r' = to_pcycle r in
    PC.cycle_account r'

/// **The incremental cycle with the page allocator, the page invariant
/// carried by the run.**  Once a run is idle again:
///   * the page `Idle` invariant holds, so the next cycle may start;
///   * every address outside the snapshot is freed (`cycle_complete`);
///   * an object unreachable at the start is freed unless its address was
///     handed out again (`cycle_frees_unreachable`);
///   * an object reachable at the start is a block in use, at its size, not
///     handed out (`cycle_survives`);
///   * an address not handed out is in use exactly when it held an object
///     reachable at the start (`cycle_addresses_lossless`);
///   * every word of a block unreachable at the start lies in a free block
///     or in one the run handed out (`cycle_covered`), and conversely, for
///     every word of the heap (`cycle_lossless`).
let ccycle_correct (#g0: heap) (#rs: seq U64.t) (#g: heap) (#st: pstate) (#since: obj_addr -> prop)
                   (r: ccycle g0 rs g st I.Idle since)
  : Lemma (ensures
      PA.inv I.Idle g st /\
      (forall (x: obj_addr). ~(MC.snapshot g0 rs since x) ==> SPC.freed g x) /\
      (forall (x: obj_addr). ~(GMC.reachable_at_start g0 rs x) /\ ~(since x) ==> SPC.freed g x) /\
      (forall (x: obj_addr). GMC.reachable_at_start g0 rs x ==>
         Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
         wosize_of_object x g == wosize_of_object x g0 /\ ~(since x)) /\
      (forall (x: obj_addr). ~(since x) ==> (GMC.reachable_at_start g0 rs x <==> ~(SPC.freed g x))) /\
      (forall (p: nat). GC_.unreachable_covered g0 rs p ==> SPC.free_or_new_at g since p) /\
      (forall (p: nat). p < heap_size ==>
         (GC_.unreachable_covered g0 rs p <==> LL.blue_covered g p \/ SPC.new_covered since g p)))
  = let r' = to_pcycle r in
    PC.cycle_complete r';
    PC.cycle_frees_unreachable r';
    PC.cycle_survives r';
    PC.cycle_addresses_lossless r';
    PC.cycle_covered r';
    PC.cycle_lossless r'
