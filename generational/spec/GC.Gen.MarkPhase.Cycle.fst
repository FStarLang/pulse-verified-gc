module GC.Gen.MarkPhase.Cycle

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
module MM = GC.Spec.MarkPhase.Mutator
module MPA = GC.Spec.MarkPhase.Alloc
module S = GC.Spec.MarkPhase.Slice
module GI = GC.Gen.Incremental
module GB = GC.Gen.Barrier
module GMM = GC.Gen.MarkPhase.Minor
module GMS = GC.Gen.MarkPhase.Safety
module MStart = GC.Gen.MarkPhase.Start
module MB = GC.Impl.MarkBounded
module MBP = GC.Impl.MarkBoundedPrecondition
module MPC = GC.Spec.MarkPhase.Completeness
module GMC = GC.Gen.MarkPhase.Completeness
module SPC = GC.Spec.SweepPhase.Completeness
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module GenInv = GC.Gen.HeapInvariant
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module Promote = GC.Gen.Promote
module FLA = GC.Spec.FreeList.Ascending
module SweepInv = GC.Spec.SweepInv
module Header = GC.Lib.Header

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The start: root darkening keeps every edge
/// ---------------------------------------------------------------------------

/// `g'` has the blocks, edges and resolutions of `g`, recoloured.
let edges_kept (g g': heap) : prop =
  objects zero_addr g' == objects zero_addr g /\ well_formed_heap g' /\
  (forall (y: obj_addr). resolve_object y g' == resolve_object y g) /\
  (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==> (is_blue y g' <==> is_blue y g)) /\
  (forall (u v: obj_addr). Seq.mem u (objects zero_addr g) ==> (MP.field_edge g' u v <==> MP.field_edge g u v))

/// Greying a white block keeps every edge.
#push-options "--z3rlimit 20"
let grey_keeps_edges (g: heap) (t: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem t (objects zero_addr g) /\ is_white t g)
          (ensures edges_kept g (makeGray t g))
  = Mark.colors_exclusive t g;
    MPC.grey_keeps_blocks g t;
    makeGray_eq t g;
    let g' = makeGray t g in
    Mark.color_change_preserves_wf g t Header.Gray;
    let rs (y: obj_addr) : Lemma (resolve_object y g' == resolve_object y g)
      = color_change_preserves_resolve t y g Header.Gray
    in
    FStar.Classical.forall_intro rs;
    let edge (u v: obj_addr)
      : Lemma (requires Seq.mem u (objects zero_addr g))
              (ensures MP.field_edge g' u v <==> MP.field_edge g u v)
      = let pt (c: obj_addr) : Lemma (points_to g' u c == points_to g u c)
          = if u = t then color_change_preserves_points_to_self g t Header.Gray c
            else color_change_preserves_points_to_other g t Header.Gray u c
        in
        FStar.Classical.forall_intro pt;
        if u = t then color_preserves_is_no_scan t g Header.Gray
        else color_change_preserves_other_is_no_scan t u g Header.Gray
    in
    FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (edge u))
#pop-options

/// What the start needs of the heap.
let start_heap (g: heap) (rs: seq U64.t) : prop =
  well_formed_heap g /\
  (forall (i: nat). i < Seq.length rs ==> MBP.root_valid_for_darkening g (Seq.index rs i))

/// Darkening the first `idx` roots keeps every edge.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let rec start_prefix_edges (g: heap) (rs: seq U64.t) (cap: nat) (idx: nat{idx <= Seq.length rs})
  : Lemma (requires start_heap g rs)
          (ensures edges_kept g (fst (MB.darken_roots_bounded_prefix_spec g Seq.empty rs idx cap)))
          (decreases idx)
  = if idx = 0 then
      assert (fst (MB.darken_roots_bounded_prefix_spec g Seq.empty rs idx cap) == g)
    else begin
      start_prefix_edges g rs cap (idx - 1);
      let (g0, st0) = MB.darken_roots_bounded_prefix_spec g Seq.empty rs (idx - 1) cap in
      let r = Seq.index rs (idx - 1) in
      if U64.v r >= U64.v zero_addr + U64.v mword && U64.v r < heap_size && U64.v r % U64.v mword = 0
      then begin
        let ro : obj_addr = r in
        let t = resolve_object ro g0 in
        hd_address_spec t;
        hd_address_bounds t;
        f_hd_roundtrip t;
        assert (U64.sub t mword == hd_address t);
        if is_white t g0 then begin
          assert (MBP.root_valid_for_darkening g r);
          grey_keeps_edges g0 t
        end
      end
    end
#pop-options

/// An element of a sequence is at some index.
let mem_index (rs: seq U64.t) (q: U64.t)
  : Lemma (requires Seq.mem q rs) (ensures exists (i: nat). i < Seq.length rs /\ Seq.index rs i == q)
  = let _ = FStar.Seq.Properties.index_mem q rs in ()

/// **The start, snapshot-at-the-beginning**: in the darkened heap every
/// object reachable from the roots is a block that is not free and, if
/// white, one the marker will reach -- the set of such blocks contains the
/// roots and is closed under the edges.
#push-options "--z3rlimit 40 --ifuel 1"
let start_satb (minor: minor_state) (g0: heap) (fp0: U64.t) (rs: seq U64.t)
  : Lemma (requires start_pre minor g0 fp0 rs)
          (ensures satb g0 rs (MStart.darkened g0 rs) MP.scan_none)
  = let gd = MStart.darkened g0 rs in
    let sp = MP.scan_none in
    GenInv.collection_heap_shape_as_free_stw minor g0 fp0;
    GenInv.collection_shape_with_elim Ph.Idle free_stw minor g0 fp0;
    GenInv.major_shape_with_elim Ph.Idle free_stw g0 fp0;
    start_prefix_edges g0 rs (Seq.length rs + 1) (Seq.length rs);
    assert (edges_kept g0 gd);
    MStart.mark_start_shape minor g0 fp0 rs;
    GI.phase_shape_marking minor gd fp0 sp;
    let c (v: obj_addr) : prop =
      in_use free_stw gd v /\ (is_white v gd ==> MP.marker_will_reach gd sp v) in
    // the roots
    let root (q: obj_addr)
      : Lemma (requires GMM.root_refs g0 rs q) (ensures c q)
      = eliminate exists (r: U64.t). Seq.mem r rs /\ is_pointer r /\ resolve_object (r <: obj_addr) g0 == q
        with begin
          mem_index rs r;
          assert (GMM.root_refs gd rs q)
        end
    in
    // the edges
    let step (u v: obj_addr)
      : Lemma (requires c u /\ MP.field_edge g0 u v) (ensures c v)
      = assert (MP.field_edge gd u v);
        eliminate exists (w: obj_addr). points_to gd u w /\ resolve_object w gd == v
        with points_to_target_not_free free_stw gd u w;
        if is_white v gd then begin
          MP.scan_none_edges gd u v;
          Mark.color_exhaustive u gd;
          Mark.colors_exclusive v gd;
          if is_white u gd then begin
            Mark.colors_exclusive u gd;
            eliminate exists (x: obj_addr). is_gray x gd /\ reach_within (MP.unscanned_edge gd sp) (MP.grey_or_white gd) x u
            with begin
              reach_within_ends (MP.unscanned_edge gd sp) (MP.grey_or_white gd) x u;
              reach_within_edge (MP.unscanned_edge gd sp) (MP.grey_or_white gd) u v;
              reach_within_trans (MP.unscanned_edge gd sp) (MP.grey_or_white gd) x u v
            end
          end else if is_gray u gd then
            reach_within_edge (MP.unscanned_edge gd sp) (MP.grey_or_white gd) u v
          else ()
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires root);
    FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (step u));
    let one (x: obj_addr)
      : Lemma (requires GMC.reachable_at_start g0 rs x) (ensures c x)
      = GMC.reachable_at_start_eq g0 rs;
        MPC.reachable_closed g0 (GMM.root_refs g0 rs) c x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

let start_inv minor g0 fp0 rs =
  start_satb minor g0 fp0 rs;
  GMC.cycle_start minor g0 fp0 rs;
  MPC.within_snapshot_ext (GMC.reachable_at_start g0 rs) (snapshot g0 rs SPC.nothing_new) (MStart.darkened g0 rs)

/// ---------------------------------------------------------------------------
/// The events
/// ---------------------------------------------------------------------------

/// A mark slice: mark moves keep the marking invariant for the objects
/// reachable at the start as outside references, and the account; they only
/// recolour.
let slice_inv (g0: heap) (rs: seq U64.t) (since: obj_addr -> prop)
              (minor: minor_state) (g: heap) (fp: U64.t) (sp: MP.scan_pos) (budget: nat)
              (g': heap) (sp': MP.scan_pos)
  : Lemma (requires mark_run_inv g0 rs since g sp /\ GI.phase_shape minor g fp Ph.Marking sp /\
                    GI.mark_slice_post g sp fp budget g' sp' fp Ph.Marking)
          (ensures mark_run_inv g0 rs since g' sp')
  = let r = GMC.reachable_at_start g0 rs in
    GI.phase_shape_marking minor g fp sp;
    assert (MP.marking_inv g r sp);
    S.mark_steps_inv g g' sp sp' r;
    MPC.account_steps (snapshot g0 rs since) g g' sp sp';
    MPC.mark_steps_keep_blocks g g' sp sp'

/// The barrier write: the deletion barrier keeps the marking invariant for
/// the nursery's fields and the objects reachable at the start as outside
/// references; the obligation keeps the account.
#push-options "--z3rlimit 20"
let write_inv (g0: heap) (rs: seq U64.t) (since: obj_addr -> prop)
              (minor: minor_state) (g: heap) (fp: U64.t) (sp: MP.scan_pos)
              (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires mark_run_inv g0 rs since g sp /\ GI.phase_shape minor g fp Ph.Marking sp /\
                    GB.modify_ok Ph.Marking minor g sp x a v /\
                    MPC.cycle_write (snapshot g0 rs since) g x a v)
          (ensures mark_run_inv g0 rs since (GB.modify_heap Ph.Marking g a v) sp)
  = let r = GMC.reachable_at_start g0 rs in
    let o (w: obj_addr) : prop = GMM.nursery_refs minor w \/ r w in
    GI.phase_shape_marking minor g fp sp;
    GI.phase_free_marking ();
    assert (MP.marking_inv g o sp);
    MM.marking_write_barrier g o sp x a v;
    MPC.account_barrier (snapshot g0 rs since) g x a v;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (GMS.modify_keeps_blocks minor g fp sp x a v))
#pop-options

/// The writes that initialise a fresh object keep it fresh, for the account
/// and the marking invariant, and keep every block that is not free.
#push-options "--ifuel 1"
let rec init_inv (#obj: obj_addr) (#g1 #g': heap) (w: init_writes obj g1 g')
                 (s: obj_addr -> prop) (r: obj_addr -> prop) (sp: MP.scan_pos)
  : Lemma (requires MPC.within_snapshot_fresh s g1 obj /\ MPA.marking_fresh g1 r sp obj)
          (ensures MPC.within_snapshot_fresh s g' obj /\ MPA.marking_fresh g' r sp obj /\
                   (forall (y: obj_addr). in_use free_stw g1 y ==> in_use free_stw g' y))
          (decreases w)
  = match w with
    | Init_done _ -> ()
    | Init_write #_ #_ #gm w' a v _ ->
        init_inv w' s r sp;
        MPC.account_fresh_write s gm obj a v;
        MPA.marking_fresh_write gm r sp obj a v;
        SPI.same_heads_facts gm (write_word gm a v)
#pop-options

/// The collector's state while marking, taken apart.
let marking_parts (minor: minor_state) (g: heap) (fp: U64.t) (sp: MP.scan_pos)
  : Lemma (requires GI.phase_shape minor g fp Ph.Marking sp)
          (ensures MP.marking_inv g (GMM.nursery_refs minor) sp /\ FLA.fl_ascending g fp)
  = GI.phase_shape_marking minor g fp sp;
    GenInv.collection_shape_with_elim Ph.Marking free_stw minor g fp;
    GenInv.major_shape_with_elim Ph.Marking free_stw g fp

/// An allocation and the initialisation of the new object: the account with
/// the object added, and the marking invariant for the objects reachable at
/// the start (the allocation keeps every block that is not free).
#push-options "--z3rlimit 30"
let alloc_inv (g0: heap) (rs: seq U64.t) (since: obj_addr -> prop)
              (minor: minor_state) (g: heap) (fp: U64.t) (sp: MP.scan_pos)
              (wz: nat) (tag: SPM.tag_t) (g1: heap) (fp': U64.t) (obj: obj_addr)
              (g': heap) (w: init_writes obj g1 g')
  : Lemma (requires mark_run_inv g0 rs since g sp /\
                    GI.phase_shape minor g fp Ph.Marking sp /\ wz >= 1 /\ tag <> infix_tag /\
                    (let r = AC.alloc_phase g fp Ph.Marking wz tag in
                     g1 == r.SA.heap_out /\ fp' == r.SA.fp_out /\ (obj <: U64.t) == r.SA.obj_out) /\
                    SPM.fields_storable (MPC.outside_snapshot (snapshot g0 rs (SPC.with_new since obj))) g' obj)
          (ensures mark_run_inv g0 rs (SPC.with_new since obj) g' sp)
  = let r = GMC.reachable_at_start g0 rs in
    let s = snapshot g0 rs since in
    let s1 = SPC.with_new s obj in
    let s' = snapshot g0 rs (SPC.with_new since obj) in
    marking_parts minor g fp sp;
    assert (MP.marking_inv g r sp);
    MPC.account_alloc s (GMM.nursery_refs minor) sp g fp wz tag;
    MPA.marking_alloc g r sp fp wz tag;
    let keep (y: obj_addr) : Lemma (requires in_use free_stw g y) (ensures in_use free_stw g1 y)
      = MM.header_kept_facts g g1 y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires keep);
    init_inv w s1 r sp;
    let same (h: heap) (y: obj_addr) : Lemma (MPC.outside_snapshot s1 h y == MPC.outside_snapshot s' h y) = () in
    FStar.Classical.forall_intro_2 same;
    assert (SPM.fields_storable (MPC.outside_snapshot s1) g' obj);
    MPC.account_fresh_close s1 g' obj;
    MPC.within_snapshot_ext s1 s' g'
#pop-options

/// A minor collection: the account with the blocks it made added
/// (`GMC.account_minor`), and the marking invariant for the objects
/// reachable at the start (`GMM.minor_keeps_marking_inv_with`).
#push-options "--z3rlimit 20"
let minor_inv (g0: heap) (rs: seq U64.t) (since: obj_addr -> prop)
              (minor: minor_state) (g: heap) (fp: U64.t) (sp: MP.scan_pos) (roots: seq U64.t)
  : Lemma (requires mark_run_inv g0 rs since g sp /\
                    GI.phase_shape minor g fp Ph.Marking sp /\
                    MCFH.roots_valid_for_minor_collection minor g roots /\
                    MP.outside_refs_reached g sp (GMM.root_refs g roots) /\
                    GenInv.minor_major_fields_not_free (MPC.outside_snapshot (snapshot g0 rs since)) minor g)
          (ensures (let g' = (GMM.collect_marking minor g fp roots).Promote.mc_major in
                    mark_run_inv g0 rs (GMC.with_new_blocks since g g') g' sp))
  = let r = GMC.reachable_at_start g0 rs in
    let s = snapshot g0 rs since in
    let g' = (GMM.collect_marking minor g fp roots).Promote.mc_major in
    GI.phase_shape_marking minor g fp sp;
    GMC.account_minor s minor g fp roots sp;
    MPC.within_snapshot_ext (GMC.with_new_blocks s g g') (snapshot g0 rs (GMC.with_new_blocks since g g')) g';
    assert (MP.marking_inv g (fun w -> GMM.outside_refs_of minor g roots w \/ r w) sp);
    GMM.minor_keeps_marking_inv_with r minor g fp roots sp;
    let keep (y: obj_addr) : Lemma (requires in_use free_stw g y) (ensures in_use free_stw g' y)
      = GMM.minor_keeps_block minor g fp roots y;
        MM.header_kept_facts g g' y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires keep)
#pop-options

/// ---------------------------------------------------------------------------
/// The run
/// ---------------------------------------------------------------------------

#push-options "--ifuel 1"
let rec mark_run_account #g0 #rs #g #fp #sp #since r : Lemma (ensures mark_run_inv g0 rs since g sp) (decreases r) =
  match r with
  | Start minor fp0 _ -> start_inv minor g0 fp0 rs
  | Slice #_ #_ #g1 #fp1 #sp1 #since1 r1 minor budget g' sp' _ ->
      mark_run_account r1;
      slice_inv g0 rs since1 minor g1 fp1 sp1 budget g' sp'
  | Write #_ #_ #g1 #fp1 #sp1 #since1 r1 minor x a v _ ->
      mark_run_account r1;
      write_inv g0 rs since1 minor g1 fp1 sp1 x a v
  | Alloc #_ #_ #g1 #fp1 #sp1 #since1 r1 minor wz tag ga fp' obj _ g' w _ ->
      mark_run_account r1;
      alloc_inv g0 rs since1 minor g1 fp1 sp1 wz tag ga fp' obj g' w
  | Minor #_ #_ #g1 #fp1 #sp1 #since1 r1 minor roots _ ->
      mark_run_account r1;
      minor_inv g0 rs since1 minor g1 fp1 sp1 roots
#pop-options

let handover #g0 #rs #g #fp #sp #since r =
  mark_run_account r;
  let black (x: obj_addr)
    : Lemma (requires GMC.reachable_at_start g0 rs x) (ensures SPC.survived_mark g x)
    = Mark.color_exhaustive x g;
      Mark.colors_exclusive x g;
      if is_white x g then MP.marker_will_reach_elim g sp x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires black);
  MPC.account_marked (snapshot g0 rs since) g
