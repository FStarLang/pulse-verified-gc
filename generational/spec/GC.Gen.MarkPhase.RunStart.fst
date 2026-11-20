module GC.Gen.MarkPhase.RunStart

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
module W = GC.Spec.Walk
module AP = GC.Spec.Allocator.Phase
module MW = GC.Gen.MarkPhase.Walk

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// A block keeps its size when it keeps its block.
let size_of_block (g g': heap) (x: obj_addr)
  : Lemma (requires SPI.same_block g g' (hd_address x))
          (ensures wosize_of_object x g' == wosize_of_object x g)
  = wosize_of_object_spec x g; wosize_of_object_spec x g'

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

/// The collector's state while marking, taken apart.
let marking_parts (minor: minor_state) (g: heap) (fp: U64.t) (sp: MP.scan_pos)
  : Lemma (requires GI.phase_shape minor g fp Ph.Marking sp)
          (ensures MP.marking_inv g (GMM.nursery_refs minor g) sp /\ FLA.fl_ascending g fp /\
                   AP.alloc_ok g fp /\ heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0)
  = GI.phase_shape_marking minor g fp sp;
    GenInv.collection_shape_with_elim Ph.Marking free_stw minor g fp;
    GenInv.major_shape_with_elim Ph.Marking free_stw g fp

/// The run's facts about the walk and the blocks handed out.
let extra_inv (g0: heap) (since: obj_addr -> prop) (g: heap) : prop =
  (forall (x: obj_addr). since x ==> Seq.mem x (objects zero_addr g) /\ is_black x g) /\
  W.walk_end g0 zero_addr + 8 >= heap_size /\
  W.reaches g zero_addr (W.walk_end g0 zero_addr)

/// Two dense heaps with the same blocks at the same sizes: the walk of the
/// second reaches where the first's ended.
let same_blocks_reaches (g g': heap) (e: nat)
  : Lemma (requires W.reaches g zero_addr e /\ e + 8 >= heap_size /\
                    heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                    heap_objects_dense g' /\ Seq.length (objects zero_addr g') > 0 /\
                    objects zero_addr g' == objects zero_addr g /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                       wosize_of_object x g' == wosize_of_object x g))
          (ensures W.reaches g' zero_addr e)
  = W.walk_end_of_reaches g zero_addr e;
    SPC.walk_end_same_blocks g g';
    W.reaches_end_of_dense g'

#push-options "--z3rlimit 20"
let start_extra (minor: minor_state) (g0: heap) (fp0: U64.t) (rs: seq U64.t)
  : Lemma (requires start_pre minor g0 fp0 rs)
          (ensures extra_inv g0 SPC.nothing_new (MStart.darkened g0 rs))
  = let gd = MStart.darkened g0 rs in
    GenInv.collection_heap_shape_as_free_stw minor g0 fp0;
    GenInv.collection_shape_with_elim Ph.Idle free_stw minor g0 fp0;
    GenInv.major_shape_with_elim Ph.Idle free_stw g0 fp0;
    W.reaches_end_of_dense g0;
    MStart.mark_start_shape minor g0 fp0 rs;
    marking_parts minor gd fp0 MP.scan_none;
    GMS.start_keeps_blocks minor g0 fp0 rs;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (size_of_block g0 gd));
    same_blocks_reaches g0 gd (W.walk_end g0 zero_addr)
#pop-options

let start_inv minor g0 fp0 rs =
  start_extra minor g0 fp0 rs;
  start_satb minor g0 fp0 rs;
  GMS.start_keeps_blocks minor g0 fp0 rs;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (size_of_block g0 (MStart.darkened g0 rs)));
  GMC.cycle_start minor g0 fp0 rs;
  MPC.within_snapshot_ext (GMC.reachable_at_start g0 rs) (snapshot g0 rs SPC.nothing_new) (MStart.darkened g0 rs)
