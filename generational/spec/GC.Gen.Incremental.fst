module GC.Gen.Incremental

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.SweepPhase.Intrinsic
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module GenInv = GC.Gen.HeapInvariant
module SL = GC.Spec.SweepPhase.Slice
module Cheney = GC.Gen.Cheney
module Promote = GC.Gen.Promote
module SPM = GC.Gen.SweepPhase.Minor
module SPE = GC.Spec.SweepPhase.Intrinsic.End
module FSI = GC.Spec.FusedSweep.Inv
module PCS = GC.Gen.PostCollectionShape
module Mark = GC.Spec.Mark
module SweepInv = GC.Spec.SweepInv
module Util = GC.Spec.SweepPhase.Util
module MP = GC.Spec.MarkPhase
module GMM = GC.Gen.MarkPhase.Minor
module MCFH = GC.Gen.MinorCollectForwarding.Helpers

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

let phase_shape_idle minor g fp sp = reveal_opaque (`%phase_shape) (phase_shape minor g fp Ph.Idle sp)

let phase_shape_marking minor g fp sp =
  reveal_opaque (`%phase_shape) (phase_shape minor g fp Ph.Marking sp)

let phase_shape_sweeping minor g fp c sp =
  reveal_opaque (`%phase_shape) (phase_shape minor g fp (Ph.Sweeping c) sp)

let phase_shape_pos minor g fp ph sp sp' =
  reveal_opaque (`%phase_shape) (phase_shape minor g fp ph sp);
  reveal_opaque (`%phase_shape) (phase_shape minor g fp ph sp')

/// The cross-generation condition carries over to a heap in which every block
/// non-free under `free` before is non-free under `free'`, with the same
/// size, tag and fields.
let fields_not_free_transport (minor: minor_state) (g g': heap) (free free': free_def)
  : Lemma (requires GenInv.minor_major_fields_not_free free minor g /\
                    no_infix_block g /\ no_infix_block g' /\
                    (forall (x: obj_addr). in_use free g x ==>
                       in_use free' g' x /\ same_block g g' (hd_address x)))
          (ensures GenInv.minor_major_fields_not_free free' minor g')
  = GenInv.minor_major_fields_not_free_transfer_blocks free free' minor g g'

let phase_shape_collection minor g fp ph sp =
  match ph with
  | Ph.Idle ->
      phase_shape_idle minor g fp sp;
      GenInv.collection_heap_shape_as_free_stw minor g fp;
      assert_norm (phase_free Ph.Idle == free_stw)
  | Ph.Marking ->
      phase_shape_marking minor g fp sp;
      assert_norm (phase_free Ph.Marking == free_stw)
  | Ph.Sweeping c ->
      phase_shape_sweeping minor g fp c sp;
      SPM.sweep_collection_shape minor g fp c;
      assert_norm (phase_free (Ph.Sweeping c) == free_incremental c)

let phase_shape_start minor g fp sp =
  let c = sweep_start.cursor in
  SPM.sweep_major_shape g fp c;
  GenInv.collection_shape_with_after_minor_reset (Ph.Sweeping c) (free_incremental c) minor g fp;
  GenInv.collection_shape_with_elim (Ph.Sweeping c) (free_incremental c) (minor_reset minor) g fp;
  phase_shape_sweeping (minor_reset minor) g fp c sp

#push-options "--z3rlimit 20"
let sweep_end_shape minor g fp c sp =
  phase_shape_sweeping minor g fp c sp;
  SPE.sweep_inv_incremental_end g fp c;
  PCS.free_list_shape_of_ascending g fp;
  let col (x: obj_addr)
    : Lemma (Seq.mem x (objects zero_addr g) ==> ~(is_black x g) /\ ~(is_gray x g))
    = if Seq.mem x (objects zero_addr g) then Mark.colors_exclusive x g
  in
  FStar.Classical.forall_intro col;
  SweepInv.no_gray_intro g;
  GenInv.major_heap_shape_intro g fp;
  // nothing is pending free, so the cross-generation condition is the idle one
  GenInv.minor_major_fields_not_free_weaken (free_incremental c) free_stw minor g;
  GenInv.minor_major_fields_not_free_stw minor g;
  GenInv.collection_heap_shape_intro minor g fp
#pop-options

/// ---------------------------------------------------------------------------
/// Marking: what the mark moves keep
/// ---------------------------------------------------------------------------

module S = GC.Spec.MarkPhase.Slice
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module SPU = GC.Spec.SweepPhase.Util
module SPI = GC.Spec.SweepPhase.Intrinsic
module Header = GC.Lib.Header
module HeapGraph = GC.Spec.HeapGraph

/// What every phase's shape says of the walk and the list.
let walk_ok (g: heap) (fp: U64.t) : prop =
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\ FLA.fl_ascending g fp

/// **Recolouring a block that is not free** to grey or black keeps
/// everything but its colour: the walk, the free list and its links, what is
/// free, every other header.
#push-options "--z3rlimit 30"
let recolour_facts (g: heap) (fp: U64.t) (t: obj_addr) (c: color)
  : Lemma (requires Seq.mem t (objects zero_addr g) /\ ~(is_blue t g) /\
                    (c == Header.Gray \/ c == Header.Black) /\ walk_ok g fp)
          (ensures (let g1 = set_object_color t g c in
                    walk_ok g1 fp /\
                    objects zero_addr g1 == objects zero_addr g /\
                    (forall (y: obj_addr). in_use free_stw g1 y == in_use free_stw g y)))
  = let g1 = set_object_color t g c in
    color_change_preserves_objects g t c;
    SweepInv.color_change_preserves_density t g c;
    let col (y: obj_addr) : Lemma ((is_blue y g1 <==> is_blue y g) /\
                                   wosize_of_object y g1 == wosize_of_object y g)
      = color_change_preserves_wosize_any t y g c;
        if y <> t then begin
          color_change_preserves_other_color t y g c;
          is_blue_iff y g; is_blue_iff y g1
        end
    in
    FStar.Classical.forall_intro col;
    let cells (q: U64.t) : Lemma (FL.fl_cell g1 q <==> FL.fl_cell g q) = () in
    FStar.Classical.forall_intro cells;
    let links (q: U64.t)
      : Lemma (requires FL.fl_cell g q) (ensures FL.fl_next g1 q == FL.fl_next g q)
      = FLA.fl_cell_facts g q;
        let o : obj_addr = q in
        SPI.obj_pos g o;
        SPI.obj_pos g t;
        SPI.colour_of g o;
        if hd_address t = q then SPU.no_pos_inside g (hd_address o) (U64.v q)
        else color_change_preserves_other_read t q g c
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires links);
    FLA.fl_ascending_transfer g g1 fp
#pop-options

/// A recolouring (or nothing) that keeps the walk and the non-free blocks
/// keeps the cross-generation condition, and what the nursery names: no
/// resolution changes.
let recolour_minor (free: free_def) (minor: minor_state) (g g': heap)
  : Lemma (requires GenInv.minor_major_fields_not_free free minor g /\
                    (g' == g \/ (exists (x: obj_addr) (c: color). g' == set_object_color x g c)) /\
                    objects zero_addr g' == objects zero_addr g /\
                    (forall (y: obj_addr). in_use free g' y == in_use free g y))
          (ensures GenInv.minor_major_fields_not_free free minor g' /\
                   (forall (w: obj_addr). GMM.nursery_refs minor g' w <==> GMM.nursery_refs minor g w))
  = if FStar.IndefiniteDescription.strong_excluded_middle (g' == g) then ()
    else
      eliminate exists (x: obj_addr) (c: color). g' == set_object_color x g c
      with begin
        GenInv.minor_major_fields_not_free_recolour free minor x g c;
        GMM.nursery_refs_colour minor x g c
      end

/// A mark move is one such recolouring, or nothing.
let move_is_recolour (g g': heap) (sp sp': MP.scan_pos)
  : Lemma (requires S.mark_move g sp g' sp')
          (ensures g' == g \/ (exists (x: obj_addr) (c: color). g' == set_object_color x g c))
  = if FStar.IndefiniteDescription.strong_excluded_middle (S.grey_move g sp g' sp') then
      eliminate exists (x: obj_addr).
        x == sp.MP.cur /\ S.scan_target g x /\ 1 <= sp.MP.fld /\ sp.MP.fld <= U64.v (wosize_of_object x g) /\
        g' == S.scan_field g x (U64.uint_to_t sp.MP.fld) /\ sp' == { sp with MP.fld = sp.MP.fld + 1 }
      with begin
        let v = HeapGraph.get_field g x (U64.uint_to_t sp.MP.fld) in
        if is_pointer v then makeGray_eq (resolve_object (v <: obj_addr) g) g
      end
    else if FStar.IndefiniteDescription.strong_excluded_middle (S.black_move g sp g' sp') then
      eliminate exists (x: obj_addr).
        Seq.mem x (objects zero_addr g) /\ is_gray x g /\ MP.all_scanned g sp x /\
        g' == makeBlack x g /\ sp' == MP.blackened_pos sp x
      with makeBlack_eq x g
    else assert (S.begin_move g sp g' sp')

#push-options "--z3rlimit 20"
let recolour_scan (g: heap) (fp: U64.t) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires well_formed_heap g /\ walk_ok g fp /\ S.scan_target g x /\
                    U64.v k <= U64.v (wosize_of_object x g))
          (ensures (let g' = S.scan_field g x k in
                    walk_ok g' fp /\ objects zero_addr g' == objects zero_addr g /\
                    (forall (y: obj_addr). in_use free_stw g' y == in_use free_stw g y)))
  = S.scan_field_is_grey g x k;
    let v = HeapGraph.get_field g x k in
    if is_pointer v && is_white (resolve_object v g) g then begin
      let tt = resolve_object v g in
      Mark.colors_exclusive tt g;
      makeGray_eq tt g;
      recolour_facts g fp tt Header.Gray
    end

let recolour_black (g: heap) (fp: U64.t) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\ walk_ok g fp /\ Seq.mem x (objects zero_addr g) /\ is_gray x g)
          (ensures (let g' = makeBlack x g in
                    walk_ok g' fp /\ objects zero_addr g' == objects zero_addr g /\
                    (forall (y: obj_addr). in_use free_stw g' y == in_use free_stw g y)))
  = Mark.colors_exclusive x g;
    makeBlack_eq x g;
    recolour_facts g fp x Header.Black

let move_recolour (g g': heap) (fp: U64.t) (sp sp': MP.scan_pos)
  : Lemma (requires well_formed_heap g /\ walk_ok g fp /\ S.mark_move g sp g' sp')
          (ensures walk_ok g' fp /\ objects zero_addr g' == objects zero_addr g /\
                   (forall (y: obj_addr). in_use free_stw g' y == in_use free_stw g y))
  = if FStar.IndefiniteDescription.strong_excluded_middle (S.grey_move g sp g' sp') then
      eliminate exists (x: obj_addr).
        x == sp.MP.cur /\ S.scan_target g x /\ 1 <= sp.MP.fld /\ sp.MP.fld <= U64.v (wosize_of_object x g) /\
        g' == S.scan_field g x (U64.uint_to_t sp.MP.fld) /\ sp' == { sp with MP.fld = sp.MP.fld + 1 }
      with recolour_scan g fp x (U64.uint_to_t sp.MP.fld)
    else if FStar.IndefiniteDescription.strong_excluded_middle (S.black_move g sp g' sp') then
      eliminate exists (x: obj_addr).
        Seq.mem x (objects zero_addr g) /\ is_gray x g /\ MP.all_scanned g sp x /\
        g' == makeBlack x g /\ sp' == MP.blackened_pos sp x
      with recolour_black g fp x
    else assert (S.begin_move g sp g' sp')
#pop-options

/// One move keeps the marking shape.
#push-options "--z3rlimit 30"
let move_shape (minor: minor_state) (fp: U64.t) (g: heap) (sp: MP.scan_pos) (g': heap) (sp': MP.scan_pos)
  : Lemma (requires phase_shape minor g fp Ph.Marking sp /\ S.mark_move g sp g' sp')
          (ensures phase_shape minor g' fp Ph.Marking sp')
  = phase_shape_marking minor g fp sp;
    phase_shape_marking minor g' fp sp';
    GenInv.collection_shape_with_elim Ph.Marking free_stw minor g fp;
    GenInv.major_shape_with_elim Ph.Marking free_stw g fp;
    S.mark_move_inv g g' sp sp' (GMM.nursery_refs minor g);
    move_recolour g g' fp sp sp';
    move_is_recolour g g' sp sp';
    recolour_minor free_stw minor g g';
    PCS.free_list_shape_of_ascending g' fp;
    GenInv.major_shape_with_intro Ph.Marking free_stw g' fp;
    GenInv.collection_shape_with_intro Ph.Marking free_stw minor g' fp
#pop-options

let mark_steps_shape minor g g' fp sp sp' =
  S.mark_steps_ind (fun h q -> phase_shape minor h fp Ph.Marking q) (move_shape minor fp) g sp g' sp'

/// What the roots and the nursery point at.
let union_outside_refs (minor: minor_state) (h0: heap) (rs: seq U64.t) (w: obj_addr) : prop =
  GMM.root_refs h0 rs w \/ GMM.nursery_refs minor h0 w

#push-options "--z3rlimit 20"
let mark_steps_roots minor g g' fp rs sp sp' =
  phase_shape_marking minor g fp sp;
  let outside_refs = union_outside_refs minor g rs in
  assert (MP.marking_inv g outside_refs sp);
  S.mark_steps_inv g g' sp sp' outside_refs;
  S.mark_steps_darker g g' sp sp';
  let same (w: obj_addr) : Lemma (GMM.root_refs g' rs w ==> GMM.root_refs g rs w) =
    let aux (r: U64.t) : Lemma (Seq.mem r rs /\ is_pointer r /\ resolve_object (r <: obj_addr) g' == w ==>
                                GMM.root_refs g rs w) = () in
    FStar.Classical.forall_intro aux
  in
  FStar.Classical.forall_intro same
#pop-options

#push-options "--z3rlimit 30"
let marking_done_shape minor g fp sp sp' =
  let c = zero_addr in
  phase_shape_marking minor g fp sp;
  GenInv.collection_shape_with_elim Ph.Marking free_stw minor g fp;
  GenInv.major_shape_with_elim Ph.Marking free_stw g fp;
  let outside_refs = GMM.nursery_refs minor g in
  MP.marking_done_sweep_start g outside_refs sp fp;
  MP.marking_done g outside_refs sp;
  assert (sweep_start.cursor == c);
  free_stw_ok ();
  let nf (obj: U64.t) (j: nat)
    : Lemma (requires Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj /\
                      is_pointer_field (minor_read_field minor obj j))
            (ensures in_use (free_incremental c) g (resolve_object ((minor_read_field minor obj j) <: obj_addr) g) /\
                     infix_addr_wf g (objects zero_addr g) ((minor_read_field minor obj j) <: obj_addr))
    = GenInv.minor_major_fields_not_free_elim free_stw minor g obj j;
      let v : obj_addr = minor_read_field minor obj j in
      assert (outside_refs (resolve_object v g))
  in
  GenInv.minor_major_fields_not_free_intro (free_incremental c) minor g nf;
  phase_shape_sweeping minor g fp c sp'
#pop-options

let mark_slice_shape minor g sp fp budget g' sp' fp' ph' =
  mark_steps_shape minor g g' fp sp sp';
  if Ph.Sweeping? ph' then marking_done_shape minor g' fp sp' sp'

#push-options "--z3rlimit 20"
let phase_slice_shape minor g fp ph budget sp =
  match ph with
  | Ph.Idle | Ph.Marking -> ()
  | Ph.Sweeping c ->
      phase_shape_sweeping minor g fp c sp;
      SL.sweep_slice_phase g fp c budget;
      let (g', fp', st') = SL.sweep_slice g fp (state_at g c) budget in
      sweep_inv_incremental_elim g fp c;
      sweep_inv_incremental_elim g' fp' st'.cursor;
      wf_with_parts ();
      fields_not_free_transport minor g g' (free_incremental c) (free_incremental st'.cursor);
      phase_shape_sweeping minor g' fp' st'.cursor sp;
      if sweep_done st'.cursor then begin
        sweep_end_shape minor g' fp' st'.cursor sp;
        phase_shape_idle minor g' fp' sp
      end
#pop-options

let phase_slice_finishes minor g fp ph budget sp =
  match ph with
  | Ph.Idle | Ph.Marking -> ()
  | Ph.Sweeping c ->
      phase_shape_sweeping minor g fp c sp;
      SL.sweep_slice_phase g fp c budget

#push-options "--z3rlimit 20"
let minor_keeps_phase_shape minor g fp c roots sp =
  phase_shape_sweeping minor g fp c sp;
  SPM.minor_keeps_sweep_phase minor g fp c roots;
  let free = free_incremental c in
  let res = SPM.collect_at c minor g fp roots in
  GenInv.collection_shape_with_elim (Ph.Sweeping c) free res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp;
  phase_shape_sweeping res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp c sp
#pop-options

#push-options "--z3rlimit 20"
let minor_keeps_marking_shape minor g fp roots sp =
  phase_shape_marking minor g fp sp;
  assert (MP.marking_inv g (GMM.outside_refs_of minor g roots) sp);
  GMM.minor_keeps_marking_inv minor g fp roots sp;
  let res = GMM.collect_marking minor g fp roots in
  FStar.Classical.forall_intro (GMM.nursery_refs_reset minor res.Promote.mc_major);
  assert (MP.marking_inv res.Promote.mc_major (GMM.nursery_refs res.Promote.mc_minor res.Promote.mc_major) sp);
  phase_shape_marking res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp sp
#pop-options

let phase_free_idle () = assert_norm (phase_free Ph.Idle == free_stw)

let phase_free_marking () = assert_norm (phase_free Ph.Marking == free_stw)

let phase_free_sweeping c = assert_norm (phase_free (Ph.Sweeping c) == free_incremental c)
