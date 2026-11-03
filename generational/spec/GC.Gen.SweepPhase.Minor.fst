module GC.Gen.SweepPhase.Minor

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.SweepPhase.Intrinsic
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module GenInv = GC.Gen.HeapInvariant
module PCS = GC.Gen.PostCollectionShape
module CA = GC.Gen.CheneyAt
module Paint = GC.Gen.Paint
module Ph = GC.Spec.Phase

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

let sweep_major_shape g fp st =
  sweep_phase_inv_elim g fp st;
  surviving_view_ok st;
  surviving_from_view_ok st g;
  well_formed_view_congr (surviving st) (surviving_from st g) g;
  PCS.free_list_shape_of_ascending g fp;
  wf_view_parts ();
  GenInv.major_shape_view_intro (surviving st) g fp;
  GenInv.major_shape_view_intro (surviving_from st g) g fp

let sweep_collection_shape minor g fp st =
  sweep_major_shape g fp st;
  GenInv.minor_major_fields_in_view_intro (surviving_from st g) minor g
    (fun obj j -> GenInv.minor_major_fields_in_view_elim (surviving st) minor g obj j);
  GenInv.collection_shape_view_intro (surviving_from st g) minor g fp


/// ---------------------------------------------------------------------------
/// The pointer update keeps the walk and every header
/// ---------------------------------------------------------------------------

module Promote = GC.Gen.Promote
module PUO = GC.Gen.PromoteUpdate.Obj
module W = GC.Spec.Walk
module FLA = GC.Spec.FreeList.Ascending
module CV = GC.Gen.CheneyView
module Cheney = GC.Gen.Cheney
module GSP = GC.Gen.SweepPhase
open GC.Spec.SweepPhase.Util
open GC.Spec.FusedSweep.Inv

#push-options "--z3rlimit 20"
let uop_heads (major: heap) (obj: obj_addr) (fwd: Promote.forwarding_map) (i: nat)
  : Lemma (requires Seq.mem obj (objects zero_addr major))
          (ensures same_heads major
                     (Promote.update_object_pointers major obj (U64.v (wosize_of_object obj major)) fwd i))
  = let wz = U64.v (wosize_of_object obj major) in
    let major' = Promote.update_object_pointers major obj wz fwd i in
    part1_holds major;
    wfh_part1_obj_bound major obj;
    hd_address_spec obj;
    obj_pos major obj; colour_of major obj;
    W.bnext_facts major (hd_address obj);
    let bnd (j: nat) : Lemma (j < wz ==> U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)
      = () in
    FStar.Classical.forall_intro bnd;
    let at (q: hp_addr)
      : Lemma (requires W.reaches major zero_addr (U64.v q))
              (ensures read_word major' q == read_word major q)
      = if U64.v q < U64.v obj then PUO.update_object_pointers_preserves_addr_below major obj wz fwd i q
        else if U64.v q >= U64.v obj + wz * 8 then PUO.update_object_pointers_preserves_addr_above major obj wz fwd i q
        else no_pos_inside major (hd_address obj) (U64.v q)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires at);
    W.walk_congr major major' zero_addr
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec uwa_heads (major: heap) (objs: seq obj_addr) (upd: obj_addr -> GTot bool)
                  (fwd: Promote.forwarding_map) (idx: nat)
  : Lemma (requires objs == objects zero_addr major)
          (ensures same_heads major (Promote.update_walk_aux major objs upd fwd idx))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      let obj = Seq.index objs idx in
      if not (upd obj) then
        uwa_heads major objs upd fwd (idx + 1)
      else if is_no_scan obj major then uwa_heads major objs upd fwd (idx + 1)
      else begin
        let wz = U64.v (wosize_of_object obj major) in
        let major' = Promote.update_object_pointers major obj wz fwd 0 in
        uop_heads major obj fwd 0;
        same_heads_facts major major';
        uwa_heads major' objs upd fwd (idx + 1)
      end
    end
#pop-options

let update_heads (major: heap) (v: view) (fwd: Promote.forwarding_map)
  : Lemma (same_heads major (Promote.update_pointers_view v major fwd))
  = uwa_heads major (objects zero_addr major) (v major) fwd 0

/// Painting heaps with the same walk and headers gives heaps with the same
/// walk and headers.
#push-options "--z3rlimit 20"
let paint_heads (c: nat) (g0 h h': heap)
  : Lemma (requires same_heads h h')
          (ensures same_heads (Paint.paint c g0 h) (Paint.paint c g0 h'))
  = Paint.paint_recoloured c g0 h;
    Paint.paint_recoloured c g0 h';
    let at (q: hp_addr)
      : Lemma (requires W.reaches (Paint.paint c g0 h) zero_addr (U64.v q))
              (ensures read_word (Paint.paint c g0 h') q == read_word (Paint.paint c g0 h) q)
      = Paint.paint_read c g0 h q; Paint.paint_read c g0 h' q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires at)
#pop-options

/// ---------------------------------------------------------------------------
/// The promotions, painted, keep the sweep shape
/// ---------------------------------------------------------------------------

let st_at (st: sweep_state) (h: heap) : GTot sweep_state = state_after st h

/// The invariant of the promotion run: the idle heap `h` keeps what the
/// collection started with, and painted it is in the sweep's shape at the
/// state the allocations have left, with the same condemned set.
let run_inv (g: heap) (st: sweep_state) (h: heap) (f: U64.t) : prop =
  Paint.paint_ok g h f /\
  sweep_shape (Paint.paint (U64.v st.cursor) g h) f (st_at st h) /\
  (forall (x: obj_addr). condemned (st_at st h) (Paint.paint (U64.v st.cursor) g h) x == condemned st g x)

#push-options "--z3rlimit 20"
let run_step (minor: minor_state) (g: heap) (st: sweep_state) (h: heap) (f: U64.t) (obj: U64.t)
  : Lemma (requires run_inv g st h f /\ Seq.mem obj (minor_objects minor) /\ minor_wosize minor obj > 0)
          (ensures (let r = Promote.promote_object minor h obj f (minor_wosize minor obj) Ph.Idle in
                    run_inv g st r.Promote.major_out r.Promote.fp_out))
  = let wz = minor_wosize minor obj in
    minor_objects_wosize_bound minor obj;
    FStar.Math.Lemmas.pow2_plus 54 3;
    assert_norm (pow2 3 == 8);
    assert (wz * 8 < pow2 54 * 8);
    assert (wz < pow2 54);
    let ph0 = Ph.Sweeping st in
    Paint.paint_promote ph0 g h f minor obj wz;
    let r = Promote.promote_object minor h obj f wz Ph.Idle in
    let hp = Paint.paint (U64.v st.cursor) g h in
    assert (Paint.phase_at ph0 h == Ph.Sweeping (st_at st h));
    GSP.promote_sweep_shape hp f (st_at st h) minor obj wz
#pop-options

#push-options "--z3rlimit 20"
let run_start (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st) (ensures run_inv g st g fp)
  = sweep_phase_inv_iff g fp st;
    sweep_phase_inv_elim g fp st;
    let c = U64.v st.cursor in
    Paint.paint_start (Ph.Sweeping st) g fp;
    tail_ok_elim g c st.swept_tail;
    Paint.phase_at_self (Ph.Sweeping st) g;
    assert (st_at st g == st)
#pop-options

/// ---------------------------------------------------------------------------
/// Step C
/// ---------------------------------------------------------------------------

/// The sweep's view of the painted result is the collection's view of the
/// idle one.
#push-options "--z3rlimit 20"
let painted_view (g: heap) (st st': sweep_state) (rm: heap) (x: obj_addr)
  : Lemma (requires Paint.kept g rm /\ U64.v st.cursor % 8 == 0 /\ st'.cursor == st.cursor)
          (ensures surviving st' (Paint.paint (U64.v st.cursor) g rm) x == surviving_from st g rm x)
  = Paint.paint_surviving st g rm x
#pop-options

#push-options "--z3rlimit 30"
let minor_keeps_sweep_phase minor g fp st roots =
  let v = surviving_from st g in
  let c = U64.v st.cursor in
  let ph0 = Ph.Sweeping st in
  sweep_collection_shape minor g fp st;
  let prom = Cheney.cheney_promote minor g fp roots in
  surviving_from_fresh st g prom.Promote.major_final;
  CV.cheney_collect_view_preserves_shape v minor g fp roots;
  let res0 = Cheney.cheney_collect_spec_view v minor g fp roots in
  let pm = prom.Promote.major_final in
  let rm = res0.Promote.mc_major in
  // the promotions
  run_start g fp st;
  Cheney.cheney_promote_induction minor g fp roots (run_inv g st) (run_step minor g st);
  assert (run_inv g st pm prom.Promote.fp_final);
  // the pointer update
  update_heads pm v prom.Promote.fwd_map;
  assert (rm == Promote.update_pointers_view v pm prom.Promote.fwd_map);
  same_heads_facts pm rm;
  Paint.max_cell_below_congr pm rm (U64.v st.swept_tail);
  assert (st_at st rm == st_at st pm);
  paint_heads c g pm rm;
  let rp = Paint.paint c g rm in
  let st' = st_at st rm in
  GenInv.collection_shape_view_elim v res0.Promote.mc_minor rm res0.Promote.mc_fp;
  GenInv.major_shape_view_elim v rm res0.Promote.mc_fp;
  Paint.paint_recoloured c g rm;
  Paint.recoloured_fl rm rp res0.Promote.mc_fp;
  shape_transport (Paint.paint c g pm) rp prom.Promote.fp_final st';
  same_heads_facts (Paint.paint c g pm) rp;
  // well-formedness on the sweep's view: painting makes the promoted copies
  // in front of the cursor black, so not condemned
  sweep_phase_inv_elim g fp st;
  Paint.kept_heads g pm rm;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (painted_view g st st' rm));
  surviving_view_ok st';
  Paint.recoloured_wf rm rp v (surviving st');
  sweep_phase_inv_iff rp prom.Promote.fp_final st';
  // the shape for the minor collection, on the collection's view
  Paint.surviving_from_colour_blind st g;
  Paint.colour_blind_elim v rm rp;
  Paint.recoloured_major_shape rm rp res0.Promote.mc_fp v;
  GenInv.collection_shape_view_after_minor_reset v minor rp res0.Promote.mc_fp
#pop-options
