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
  pending_ok_lemma g st;
  PCS.free_list_shape_of_ascending g fp;
  wf_except_parts ();
  GenInv.major_shape_except_intro g fp (pending g st)

let sweep_collection_shape minor g fp st =
  sweep_major_shape g fp st;
  GenInv.collection_shape_except_intro minor g fp (pending g st)


/// ---------------------------------------------------------------------------
/// The pointer update keeps the walk and every header
/// ---------------------------------------------------------------------------

module Promote = GC.Gen.Promote
module PUO = GC.Gen.PromoteUpdate.Obj
module W = GC.Spec.Walk
module FLA = GC.Spec.FreeList.Ascending
module CE = GC.Gen.CheneyExcept
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
let rec uwa_heads (major: heap) (objs: seq obj_addr) (upd: obj_addr -> prop)
                  (fwd: Promote.forwarding_map) (idx: nat)
  : Lemma (requires objs == objects zero_addr major)
          (ensures same_heads major (Promote.update_walk_aux major objs upd fwd idx))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      let obj = Seq.index objs idx in
      if not (FStar.IndefiniteDescription.strong_excluded_middle (upd obj)) then
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

let update_heads (major: heap) (pf: obj_addr -> prop) (fwd: Promote.forwarding_map)
  : Lemma (same_heads major (Promote.update_pointers_except major pf fwd))
  = uwa_heads major (objects zero_addr major) (not_freed major pf) fwd 0

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
/// state the allocations have left, with the same pending set.
let run_inv (g: heap) (st: sweep_state) (h: heap) (f: U64.t) : prop =
  Paint.paint_ok g h f /\
  sweep_shape (Paint.paint (U64.v st.cursor) g h) f (st_at st h) /\
  (forall (x: obj_addr). pending (Paint.paint (U64.v st.cursor) g h) (st_at st h) x <==> pending g st x)

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

#push-options "--z3rlimit 30"
let minor_keeps_sweep_phase minor g fp st roots =
  let pf = pending g st in
  let c = U64.v st.cursor in
  let ph0 = Ph.Sweeping st in
  sweep_collection_shape minor g fp st;
  CE.cheney_collect_except_preserves_shape minor g fp roots pf;
  let res0 = Cheney.cheney_collect_spec_except minor g fp roots pf in
  let prom = Cheney.cheney_promote minor g fp roots in
  let pm = prom.Promote.major_final in
  let rm = res0.Promote.mc_major in
  // the promotions
  run_start g fp st;
  Cheney.cheney_promote_induction minor g fp roots (run_inv g st) (run_step minor g st);
  assert (run_inv g st pm prom.Promote.fp_final);
  // the pointer update
  update_heads pm pf prom.Promote.fwd_map;
  assert (rm == Promote.update_pointers_except pm pf prom.Promote.fwd_map);
  same_heads_facts pm rm;
  Paint.max_cell_below_congr pm rm (U64.v st.swept_tail);
  assert (st_at st rm == st_at st pm);
  paint_heads c g pm rm;
  let rp = Paint.paint c g rm in
  GenInv.collection_shape_except_elim res0.Promote.mc_minor rm res0.Promote.mc_fp pf;
  GenInv.major_shape_except_elim rm res0.Promote.mc_fp pf;
  Paint.paint_recoloured c g rm;
  Paint.recoloured_fl rm rp res0.Promote.mc_fp;
  shape_transport (Paint.paint c g pm) rp prom.Promote.fp_final (st_at st pm);
  same_heads_facts (Paint.paint c g pm) rp;
  // the field closure
  Paint.recoloured_wf rm rp pf;
  wf_except_parts ();
  Paint.recoloured_facts rm rp;
  wf_transport rp rp pf (pending rp (st_at st rm));
  sweep_phase_inv_iff rp prom.Promote.fp_final (st_at st rm);
  // the shape for the minor collection
  Paint.recoloured_major_shape rm rp res0.Promote.mc_fp pf;
  GenInv.collection_shape_except_after_minor_reset minor rp res0.Promote.mc_fp pf
#pop-options
