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
  free_incremental_ok st;
  free_incremental_from_ok st g;
  well_formed_heap_with_congr (free_incremental st) (free_incremental_from st g) g;
  PCS.free_list_shape_of_ascending g fp;
  wf_with_parts ();
  GenInv.major_shape_with_intro (free_incremental st) g fp;
  GenInv.major_shape_with_intro (free_incremental_from st g) g fp

let sweep_collection_shape minor g fp st =
  sweep_major_shape g fp st;
  GenInv.minor_major_fields_not_free_intro (free_incremental_from st g) minor g
    (fun obj j -> GenInv.minor_major_fields_not_free_elim (free_incremental st) minor g obj j);
  GenInv.collection_shape_with_intro (free_incremental_from st g) minor g fp


/// ---------------------------------------------------------------------------
/// The pointer update keeps the walk and every header
/// ---------------------------------------------------------------------------

module Promote = GC.Gen.Promote
module PUO = GC.Gen.PromoteUpdate.Obj
module W = GC.Spec.Walk
module FLA = GC.Spec.FreeList.Ascending
module CV = GC.Gen.CheneyWith
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

let update_heads (major: heap) (free: free_def) (fwd: Promote.forwarding_map)
  : Lemma (same_heads major (Promote.update_pointers_with free major fwd))
  = uwa_heads major (objects zero_addr major) (in_use free major) fwd 0

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
/// state the allocations have left, with the same pending-free set.
let run_inv (g: heap) (st: sweep_state) (h: heap) (f: U64.t) : prop =
  Paint.paint_ok g h f /\
  sweep_shape (Paint.paint (U64.v st.cursor) g h) f (st_at st h) /\
  (forall (x: obj_addr). pending_free (st_at st h) (Paint.paint (U64.v st.cursor) g h) x == pending_free st g x)

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

/// What is non-free in the painted result for `free_incremental` is what is
/// non-free in the idle one for the collection's definition of free.
#push-options "--z3rlimit 20"
let painted_in_use (g: heap) (st st': sweep_state) (rm: heap) (x: obj_addr)
  : Lemma (requires Paint.kept g rm /\ U64.v st.cursor % 8 == 0 /\ st'.cursor == st.cursor)
          (ensures in_use (free_incremental st') (Paint.paint (U64.v st.cursor) g rm) x == in_use (free_incremental_from st g) rm x)
  = Paint.paint_in_use st g rm x
#pop-options

#push-options "--z3rlimit 30"
let minor_keeps_sweep_phase minor g fp st roots =
  let free = free_incremental_from st g in
  let c = U64.v st.cursor in
  let ph0 = Ph.Sweeping st in
  sweep_collection_shape minor g fp st;
  let prom = Cheney.cheney_promote minor g fp roots in
  free_incremental_from_fresh st g prom.Promote.major_final;
  CV.cheney_collect_with_preserves_shape free minor g fp roots;
  let res0 = Cheney.cheney_collect_spec_with free minor g fp roots in
  let pm = prom.Promote.major_final in
  let rm = res0.Promote.mc_major in
  // the promotions
  run_start g fp st;
  Cheney.cheney_promote_induction minor g fp roots (run_inv g st) (run_step minor g st);
  assert (run_inv g st pm prom.Promote.fp_final);
  // the pointer update
  update_heads pm free prom.Promote.fwd_map;
  assert (rm == Promote.update_pointers_with free pm prom.Promote.fwd_map);
  same_heads_facts pm rm;
  Paint.max_cell_below_congr pm rm (U64.v st.swept_tail);
  assert (st_at st rm == st_at st pm);
  paint_heads c g pm rm;
  let rp = Paint.paint c g rm in
  let st' = st_at st rm in
  GenInv.collection_shape_with_elim free res0.Promote.mc_minor rm res0.Promote.mc_fp;
  GenInv.major_shape_with_elim free rm res0.Promote.mc_fp;
  Paint.paint_recoloured c g rm;
  Paint.recoloured_fl rm rp res0.Promote.mc_fp;
  shape_transport (Paint.paint c g pm) rp prom.Promote.fp_final st';
  same_heads_facts (Paint.paint c g pm) rp;
  // well-formedness for `free_incremental`: painting makes the promoted copies
  // in front of the cursor black, so not pending free
  sweep_phase_inv_elim g fp st;
  Paint.kept_heads g pm rm;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (painted_in_use g st st' rm));
  free_incremental_ok st';
  Paint.recoloured_wf rm rp free (free_incremental st');
  sweep_phase_inv_iff rp prom.Promote.fp_final st';
  // the shape for the minor collection, on the collection's definition of free
  Paint.free_incremental_from_colour_blind st g;
  Paint.colour_blind_elim free rm rp;
  Paint.recoloured_major_shape rm rp res0.Promote.mc_fp free;
  GenInv.collection_shape_with_after_minor_reset free minor rp res0.Promote.mc_fp
#pop-options

let minor_keeps_pending_free minor g fp st roots x =
  minor_keeps_sweep_phase minor g fp st roots

/// An old non-free block keeps its header through the update and the painting.
#push-options "--z3rlimit 20"
private let old_block_kept (g rm: heap) (c: nat) (x: obj_addr)
  : Lemma (requires Paint.kept g rm /\ is_block g x /\ not (is_blue x g))
          (ensures is_block (Paint.paint c g rm) x /\
                   read_word (Paint.paint c g rm) (hd_address x) == read_word g (hd_address x))
  = let rp = Paint.paint c g rm in
    obj_pos g x; colour_of g x; obj_pos rm x;
    Paint.paint_read c g rm (hd_address x);
    Paint.paint_recoloured c g rm;
    Paint.recoloured_facts rm rp;
    obj_pos rp x
#pop-options

/// The idle collection, its painted heap, and the facts the block lemmas read.
#push-options "--z3rlimit 30"
private let collection_facts (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state)
                             (roots: seq U64.t)
  : Lemma (requires sweep_phase_inv g fp st /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_free (free_incremental st) minor g)
          (ensures (let free = free_incremental_from st g in
                    let prom = Cheney.cheney_promote minor g fp roots in
                    let pm = prom.Promote.major_final in
                    let rm = (Cheney.cheney_collect_spec_with free minor g fp roots).Promote.mc_major in
                    free_def_ok free /\ CV.promote_pre minor g fp /\ blocks_fit pm /\
                    rm == Promote.update_walk pm (in_use free pm) prom.Promote.fwd_map /\
                    Paint.kept g rm))
  = let free = free_incremental_from st g in
    sweep_major_shape g fp st;
    GenInv.major_shape_with_elim free g fp;
    GenInv.minor_heap_shape_elim minor;
    free_incremental_from_ok st g;
    let prom = Cheney.cheney_promote minor g fp roots in
    let pm = prom.Promote.major_final in
    let rm = (Cheney.cheney_collect_spec_with free minor g fp roots).Promote.mc_major in
    run_start g fp st;
    Cheney.cheney_promote_induction minor g fp roots (run_inv g st) (run_step minor g st);
    assert (run_inv g st pm prom.Promote.fp_final);
    update_heads pm free prom.Promote.fwd_map;
    Paint.kept_heads g pm rm;
    sweep_collection_shape minor g fp st;
    GenInv.collection_shape_with_elim free minor g fp;
    CV.cheney_promote_preserves_wf_with free minor g fp roots;
    wf_with_parts ()
#pop-options

#push-options "--z3rlimit 20"
let minor_keeps_blocks minor g fp st roots x =
  let free = free_incremental_from st g in
  let c = U64.v st.cursor in
  let prom = Cheney.cheney_promote minor g fp roots in
  let pm = prom.Promote.major_final in
  let rm = (Cheney.cheney_collect_spec_with free minor g fp roots).Promote.mc_major in
  let st' = st_at st rm in
  collection_facts minor g fp st roots;
  sweep_phase_inv_elim g fp st;
  // what is non-free in the painted heap is what is non-free in `pm` for `free`
  painted_in_use g st st' rm x;
  CV.update_walk_keeps_in_use free pm (in_use free pm) prom.Promote.fwd_map x;
  assert (in_use (free_incremental st') (Paint.paint c g rm) x == in_use free pm x);
  // an old non-free block
  (if is_block g x && not (free_incremental st g x) then begin
     old_block_kept g rm c x;
     CV.cheney_promote_keeps_in_use free minor g fp roots x
   end);
  // a new one
  FStar.Classical.move_requires (CV.cheney_promote_in_use_origin free minor g fp roots) x
#pop-options
