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
module Ph = GC.Spec.Phase
module AP = GC.Gen.AllocPhase
module AC = GC.Spec.Allocator.Cursor
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney
module ST = GC.Gen.SweptTail

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The allocator at the sweep's phase
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let free_incremental_allocations_not_free st =
  let ph = Ph.Sweeping st in
  let prf (g: heap) (fp: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256}) (x: obj_addr)
    : Lemma (requires AP.alloc_ok g fp /\ (AP.alloc_at ph g fp wz tag).GC.Spec.Allocator.obj_out == x)
            (ensures not (free_incremental st (AP.alloc_at ph g fp wz tag).GC.Spec.Allocator.heap_out x))
    = AP.alloc_at_recoloured ph g fp wz tag;
      let h = (AP.alloc_at ph g fp wz tag).GC.Spec.Allocator.heap_out in
      hd_address_spec x;
      colour_of h x;
      assert (is_white x h ==> U64.v (hd_address x) < U64.v st.cursor);
      assert (not (pending_free st h x))
  in
  Promote.allocations_not_free_intro ph (free_incremental st) prf
#pop-options

/// ---------------------------------------------------------------------------
/// Step B
/// ---------------------------------------------------------------------------

let sweep_major_shape g fp st =
  sweep_phase_inv_elim g fp st;
  free_incremental_ok st;
  free_incremental_allocations_not_free st;
  PCS.free_list_shape_of_ascending g fp;
  wf_with_parts ();
  GenInv.major_shape_with_intro (Ph.Sweeping st) (free_incremental st) g fp

let sweep_collection_shape minor g fp st =
  sweep_major_shape g fp st;
  GenInv.collection_shape_with_intro (Ph.Sweeping st) (free_incremental st) minor g fp

/// ---------------------------------------------------------------------------
/// The pointer update keeps the walk and every header
/// ---------------------------------------------------------------------------

module PUO = GC.Gen.PromoteUpdate.Obj
module W = GC.Spec.Walk
module FLA = GC.Spec.FreeList.Ascending
module CV = GC.Gen.CheneyGeneric
module CI = GC.Gen.Cheney.Induction
module CS = GC.Gen.Cheney.Steps
module Frame = GC.Gen.CheneyPreservation.Frame
module GSP = GC.Gen.SweepPhase
open GC.Spec.SweepPhase.Util
open GC.Spec.FusedSweep.Inv

/// ---------------------------------------------------------------------------
/// The promotions keep the sweep shape
/// ---------------------------------------------------------------------------

/// The invariant of the promotion run: the heap is in the sweep's shape at the
/// state the allocations have left, with the pending-free set the collection
/// started with.
let run_p (st: sweep_state) (g: heap) (h: heap) (f: U64.t) : prop =
  sweep_shape h f (state_after st h) /\
  (forall (x: obj_addr). pending_free st h x == pending_free st g x)

/// The phase the allocator holds is the state after the heap.
let phase_at_sweeping (st: sweep_state) (h: heap)
  : Lemma (ST.phase_at (Ph.Sweeping st) h == Ph.Sweeping (state_after st h))
  = ()

#push-options "--z3rlimit 30 --ifuel 1"
let run_step (minor: minor_state) (st: sweep_state) (g: heap)
  : CI.promote_keeps minor (Ph.Sweeping st) (run_p st g)
  = fun h f obj wz ->
    let ph = Ph.Sweeping st in
    let sth = state_after st h in
    let tag = Promote.promoted_tag minor obj in
    sweep_shape_elim h f sth;
    // the promotion at the collection's phase is the one at the phase the
    // allocator holds: only the cursor colours
    AP.alloc_at_cursor st sth h f wz tag;
    assert (Promote.promote_object minor h obj f wz ph ==
            Promote.promote_object minor h obj f wz (Ph.Sweeping sth));
    GSP.promote_sweep_shape h f sth minor obj wz;
    let r = Promote.promote_object minor h obj f wz ph in
    ST.promote_phase_at ph h f minor obj wz;
    phase_at_sweeping st h;
    phase_at_sweeping st r.Promote.major_out;
    assert (Ph.Sweeping (GSP.alloc_state h f wz sth) == Ph.Sweeping (state_after st r.Promote.major_out));
    assert (GSP.alloc_state h f wz sth == state_after st r.Promote.major_out)
#pop-options

#push-options "--z3rlimit 20"
let run_start (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st) (ensures run_p st g g fp /\ CI.alloc_ok g fp)
  = sweep_phase_inv_iff g fp st;
    sweep_phase_inv_elim g fp st;
    let c = U64.v st.cursor in
    tail_ok_elim g c st.swept_tail;
    ST.phase_at_self (Ph.Sweeping st) g;
    phase_at_sweeping st g;
    assert (state_after st g == st);
    FLA.fl_ascending_valid g fp;
    part1_holds g
#pop-options

/// The promotions, then the pointer update.
#push-options "--z3rlimit 30"
let run_facts (minor: minor_state) (g: heap) (fp: U64.t) (st: sweep_state) (roots: seq U64.t)
  : Lemma (requires sweep_phase_inv g fp st /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_free (free_incremental st) minor g)
          (ensures (let ph = Ph.Sweeping st in
                    let free = free_incremental st in
                    let prom = Cheney.cheney_promote ph minor g fp roots in
                    let res = collect_at st minor g fp roots in
                    let st' = state_after st res.Promote.mc_major in
                    run_p st g prom.Promote.major_final prom.Promote.fp_final /\
                    same_heads prom.Promote.major_final res.Promote.mc_major /\
                    st' == state_after st prom.Promote.major_final /\
                    res.Promote.mc_fp == prom.Promote.fp_final /\
                    GenInv.collection_shape_with ph free res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp))
  = let ph = Ph.Sweeping st in
    let free = free_incremental st in
    sweep_collection_shape minor g fp st;
    CV.cheney_collect_with_preserves_shape ph free minor g fp roots;
    let prom = Cheney.cheney_promote ph minor g fp roots in
    let pm = prom.Promote.major_final in
    let res = collect_at st minor g fp roots in
    let rm = res.Promote.mc_major in
    run_start g fp st;
    CI.cheney_promote_keeps minor ph (run_p st g) (run_step minor st g) g fp roots;
    ST.update_heads pm free prom.Promote.fwd_map;
    same_heads_facts pm rm;
    ST.phase_at_heads (Ph.Sweeping st) pm rm
#pop-options

/// ---------------------------------------------------------------------------
/// Step C
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30"
let minor_keeps_sweep_phase minor g fp st roots =
  let ph = Ph.Sweeping st in
  let free = free_incremental st in
  run_facts minor g fp st roots;
  let prom = Cheney.cheney_promote ph minor g fp roots in
  let pm = prom.Promote.major_final in
  let res = collect_at st minor g fp roots in
  let rm = res.Promote.mc_major in
  let st' = state_after st rm in
  phase_at_sweeping st rm;
  // the shape: the pointer update keeps the walk and every header
  GenInv.collection_shape_with_elim ph free res.Promote.mc_minor rm res.Promote.mc_fp;
  GenInv.major_shape_with_elim ph free rm res.Promote.mc_fp;
  shape_transport pm rm prom.Promote.fp_final st';
  same_heads_facts pm rm;
  // well-formedness: the generic theorem's, and the sweep state after has the
  // same cursor, so the same definition of free
  free_incremental_ok st';
  well_formed_heap_with_congr free (free_incremental st') rm;
  sweep_phase_inv_iff rm prom.Promote.fp_final st'
#pop-options

let minor_keeps_pending_free minor g fp st roots x =
  minor_keeps_sweep_phase minor g fp st roots

#push-options "--z3rlimit 30"
let minor_keeps_blocks minor g fp st roots x =
  let ph = Ph.Sweeping st in
  let free = free_incremental st in
  sweep_collection_shape minor g fp st;
  GenInv.collection_shape_with_elim ph free minor g fp;
  GenInv.major_shape_with_elim ph free g fp;
  GenInv.minor_heap_shape_elim minor;
  minor_keeps_sweep_phase minor g fp st roots;
  let prom = Cheney.cheney_promote ph minor g fp roots in
  let pm = prom.Promote.major_final in
  let res = collect_at st minor g fp roots in
  let rm = res.Promote.mc_major in
  let st' = state_after st rm in
  CS.cheney_promote_preserves_wfh_part1 ph minor g fp roots;
  CV.update_walk_keeps_in_use free pm (in_use free pm) prom.Promote.fwd_map x;
  assert (rm == Promote.update_walk pm (in_use free pm) prom.Promote.fwd_map);
  // what is non-free under the state after is what is non-free under `st`
  assert (in_use (free_incremental st') rm x == in_use free rm x);
  // an old non-free block keeps its header
  (if is_block g x && not (free_incremental st g x) then begin
     CV.cheney_promote_keeps_in_use ph free minor g fp roots x;
     Frame.cheney_promote_frame_old_header ph minor g fp roots x;
     GC.Gen.PromoteUpdate.update_walk_preserves_header pm (in_use free pm) prom.Promote.fwd_map x
   end);
  // a new one is a promoted copy
  FStar.Classical.move_requires (CV.cheney_promote_in_use_origin ph free minor g fp roots) x
#pop-options
