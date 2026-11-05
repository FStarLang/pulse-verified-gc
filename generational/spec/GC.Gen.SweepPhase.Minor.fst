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
let free_incremental_allocations_not_free c =
  let ph = Ph.Sweeping c in
  let prf (g: heap) (fp: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256}) (x: obj_addr)
    : Lemma (requires AP.alloc_ok g fp /\ (AP.alloc_at ph g fp wz tag).GC.Spec.Allocator.obj_out == x)
            (ensures not (free_incremental c (AP.alloc_at ph g fp wz tag).GC.Spec.Allocator.heap_out x))
    = AP.alloc_at_recoloured ph g fp wz tag;
      let h = (AP.alloc_at ph g fp wz tag).GC.Spec.Allocator.heap_out in
      hd_address_spec x;
      colour_of h x;
      assert (is_white x h ==> U64.v (hd_address x) < U64.v c);
      assert (not (pending_free c h x))
  in
  Promote.allocations_not_free_intro ph (free_incremental c) prf
#pop-options

/// ---------------------------------------------------------------------------
/// Step B
/// ---------------------------------------------------------------------------

let sweep_major_shape g fp c =
  sweep_inv_incremental_elim g fp c;
  free_incremental_ok c;
  free_incremental_allocations_not_free c;
  PCS.free_list_shape_of_ascending g fp;
  wf_with_parts ();
  GenInv.major_shape_with_intro (Ph.Sweeping c) (free_incremental c) g fp

let sweep_collection_shape minor g fp c =
  sweep_major_shape g fp c;
  GenInv.collection_shape_with_intro (Ph.Sweeping c) (free_incremental c) minor g fp

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

/// The invariant of the promotion run: the heap is in the sweep's shape, with
/// the pending-free set the collection started with.
let run_p (c: U64.t) (g: heap) (h: heap) (f: U64.t) : prop =
  sweep_shape h f c /\
  (forall (x: obj_addr). pending_free c h x == pending_free c g x)

#push-options "--z3rlimit 30 --ifuel 1"
let run_step (minor: minor_state) (c: U64.t) (g: heap)
  : CI.promote_keeps minor (Ph.Sweeping c) (run_p c g)
  = fun h f obj wz -> GSP.promote_sweep_shape h f c minor obj wz
#pop-options

#push-options "--z3rlimit 20"
let run_start (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires sweep_inv_incremental g fp c) (ensures run_p c g g fp /\ CI.alloc_ok g fp)
  = sweep_inv_incremental_iff g fp c;
    sweep_inv_incremental_elim g fp c;
    FLA.fl_ascending_valid g fp;
    part1_holds g
#pop-options

/// The promotions, then the pointer update.
#push-options "--z3rlimit 30"
let run_facts (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t) (roots: seq U64.t)
  : Lemma (requires sweep_inv_incremental g fp c /\
                    GenInv.minor_heap_shape minor /\
                    GenInv.minor_major_fields_not_free (free_incremental c) minor g)
          (ensures (let ph = Ph.Sweeping c in
                    let free = free_incremental c in
                    let prom = Cheney.cheney_promote ph minor g fp roots in
                    let res = collect_at c minor g fp roots in
                    run_p c g prom.Promote.major_final prom.Promote.fp_final /\
                    same_heads prom.Promote.major_final res.Promote.mc_major /\
                    res.Promote.mc_fp == prom.Promote.fp_final /\
                    GenInv.collection_shape_with ph free res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp))
  = let ph = Ph.Sweeping c in
    let free = free_incremental c in
    sweep_collection_shape minor g fp c;
    CV.cheney_collect_with_preserves_shape ph free minor g fp roots;
    let prom = Cheney.cheney_promote ph minor g fp roots in
    let pm = prom.Promote.major_final in
    let res = collect_at c minor g fp roots in
    let rm = res.Promote.mc_major in
    run_start g fp c;
    CI.cheney_promote_keeps minor ph (run_p c g) (run_step minor c g) g fp roots;
    ST.update_heads pm free prom.Promote.fwd_map;
    same_heads_facts pm rm
#pop-options

/// ---------------------------------------------------------------------------
/// Step C
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30"
let minor_keeps_sweep_phase minor g fp c roots =
  let ph = Ph.Sweeping c in
  let free = free_incremental c in
  run_facts minor g fp c roots;
  let prom = Cheney.cheney_promote ph minor g fp roots in
  let pm = prom.Promote.major_final in
  let res = collect_at c minor g fp roots in
  let rm = res.Promote.mc_major in
  // the shape: the pointer update keeps the walk and every header
  GenInv.collection_shape_with_elim ph free res.Promote.mc_minor rm res.Promote.mc_fp;
  GenInv.major_shape_with_elim ph free rm res.Promote.mc_fp;
  shape_transport pm rm prom.Promote.fp_final c;
  same_heads_facts pm rm;
  // well-formedness: the generic theorem's, at the same cursor
  sweep_inv_incremental_iff rm prom.Promote.fp_final c
#pop-options

let minor_keeps_pending_free minor g fp c roots x =
  minor_keeps_sweep_phase minor g fp c roots

#push-options "--z3rlimit 30"
let minor_keeps_blocks minor g fp c roots x =
  let ph = Ph.Sweeping c in
  let free = free_incremental c in
  sweep_collection_shape minor g fp c;
  GenInv.collection_shape_with_elim ph free minor g fp;
  GenInv.major_shape_with_elim ph free g fp;
  GenInv.minor_heap_shape_elim minor;
  minor_keeps_sweep_phase minor g fp c roots;
  let prom = Cheney.cheney_promote ph minor g fp roots in
  let pm = prom.Promote.major_final in
  let res = collect_at c minor g fp roots in
  let rm = res.Promote.mc_major in
  CS.cheney_promote_preserves_wfh_part1 ph minor g fp roots;
  CV.update_walk_keeps_in_use free pm (in_use free pm) prom.Promote.fwd_map x;
  assert (rm == Promote.update_walk pm (in_use free pm) prom.Promote.fwd_map);
  // an old non-free block keeps its header
  (if is_block g x && not (free_incremental c g x) then begin
     CV.cheney_promote_keeps_in_use ph free minor g fp roots x;
     Frame.cheney_promote_frame_old_header ph minor g fp roots x;
     GC.Gen.PromoteUpdate.update_walk_preserves_header pm (in_use free pm) prom.Promote.fwd_map x
   end);
  // a new one is a promoted copy
  FStar.Classical.move_requires (CV.cheney_promote_in_use_origin ph free minor g fp roots) x
#pop-options
