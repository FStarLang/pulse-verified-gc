module GC.Gen.Run.Invariant.Minor

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant.Defs

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module MPC = GC.Spec.MarkPhase.Completeness
module MM = GC.Spec.MarkPhase.Mutator
module SPC = GC.Spec.SweepPhase.Completeness
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPMut = GC.Spec.SweepPhase.Mutator
module Util = GC.Spec.SweepPhase.Util
module LL = GC.Spec.FusedSweep.Lossless
module W = GC.Spec.Walk
module AP = GC.Spec.Allocator.Phase
module SA = GC.Spec.Allocator
module FLA = GC.Spec.FreeList.Ascending
module Asc = GC.Spec.Allocator.Ascending
module GI = GC.Gen.Incremental
module RT = GC.Gen.RefTable
module GenInv = GC.Gen.HeapInvariant
module GMC = GC.Gen.MarkPhase.Completeness
module GMM = GC.Gen.MarkPhase.Minor
module MW = GC.Gen.MarkPhase.Walk
module GSM = GC.Gen.SweepPhase.Minor
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney
module CI = GC.Gen.Cheney.Induction
module CV = GC.Gen.CheneyGeneric
module CS = GC.Gen.Cheney.Steps
module CP = GC.Gen.CheneyPreservation
module Frame = GC.Gen.CheneyPreservation.Frame
module PUpd = GC.Gen.PromoteUpdate
module ST = GC.Gen.SweptTail
module WB = GC.Gen.WriteBodyLemmas
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module MRT = GC.Gen.Run.MinorRefTable

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The walk, at any phase (`GC.Gen.MarkPhase.Walk.minor_reaches`, generalised)
/// ---------------------------------------------------------------------------

/// Copying into the body of a block that is not free keeps the walk, every
/// header, and an ascending free list.  (Copied from `GC.Gen.MarkPhase.Walk`.)
#push-options "--z3rlimit 20"
let rec copy_heads (g: heap) (fp: U64.t) (minor: minor_state) (src: U64.t) (dst: obj_addr) (i n: nat)
  : Lemma (requires Seq.mem dst (objects zero_addr g) /\ ~(is_blue dst g) /\
                    n <= U64.v (wosize_of_object dst g))
          (ensures (let g' = WB.copy_fields minor g src dst i n in
                    SPI.same_heads g g' /\ (FLA.fl_ascending g fp ==> FLA.fl_ascending g' fp)))
          (decreases (n - i))
  = if i >= n then begin
      WB.copy_fields_base minor g src dst i n;
      SPMut.same_heads_refl g
    end else begin
      Util.part1_holds g;
      wfh_part1_obj_bound g dst;
      hd_address_spec dst;
      let a : hp_addr = U64.uint_to_t (U64.v dst + i * 8) in
      let v = minor_read_field minor src i in
      WB.copy_fields_step minor g src dst i n;
      let g1 = write_word g a v in
      SPI.obj_pos g dst;
      SPI.colour_of g dst;
      SPI.body_write g fp (hd_address dst) a v;
      SPI.same_heads_facts g g1;
      SPI.colour_of g1 dst;
      copy_heads g1 fp minor src dst (i + 1) n;
      SPMut.same_heads_trans g g1 (WB.copy_fields minor g1 src dst (i + 1) n)
    end
#pop-options

let keeps_e (e: nat) (h: heap) (f: U64.t) : prop =
  W.reaches h zero_addr e /\ FLA.fl_ascending h f /\ e <= heap_size

#push-options "--z3rlimit 30"
let promote_step_at (ph: Ph.gc_phase) (minor: minor_state) (e: nat) : CI.promote_keeps minor ph (keeps_e e) =
  fun h f obj wz ->
    let tag = Promote.promoted_tag minor obj in
    MW.alloc_reaches ph h f wz tag e;
    AP.alloc_at_recoloured ph h f wz tag;
    AP.alloc_at_obj_wosize ph h f wz tag;
    AP.alloc_at_fields ph h f wz tag;
    Asc.alloc_spec_preserves_fl_ascending h f wz tag;
    let r = AP.alloc_at ph h f wz tag in
    let r0 = SA.alloc_spec h f wz tag in
    AP.recoloured_fl r0.SA.heap_out r.SA.heap_out r.SA.fp_out;
    let dst : obj_addr = r.SA.obj_out in
    copy_heads r.SA.heap_out r.SA.fp_out minor obj dst 0 wz;
    SPI.same_heads_facts r.SA.heap_out (WB.copy_fields minor r.SA.heap_out obj dst 0 wz)
#pop-options

/// **A minor collection at any phase keeps a position of the walk.**
let minor_reaches_at (ph: Ph.gc_phase) (pf: free_def) (minor: minor_state) (g: heap) (fp: U64.t)
                     (roots: seq U64.t) (e: nat)
  : Lemma (requires AP.alloc_ok g fp /\ FLA.fl_ascending g fp /\ W.reaches g zero_addr e /\ e <= heap_size)
          (ensures W.reaches (Cheney.cheney_collect_spec_with ph pf minor g fp roots).Promote.mc_major zero_addr e)
  = CI.cheney_promote_keeps minor ph (keeps_e e) (promote_step_at ph minor e) g fp roots;
    let prom = Cheney.cheney_promote ph minor g fp roots in
    ST.update_heads prom.Promote.major_final pf prom.Promote.fwd_map

/// ---------------------------------------------------------------------------
/// What the collection does to the major heap, at any phase
/// ---------------------------------------------------------------------------

/// The shape before, taken apart.
#push-options "--z3rlimit 20"
let shape_parts (m: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (sp: MP.scan_pos)
  : Lemma (requires GI.phase_shape m g fp ph sp)
          (ensures (let pf = GI.phase_free ph in
                    free_def_ok pf /\ well_formed_heap_with pf g /\
                    (forall (g: heap) (x: obj_addr). {:pattern (in_use pf g x)}
                       in_use pf g x ==> Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                    blocks_fit g /\ no_infix_block g /\
                    AP.alloc_ok g fp /\ FLA.fl_ascending g fp /\ CV.promote_pre m g fp /\
                    heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0))
  = let pf = GI.phase_free ph in
    GI.phase_shape_collection m g fp ph sp;
    GenInv.collection_shape_with_elim ph pf m g fp;
    GenInv.major_shape_with_elim ph pf g fp;
    GenInv.minor_heap_shape_elim m
#pop-options

/// An allocated block stays, with its header.
#push-options "--z3rlimit 20"
let keep_block (ph: Ph.gc_phase) (pf: free_def) (m: minor_state) (g: heap) (fp: U64.t) (rs: seq U64.t)
               (y: obj_addr)
  : Lemma (requires CV.promote_pre m g fp /\ Seq.mem y (objects zero_addr g) /\ ~(is_blue y g))
          (ensures (let g' = (Cheney.cheney_collect_spec_with ph pf m g fp rs).Promote.mc_major in
                    Seq.mem y (objects zero_addr g') /\ read_word g' (hd_address y) == read_word g (hd_address y)))
  = let p = Cheney.cheney_promote ph m g fp rs in
    let pm = p.Promote.major_final in
    free_stw_ok ();
    free_def_ok_elim free_stw;
    CV.cheney_promote_keeps_in_use ph free_stw m g fp rs y;
    Frame.cheney_promote_frame_old_header ph m g fp rs y;
    CS.cheney_promote_preserves_wfh_part1 ph m g fp rs;
    PUpd.update_walk_preserves_objects pm (in_use pf pm) p.Promote.fwd_map;
    PUpd.update_walk_preserves_header pm (in_use pf pm) p.Promote.fwd_map y
#pop-options

/// Every allocated block of `g` is a block of `g'` with the same header.
let blocks_kept (g g': heap) : prop =
  forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) ==>
    Seq.mem x (objects zero_addr g') /\ read_word g' (hd_address x) == read_word g (hd_address x)

/// The collection keeps the allocated blocks and the walk's end.
#push-options "--z3rlimit 20"
let collect_facts (r: real_state) (roots: seq U64.t) (r': real_state)
  : Lemma (requires phase_shape r /\ minor_step r roots r')
          (ensures blocks_kept r.memory.major r'.memory.major /\
                   W.walk_end r'.memory.major zero_addr == W.walk_end r.memory.major zero_addr)
  = let m = r.memory.nursery in
    let g = r.memory.major in
    let fp = r.free_list in
    let rs = collector_roots r roots in
    let ph = r.phase in
    let pf = GI.phase_free ph in
    shape_parts m g fp ph r.scan_pos;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (keep_block ph pf m g fp rs));
    let e = W.walk_end g zero_addr in
    W.reaches_walk_end g zero_addr;
    W.reaches_bounds g zero_addr e;
    minor_reaches_at ph pf m g fp rs e;
    W.walk_end_of_reaches r'.memory.major zero_addr e
#pop-options

/// A kept block keeps its colour, size and extent.
let old_kept (g g': heap) (x: obj_addr)
  : Lemma (requires blocks_kept g g' /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
          (ensures Seq.mem x (objects zero_addr g') /\ ~(is_blue x g') /\
                   wosize_of_object x g' == wosize_of_object x g /\
                   (is_black x g' <==> is_black x g) /\ (is_white x g' <==> is_white x g) /\
                   (is_gray x g' <==> is_gray x g) /\
                   (forall (p: nat). LL.in_extent g' x p <==> LL.in_extent g x p))
  = MM.header_kept_facts g g' x

/// ---------------------------------------------------------------------------
/// The collector's state after, at each phase
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let idle_shape (r: real_state) (roots: seq U64.t) (r': real_state)
  : Lemma (requires phase_shape r /\ minor_step r roots r' /\ r.phase == Ph.Idle)
          (ensures GI.phase_shape r'.memory.nursery r'.memory.major r'.free_list r'.phase r'.scan_pos)
  = let m = r.memory.nursery in
    let g = r.memory.major in
    let fp = r.free_list in
    let rs = collector_roots r roots in
    GI.phase_free_idle ();
    CV.cheney_collect_spec_with_stw m g fp rs;
    GI.phase_shape_idle m g fp r.scan_pos;
    CP.cheney_collect_preserves_collection_heap_shape m g fp rs;
    GI.phase_shape_idle r'.memory.nursery r'.memory.major r'.free_list r'.scan_pos

let marking_shape (r: real_state) (roots: seq U64.t) (r': real_state)
  : Lemma (requires phase_shape r /\ minor_step r roots r' /\ r.phase == Ph.Marking)
          (ensures GI.phase_shape r'.memory.nursery r'.memory.major r'.free_list r'.phase r'.scan_pos /\
                   MCFH.roots_valid_for_minor_collection r.memory.nursery r.memory.major (collector_roots r roots) /\
                   r'.memory.major == (GMM.collect_marking r.memory.nursery r.memory.major r.free_list
                                         (collector_roots r roots)).Promote.mc_major)
  = let m = r.memory.nursery in
    let g = r.memory.major in
    let fp = r.free_list in
    let rs = collector_roots r roots in
    GI.phase_free_marking ();
    GI.minor_keeps_marking_shape m g fp rs r.scan_pos

let sweeping_shape (r: real_state) (roots: seq U64.t) (r': real_state) (c: U64.t)
  : Lemma (requires phase_shape r /\ minor_step r roots r' /\ r.phase == Ph.Sweeping c)
          (ensures GI.phase_shape r'.memory.nursery r'.memory.major r'.free_list r'.phase r'.scan_pos /\
                   (forall (x: obj_addr). SPI.pending_free c r'.memory.major x == SPI.pending_free c r.memory.major x))
  = let m = r.memory.nursery in
    let g = r.memory.major in
    let fp = r.free_list in
    let rs = collector_roots r roots in
    GI.phase_free_sweeping c;
    GI.minor_keeps_phase_shape m g fp c rs r.scan_pos
#pop-options

#push-options "--ifuel 1"
let gi_shape (r: real_state) (roots: seq U64.t) (r': real_state)
  : Lemma (requires phase_shape r /\ minor_step r roots r')
          (ensures GI.phase_shape r'.memory.nursery r'.memory.major r'.free_list r'.phase r'.scan_pos)
  = match r.phase with
    | Ph.Idle -> idle_shape r roots r'
    | Ph.Marking -> marking_shape r roots r'
    | Ph.Sweeping c -> sweeping_shape r roots r' c
#pop-options

/// **The shape after.**
#push-options "--z3rlimit 20"
let shape_after (r: real_state) (roots: seq U64.t) (r': real_state)
  : Lemma (requires phase_shape r /\ minor_step r roots r')
          (ensures phase_shape r' /\ blocks_kept r.memory.major r'.memory.major /\
                   W.walk_end r'.memory.major zero_addr == W.walk_end r.memory.major zero_addr)
  = gi_shape r roots r';
    collect_facts r roots r';
    MRT.minor_ref_table_empty r roots r';
    FStar.Classical.forall_intro (minor_reset_objects_not_mem r.memory.nursery)
#pop-options

/// ---------------------------------------------------------------------------
/// The accounting
/// ---------------------------------------------------------------------------

let hist (h: cycle_history) (r: real_state) (roots: seq U64.t) (r': real_state)
  : Lemma (let h' = update_history h r (Minor roots) r' in
           h'.start_memory == h.start_memory /\ h'.start_roots == h.start_roots /\
           (forall (x: obj_addr). h'.allocated_during_cycle x <==> h.allocated_during_cycle x \/ made r r' x) /\
           (forall (x: obj_addr). snapshot h' x <==> snapshot h x) /\
           (forall (x: obj_addr). kept h' x <==> kept h x \/ made r r' x) /\
           (forall (x: obj_addr). garbage_at_start h' x <==> garbage_at_start h x) /\
           (forall (p: nat). reclaimable_at_start h' p <==> reclaimable_at_start h p))
  = ()

/// The context: the invariant before, the step, and what the collection does.
let ctx (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state) : prop =
  run_invariant r h /\ minor_step r roots r' /\ phase_shape r' /\
  blocks_kept r.memory.major r'.memory.major /\
  W.walk_end r'.memory.major zero_addr == W.walk_end r.memory.major zero_addr

let kept_alloc (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state) (x: obj_addr)
  : Lemma (requires ctx r h roots r' /\ kept h x)
          (ensures is_allocated r.memory (Major x))
  = ()

/// B2-B4.
#push-options "--z3rlimit 20"
let b2_b4 (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state)
  : Lemma (requires ctx r h roots r')
          (ensures (let h' = update_history h r (Minor roots) r' in
                    let g = r'.memory.major in
                    let g0 = h'.start_memory.major in
                    (forall (x: obj_addr). snapshot h' x ==>
                       Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ wosize_of_object x g == wosize_of_object x g0) /\
                    (forall (x: obj_addr). garbage_at_start h' x /\ is_allocated r'.memory (Major x) /\ ~(h'.allocated_during_cycle x) ==>
                       wosize_of_object x g == wosize_of_object x g0) /\
                    W.walk_end g zero_addr == W.walk_end g0 zero_addr /\
                    (forall (x: obj_addr). h'.allocated_during_cycle x ==> is_allocated r'.memory (Major x) /\ ~(snapshot h' x)) /\
                    (forall (x: obj_addr). is_allocated r'.memory (Major x) ==>
                       snapshot h' x \/ h'.allocated_during_cycle x \/ garbage_at_start h' x)))
  = hist h r roots r';
    FStar.Classical.forall_intro (FStar.Classical.move_requires (old_kept r.memory.major r'.memory.major))
#pop-options

/// A word of a block of `g'` that was not an allocated block of `g` was
/// free in `g`.
#push-options "--z3rlimit 20"
let new_word (g g': heap) (y: obj_addr) (p: nat)
  : Lemma (requires blocks_kept g g' /\ W.walk_end g' zero_addr == W.walk_end g zero_addr /\
                    W.walk_end g' zero_addr + 8 >= heap_size /\
                    Seq.mem y (objects zero_addr g') /\ LL.in_extent g' y p /\
                    ~(Seq.mem y (objects zero_addr g) /\ ~(is_blue y g)))
          (ensures LL.blue_covered g p)
  = SPC.extent_below_end g' y p;
    let z = SPC.block_over g p in
    if is_blue z g then ()
    else begin
      old_kept g g' z;
      if z = y then () else SPC.extents_disjoint g' z y p
    end
#pop-options

/// B5.
#push-options "--z3rlimit 20"
let b5_word (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state) (p: nat)
  : Lemma (requires ctx r h roots r' /\
                    (LL.blue_covered r'.memory.major p \/
                     SPC.new_covered (update_history h r (Minor roots) r').allocated_during_cycle r'.memory.major p))
          (ensures reclaimable_at_start (update_history h r (Minor roots) r') p)
  = let h' = update_history h r (Minor roots) r' in
    let g = r.memory.major in
    let g' = r'.memory.major in
    hist h r roots r';
    let one (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\ LL.in_extent g' y p /\
                        (is_blue y g' \/ h'.allocated_during_cycle y))
              (ensures LL.blue_covered g p \/ SPC.new_covered h.allocated_during_cycle g p)
      = if Seq.mem y (objects zero_addr g) && not (is_blue y g) then old_kept g g' y
        else new_word g g' y p
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one);
    assert (LL.blue_covered g p \/ SPC.new_covered h.allocated_during_cycle g p)
#pop-options

let b5 (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state)
  : Lemma (requires ctx r h roots r')
          (ensures (forall (p: nat). LL.blue_covered r'.memory.major p \/
                       SPC.new_covered (update_history h r (Minor roots) r').allocated_during_cycle r'.memory.major p ==>
                     reclaimable_at_start (update_history h r (Minor roots) r') p))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (b5_word r h roots r'))

/// The emptied nursery points nowhere.
let reset_points_nowhere (free: free_def) (m: minor_state) (g: heap)
  : Lemma (GenInv.minor_major_fields_not_free free (minor_reset m) g)
  = let f (obj: U64.t) (j: nat)
      : Lemma (requires Seq.mem obj (minor_objects (minor_reset m)) /\ j < minor_scan_wosize (minor_reset m) obj /\
                        is_pointer_field (minor_read_field (minor_reset m) obj j))
              (ensures in_use free g (resolve_object ((minor_read_field (minor_reset m) obj j) <: obj_addr) g) /\
                       infix_addr_wf g (objects zero_addr g) ((minor_read_field (minor_reset m) obj j) <: obj_addr))
      = minor_reset_objects_not_mem m obj
    in
    GenInv.minor_major_fields_not_free_intro free (minor_reset m) g f

/// ---------------------------------------------------------------------------
/// Idle
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let idle_after (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state)
  : Lemma (requires ctx r h roots r' /\ r.phase == Ph.Idle)
          (ensures (let h' = update_history h r (Minor roots) r' in
                    (forall (x: obj_addr). is_allocated r'.memory (Major x) ==> kept h' x) /\
                    MPC.within_snapshot (kept h') r'.memory.major))
  = let h' = update_history h r (Minor roots) r' in
    let k = kept h' in
    let g' = r'.memory.major in
    hist h r roots r';
    assert (forall (x: obj_addr). is_allocated r'.memory (Major x) ==> kept h' x);
    GI.phase_free_idle ();
    shape_parts r'.memory.nursery g' r'.free_list Ph.Idle r'.scan_pos;
    MPC.outside_snapshot_ok k;
    let eq (x: obj_addr) : Lemma (in_use (MPC.outside_snapshot k) g' x == in_use free_stw g' x)
      = MPC.in_use_outside_snapshot k g' x
    in
    FStar.Classical.forall_intro eq;
    SPI.wf_transport g' g' free_stw (MPC.outside_snapshot k);
    let dark (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g') /\ (is_gray x g' \/ is_black x g')) (ensures k x)
      = Mark.colors_exclusive x g'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires dark)
#pop-options

/// ---------------------------------------------------------------------------
/// Mid-sweep
/// ---------------------------------------------------------------------------

let sweep_ctx (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state) (c: U64.t) : prop =
  ctx r h roots r' /\ r.phase == Ph.Sweeping c /\
  SPI.sweep_inv_incremental r'.memory.major r'.free_list c /\
  (forall (x: obj_addr). SPI.pending_free c r'.memory.major x == SPI.pending_free c r.memory.major x)

let sweep_ctx_intro (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state) (c: U64.t)
  : Lemma (requires ctx r h roots r' /\ r.phase == Ph.Sweeping c)
          (ensures sweep_ctx r h roots r' c)
  = sweeping_shape r roots r' c;
    GI.phase_shape_sweeping r'.memory.nursery r'.memory.major r'.free_list c r'.scan_pos

/// A block not free mid-sweep after is kept.
#push-options "--z3rlimit 20"
let sweep_in_after (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state) (c: U64.t) (x: obj_addr)
  : Lemma (requires sweep_ctx r h roots r' c /\ in_use (SPI.free_incremental c) r'.memory.major x)
          (ensures kept (update_history h r (Minor roots) r') x)
  = let g = r.memory.major in
    let g' = r'.memory.major in
    hist h r roots r';
    SPI.free_incremental_ok c;
    free_def_ok_elim (SPI.free_incremental c);
    if Seq.mem x (objects zero_addr g) && not (is_blue x g) then begin
      old_kept g g' x;
      in_use_is_determined_from_header (SPI.free_incremental c) g g' x
    end
#pop-options

/// An object past the cursor has its header at or past it.
let past_cursor (x: obj_addr) (c: U64.t)
  : Lemma (requires U64.v c % 8 == 0 /\ U64.v x > U64.v c)
          (ensures U64.v (hd_address x) >= U64.v c)
  = hd_address_spec x;
    FStar.Math.Lemmas.lemma_div_exact (U64.v x) 8;
    FStar.Math.Lemmas.lemma_div_exact (U64.v c) 8

/// A kept block past the cursor is black after.
#push-options "--z3rlimit 20"
let black_after (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state) (c: U64.t) (x: obj_addr)
  : Lemma (requires sweep_ctx r h roots r' c /\ kept (update_history h r (Minor roots) r') x /\ U64.v x > U64.v c)
          (ensures is_black x r'.memory.major)
  = let g = r.memory.major in
    let g' = r'.memory.major in
    hist h r roots r';
    Mark.colors_exclusive x g;
    if Seq.mem x (objects zero_addr g) && not (is_blue x g) then old_kept g g' x
    else begin
      assert (made r r' x);
      assert (not (SPI.pending_free c g x));
      assert (not (SPI.pending_free c g' x));
      Mark.colors_exclusive x g';
      SPI.obj_pos g' x;
      SPI.colour_of g' x;
      SPI.sweep_inv_incremental_elim g' r'.free_list c;
      past_cursor x c;
      SPI.front_unswept_elim g' (U64.v c) (hd_address x)
    end
#pop-options

#push-options "--z3rlimit 30"
let sweep_after (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state) (c: U64.t)
  : Lemma (requires sweep_ctx r h roots r' c)
          (ensures (let h' = update_history h r (Minor roots) r' in
                    MPC.sweep_in_snapshot (kept h') r'.memory.major c /\
                    (forall (x: obj_addr). kept h' x /\ U64.v x > U64.v c ==> is_black x r'.memory.major) /\
                    MPC.within_snapshot (kept h') r'.memory.major))
  = let h' = update_history h r (Minor roots) r' in
    let k = kept h' in
    let g' = r'.memory.major in
    let fi = SPI.free_incremental c in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (sweep_in_after r h roots r' c));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (black_after r h roots r' c));
    GI.phase_free_sweeping c;
    shape_parts r'.memory.nursery g' r'.free_list (Ph.Sweeping c) r'.scan_pos;
    MPC.outside_snapshot_ok k;
    let eq (x: obj_addr) : Lemma (in_use (MPC.outside_snapshot k) g' x == in_use fi g' x)
      = MPC.in_use_outside_snapshot k g' x;
        Mark.colors_exclusive x g'
    in
    FStar.Classical.forall_intro eq;
    SPI.wf_transport g' g' fi (MPC.outside_snapshot k);
    let dark (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g') /\ (is_gray x g' \/ is_black x g')) (ensures k x)
      = Mark.colors_exclusive x g'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires dark)
#pop-options

/// ---------------------------------------------------------------------------
/// Marking
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30"
let marking_after (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state)
  : Lemma (requires ctx r h roots r' /\ r.phase == Ph.Marking)
          (ensures (let h' = update_history h r (Minor roots) r' in
                    MPC.within_snapshot (kept h') r'.memory.major /\
                    MP.outside_refs_reached r'.memory.major r'.scan_pos (snapshot h') /\
                    (forall (x: obj_addr). h'.allocated_during_cycle x ==> is_black x r'.memory.major)))
  = let h' = update_history h r (Minor roots) r' in
    let m = r.memory.nursery in
    let g = r.memory.major in
    let g' = r'.memory.major in
    let fp = r.free_list in
    let sp = r.scan_pos in
    let rs = collector_roots r roots in
    hist h r roots r';
    marking_shape r roots r';
    GI.phase_shape_marking m g fp sp;
    // B1
    GMC.account_minor (kept h) m g fp rs sp;
    MPC.within_snapshot_ext (GMC.with_new_blocks (kept h) g g') (kept h') g';
    // what the marker will reach
    assert (MP.marking_inv g (fun w -> GMM.outside_refs_of m g rs w \/ snapshot h w) sp);
    GMM.minor_keeps_marking_inv_with (snapshot h) m g fp rs sp;
    // the blocks allocated during the cycle are black
    let blk (x: obj_addr)
      : Lemma (requires h'.allocated_during_cycle x) (ensures is_black x g')
      = if Seq.mem x (objects zero_addr g) && not (is_blue x g) then old_kept g g' x
        else GMM.minor_new_block_black m g fp rs x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires blk)
#pop-options

/// ---------------------------------------------------------------------------
/// The lemma
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --ifuel 1"
let minor_keeps r h roots r' =
  let h' = update_history h r (Minor roots) r' in
  shape_after r roots r';
  b2_b4 r h roots r';
  b5 r h roots r';
  hist h r roots r';
  reset_points_nowhere (MPC.outside_snapshot (kept h')) r.memory.nursery r'.memory.major;
  match r.phase with
  | Ph.Idle -> idle_after r h roots r'
  | Ph.Marking -> marking_after r h roots r'
  | Ph.Sweeping c -> sweep_ctx_intro r h roots r' c; sweep_after r h roots r' c
#pop-options
