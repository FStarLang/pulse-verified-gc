module GC.Gen.MarkPhase.Safety

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module GI = GC.Gen.Incremental
module GMM = GC.Gen.MarkPhase.Minor
module SPI = GC.Spec.SweepPhase.Intrinsic
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant
module GB = GC.Gen.Barrier
module MStart = GC.Gen.MarkPhase.Start
module MBP = GC.Impl.MarkBoundedPrecondition
module MB = GC.Impl.MarkBounded
module MM = GC.Spec.MarkPhase.Mutator
module SPMut = GC.Spec.SweepPhase.Mutator
module S = GC.Spec.MarkPhase.Slice
module W = GC.Spec.Walk
module MPC = GC.Spec.MarkPhase.Completeness
module SL = GC.Spec.SweepPhase.Slice
module SPE = GC.Spec.SweepPhase.Intrinsic.End

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// What every phase's state gives: the heap well formed for the phase's
/// definition of free, and the nursery's shape.
let phase_facts (minor: minor_state) (g: heap) (fp: U64.t) (ph: Ph.gc_phase)
  : Lemma (requires GI.phase_shape minor g fp ph)
          (ensures free_def_ok (GI.phase_free ph) /\ well_formed_heap_with (GI.phase_free ph) g /\
                   minor_wf minor /\ GenInv.minor_major_fields_not_free (GI.phase_free ph) minor g)
  = GI.phase_shape_collection minor g fp ph;
    GenInv.collection_shape_with_elim ph (GI.phase_free ph) minor g fp;
    GenInv.major_shape_with_elim ph (GI.phase_free ph) g fp;
    GenInv.minor_heap_shape_elim minor

let cycle_reachable_not_free minor g fp ph roots a =
  phase_facts minor g fp ph;
  RBridge.reachable_not_free (GI.phase_free ph) minor g roots

let handover_roots minor g fp rs =
  GI.phase_shape_marking minor g fp;
  SPI.free_incremental_ok zero_addr;
  wf_with_parts ();
  let one (r: U64.t)
    : Lemma (Seq.mem r rs /\ ~(GC.Gen.Promote.is_minor_pointer r) /\ is_val_addr r ==>
             (is_block g (r <: obj_addr) ==> not (SPI.free_incremental zero_addr g (r <: obj_addr))))
    = if Seq.mem r rs && is_val_addr r then begin
        let ro : obj_addr = r in
        if is_block g ro then begin
          objects_addresses_gt_start zero_addr g ro;
          RBridge.aligned_gt_ge_plus_mword (U64.v ro) (U64.v zero_addr);
          resolve_non_infix ro g;
          assert (GMM.roots_held g rs ro);
          if is_white ro g then MP.marker_will_reach_elim g ro
        end
      end
  in
  FStar.Classical.forall_intro one

#push-options "--ifuel 1"
let cycle_slice_keeps minor g fp ph budget g' fp' ph' x =
  match ph with
  | Ph.Marking ->
      GI.phase_shape_marking minor g fp;
      GI.phase_free_marking ();
      MPC.mark_steps_keep_blocks g g';
      S.mark_steps_darker g g';
      (match ph' with
       | Ph.Marking -> ()
       | Ph.Sweeping c -> GI.phase_free_sweeping c; SPI.free_incremental_ok c
       | Ph.Idle -> ())
  | Ph.Idle ->
      GI.phase_free_idle ()
  | Ph.Sweeping c ->
      GI.phase_shape_sweeping minor g fp c;
      GI.phase_free_sweeping c;
      SPI.free_incremental_ok c;
      free_def_ok_elim (SPI.free_incremental c);
      SL.sweep_slice_phase g fp c budget;
      let (g1, fp1, st1) = SL.sweep_slice g fp (SPI.state_at g c) budget in
      let c1 = st1.GC.Spec.FusedSweep.cursor in
      SPI.free_incremental_ok c1;
      free_def_ok_elim (SPI.free_incremental c1);
      if SPI.sweep_done c1 then GI.phase_free_idle ()
      else GI.phase_free_sweeping c1
#pop-options

let slice_keeps_reachable minor g fp ph budget g' fp' ph' roots a =
  cycle_reachable_not_free minor g fp ph roots a;
  cycle_slice_keeps minor g fp ph budget g' fp' ph' (a <: obj_addr)

/// Darkening the first `idx` roots keeps every block.
#push-options "--fuel 1 --ifuel 1"
let rec start_prefix_blocks (g: heap) (rs: seq U64.t) (cap: nat) (idx: nat{idx <= Seq.length rs})
  : Lemma (requires well_formed_heap g /\
                    (forall (i: nat). i < Seq.length rs ==> MBP.root_valid_for_darkening g (Seq.index rs i)))
          (ensures (let gi = fst (MB.darken_roots_bounded_prefix_spec g Seq.empty rs idx cap) in
                    objects zero_addr gi == objects zero_addr g /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                       SPI.same_block g gi (hd_address x) /\ (is_blue x gi <==> is_blue x g))))
          (decreases idx)
  = if idx = 0 then ()
    else begin
      start_prefix_blocks g rs cap (idx - 1);
      let (g0, st0) = MB.darken_roots_bounded_prefix_spec g Seq.empty rs (idx - 1) cap in
      let r = Seq.index rs (idx - 1) in
      if U64.v r >= U64.v zero_addr + U64.v mword && U64.v r < heap_size && U64.v r % U64.v mword = 0
      then begin
        let ro : obj_addr = r in
        MB.darken_roots_bounded_prefix_preserves_resolve g Seq.empty rs (idx - 1) cap ro;
        let t = resolve_object ro g0 in
        hd_address_spec t;
        hd_address_bounds t;
        f_hd_roundtrip t;
        assert (U64.sub t mword == hd_address t);
        if is_white t g0 then begin
          Mark.colors_exclusive t g0;
          MPC.grey_keeps_blocks g0 t
        end
      end
    end
#pop-options

let start_keeps_blocks minor g fp rs =
  GenInv.collection_heap_shape_as_free_stw minor g fp;
  GenInv.collection_shape_with_elim Ph.Idle free_stw minor g fp;
  GenInv.major_shape_with_elim Ph.Idle free_stw g fp;
  start_prefix_blocks g rs (Seq.length rs + 1) (Seq.length rs)

/// A write into the body of `x` keeps every other block, and every header.
let write_keeps_other (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t) (y: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ SPMut.in_body g x a /\
                    Seq.mem y (objects zero_addr g) /\ y <> x)
          (ensures SPI.same_block g (write_word g a v) (hd_address y) /\
                   SPI.same_heads g (write_word g a v) /\
                   read_word (write_word g a v) (hd_address y) == read_word g (hd_address y))
  = MM.write_heads g x a v;
    SPMut.other_body g x y a;
    SPI.obj_pos g y;
    let body (b: hp_addr)
      : Lemma (requires U64.v (hd_address y) < U64.v b /\ U64.v b < W.bnext g (hd_address y))
              (ensures read_word (write_word g a v) b == read_word g b)
      = read_write_different g a b v
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires body)

/// The write half: a write into the body of `x` keeps every other block
/// non-free, with its block and colours.
let write_keeps_in_use (free: free_def) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t) (y: obj_addr)
  : Lemma (requires free_def_ok free /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    SPMut.in_body g x a /\ in_use free g y /\ y <> x)
          (ensures SPI.same_block g (write_word g a v) (hd_address y) /\
                   in_use free (write_word g a v) y /\
                   (is_white y (write_word g a v) <==> is_white y g))
  = free_def_ok_elim free;
    write_keeps_other g x a v y;
    SPI.same_heads_facts g (write_word g a v);
    MM.header_kept_facts g (write_word g a v) y

/// The darkening half, while marking.
let darken_keeps (g: heap) (w: U64.t) (x y: obj_addr) (a: hp_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    SPMut.in_body g x a /\ in_use free_stw g y)
          (ensures (let g1 = MM.darken g w in
                    Seq.mem x (objects zero_addr g1) /\ ~(is_blue x g1) /\ SPMut.in_body g1 x a /\
                    in_use free_stw g1 y /\ SPI.same_block g g1 (hd_address y) /\
                    (~(is_white y g) ==> ~(is_white y g1))))
  = let g1 = MM.darken g w in
    free_stw_ok ();
    free_def_ok_elim free_stw;
    if is_pointer w &&
       Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
       is_white (resolve_object (w <: obj_addr) g) g
    then begin
      let t = resolve_object (w <: obj_addr) g in
      Mark.colors_exclusive t g;
      MPC.grey_keeps_blocks g t;
      makeGray_eq t g;
      color_change_preserves_wosize_any t x g GC.Lib.Header.Gray;
      (if y <> t then MM.header_kept_facts g g1 y
       else begin
         makeGray_is_gray t g;
         Mark.colors_exclusive t g1
       end)
    end

#push-options "--ifuel 1"
let modify_keeps_others ph minor g fp x a v y =
  match ph with
  | Ph.Marking ->
      GI.phase_shape_marking minor g fp;
      GI.phase_free_marking ();
      free_stw_ok ();
      free_def_ok_elim free_stw;
      let g1 = MM.darken g (read_word g a) in
      darken_keeps g (read_word g a) x y a;
      write_keeps_in_use free_stw g1 x a v y
  | Ph.Idle ->
      GI.phase_free_idle ();
      free_stw_ok ();
      free_def_ok_elim free_stw;
      write_keeps_in_use free_stw g x a v y
  | Ph.Sweeping c ->
      GI.phase_free_sweeping c;
      SPI.free_incremental_ok c;
      free_def_ok_elim (SPI.free_incremental c);
      write_keeps_in_use (SPI.free_incremental c) g x a v y
#pop-options
