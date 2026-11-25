module GC.Gen.Run.Invariant.SweepSlice

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
module SPC = GC.Spec.SweepPhase.Completeness
module SPI = GC.Spec.SweepPhase.Intrinsic
module SL = GC.Spec.SweepPhase.Slice
module Step = GC.Spec.FusedSweep.Step
module LL = GC.Spec.FusedSweep.Lossless
module W = GC.Spec.Walk
module GI = GC.Gen.Incremental
module RT = GC.Gen.RefTable
module GenInv = GC.Gen.HeapInvariant
module GMC = GC.Gen.MarkPhase.Completeness

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// What a slice of the sweep does
/// ---------------------------------------------------------------------------

let front_same (g g': heap) (c': U64.t) : prop =
  forall (a: hp_addr). U64.v a >= U64.v c' ==> read_word g' a == read_word g a

/// The slice from `g` at cursor `c` to `g'` at cursor `c'`.
let slice_rel (g g': heap) (fp fp': U64.t) (c c': U64.t) : prop =
  SPI.sweep_inv_incremental g fp c /\ SPI.sweep_inv_incremental g' fp' c' /\
  U64.v c % 8 == 0 /\ U64.v c' % 8 == 0 /\ U64.v c' >= U64.v c /\
  (forall (x: obj_addr). in_use (SPI.free_incremental c') g' x == in_use (SPI.free_incremental c) g x) /\
  (forall (x: obj_addr). in_use (SPI.free_incremental c) g x ==> SPI.same_block g g' (hd_address x)) /\
  (forall (x: obj_addr). SPI.pending_free c' g' x ==> SPI.pending_free c g x) /\
  W.walk_end g' zero_addr == W.walk_end g zero_addr /\
  front_same g g' c'

let slice_facts (g: heap) (fp: U64.t) (c: U64.t) (budget: nat)
  : Lemma (requires SPI.sweep_inv_incremental g fp c)
          (ensures (let (g', fp', st') = SL.sweep_slice g fp (SPI.state_at g c) budget in
                    slice_rel g g' fp fp' c st'.GC.Spec.FusedSweep.cursor))
  = SL.sweep_slice_phase g fp c budget;
    let st = SPI.state_at g c in
    SL.slice_is_steps g fp st c budget;
    let k = SL.slice_count g fp st c budget in
    Step.sweep_steps_walk_end g fp c k;
    Step.sweep_steps_front g fp c k;
    let (g', fp', st') = SL.sweep_slice g fp st budget in
    SPI.sweep_inv_incremental_elim g fp c;
    SPI.sweep_inv_incremental_elim g' fp' st'.GC.Spec.FusedSweep.cursor

/// A block keeping its block keeps its size.
let same_block_size (g g': heap) (x: obj_addr)
  : Lemma (requires SPI.same_block g g' (hd_address x))
          (ensures wosize_of_object x g' == wosize_of_object x g)
  = SPI.colour_of g x; SPI.colour_of g' x

/// A block whose header lies past the new cursor keeps its size.
let front_size (g g': heap) (c': U64.t) (x: obj_addr)
  : Lemma (requires front_same g g' c' /\ U64.v x > U64.v c' /\ U64.v c' % 8 == 0)
          (ensures wosize_of_object x g' == wosize_of_object x g)
  = hd_address_spec x;
    wosize_of_object_spec x g; wosize_of_object_spec x g'

/// With the sweep done, nothing is pending free.
let done_nothing_pending (g: heap) (c: U64.t) (x: obj_addr)
  : Lemma (requires SPI.sweep_done c)
          (ensures in_use (SPI.free_incremental c) g x == in_use free_stw g x)
  = ()

/// A block dark after the slice, and not free before, was black before.
#push-options "--z3rlimit 20"
let dark_was_black (g g': heap) (fp fp': U64.t) (c c': U64.t) (x: obj_addr)
  : Lemma (requires slice_rel g g' fp fp' c c' /\ in_use (SPI.free_incremental c) g x /\
                    Seq.mem x (objects zero_addr g') /\ ~(is_white x g') /\ ~(is_blue x g'))
          (ensures is_black x g)
  = SPI.sweep_inv_incremental_elim g fp c;
    SPI.sweep_inv_incremental_elim g' fp' c';
    SPI.obj_pos g x; SPI.obj_pos g' x;
    SPI.colour_of g x; SPI.colour_of g' x;
    Mark.color_exhaustive x g; Mark.colors_exclusive x g;
    Mark.color_exhaustive x g'; Mark.colors_exclusive x g';
    let q = hd_address x in
    if U64.v q < U64.v c then begin
      SPI.behind_swept_elim g (U64.v c) q;
      SPI.behind_swept_elim g' (U64.v c') q
    end
    else SPI.front_unswept_elim g (U64.v c) q
#pop-options

/// ---------------------------------------------------------------------------
/// The proof
/// ---------------------------------------------------------------------------

/// The context: a run-invariant state mid-sweep and the slice.
let ctx (r: real_state) (h: cycle_history) (r': real_state) (c c': U64.t) : prop =
  run_invariant r h /\ r.phase == Ph.Sweeping c /\
  slice_rel r.memory.major r'.memory.major r.free_list r'.free_list c c' /\
  r'.memory.nursery == r.memory.nursery /\ r'.ref_table == r.ref_table /\
  r'.phase == (if SPI.sweep_done c' then Ph.Idle else Ph.Sweeping c')

/// Kept blocks are in use before (and so after, with their blocks).
let kept_in_use (r: real_state) (h: cycle_history) (r': real_state) (c c': U64.t) (x: obj_addr)
  : Lemma (requires ctx r h r' c c' /\ kept h x)
          (ensures in_use (SPI.free_incremental c) r.memory.major x /\
                   in_use (SPI.free_incremental c') r'.memory.major x /\
                   wosize_of_object x r'.memory.major == wosize_of_object x r.memory.major)
  = let g = r.memory.major in
    Mark.colors_exclusive x g;
    same_block_size g r'.memory.major x

/// Blocks not free for the snapshot: the same before and after.
#push-options "--z3rlimit 30"
let outside_same (r: real_state) (h: cycle_history) (r': real_state) (c c': U64.t) (x: obj_addr)
  : Lemma (requires ctx r h r' c c')
          (ensures (in_use (MPC.outside_snapshot (kept h)) r'.memory.major x ==
                    in_use (MPC.outside_snapshot (kept h)) r.memory.major x) /\
                   (in_use (MPC.outside_snapshot (kept h)) r.memory.major x ==>
                      in_use (SPI.free_incremental c) r.memory.major x))
  = let g = r.memory.major in
    let g' = r'.memory.major in
    let k = kept h in
    MPC.in_use_outside_snapshot k g x;
    MPC.in_use_outside_snapshot k g' x;
    Mark.colors_exclusive x g; Mark.colors_exclusive x g';
    Mark.color_exhaustive x g; Mark.color_exhaustive x g';
    if in_use (SPI.free_incremental c) g x && Seq.mem x (objects zero_addr g') &&
       not (is_white x g') && not (is_blue x g')
    then dark_was_black g g' r.free_list r'.free_list c c' x
#pop-options

let phase_free_after (r': real_state) (c': U64.t) (x: obj_addr)
  : Lemma (requires r'.phase == (if SPI.sweep_done c' then Ph.Idle else Ph.Sweeping c'))
          (ensures in_use (GI.phase_free r'.phase) r'.memory.major x ==
                   in_use (SPI.free_incremental c') r'.memory.major x)
  = if SPI.sweep_done c' then GI.phase_free_idle () else GI.phase_free_sweeping c'

/// ---------------------------------------------------------------------------
/// The remembered set
/// ---------------------------------------------------------------------------

let same_block_field (g g': heap) (x: obj_addr) (j: nat)
  : Lemma (requires SPI.same_block g g' (hd_address x) /\
                    j < U64.v (wosize_of_object x g) /\ U64.v x + j * 8 + 8 <= heap_size)
          (ensures read_word g' (U64.uint_to_t (U64.v x + j * 8)) == read_word g (U64.uint_to_t (U64.v x + j * 8)))
  = wosize_of_object_spec x g;
    hd_address_spec x;
    let a : hp_addr = U64.uint_to_t (U64.v x + j * 8) in
    assert (U64.v (hd_address x) < U64.v a /\ U64.v a < W.bnext g (hd_address x))

let same_block_facts (g g': heap) (x: obj_addr)
  : Lemma (requires SPI.same_block g g' (hd_address x))
          (ensures wosize_of_object x g' == wosize_of_object x g /\
                   scannable g' x == scannable g x /\
                   (forall (j: nat). j < U64.v (wosize_of_object x g) /\ U64.v x + j * 8 + 8 <= heap_size ==>
                      read_word g' (U64.uint_to_t (U64.v x + j * 8)) == read_word g (U64.uint_to_t (U64.v x + j * 8))))
  = wosize_of_object_spec x g; wosize_of_object_spec x g';
    tag_of_object_spec x g; tag_of_object_spec x g';
    is_no_scan_spec x g; is_no_scan_spec x g';
    hd_address_spec x;
    introduce forall (j: nat). j < U64.v (wosize_of_object x g) /\ U64.v x + j * 8 + 8 <= heap_size ==>
                        read_word g' (U64.uint_to_t (U64.v x + j * 8)) == read_word g (U64.uint_to_t (U64.v x + j * 8))
    with introduce _ ==> _ with same_block_field g g' x j

/// The remembered set moves to a heap with the same blocks in use, each
/// with its block.
#push-options "--z3rlimit 20"
let rt_transfer (free free': free_def) (g g': heap) (sl: seq U64.t)
  : Lemma (requires (forall (x: obj_addr). in_use free' g' x == in_use free g x) /\
                    (forall (x: obj_addr). in_use free g x ==> SPI.same_block g g' (hd_address x)) /\
                    RT.ref_table_covers_with free g sl (Seq.length sl) /\
                    RT.ref_table_sound_with free g sl (Seq.length sl))
          (ensures RT.ref_table_covers_with free' g' sl (Seq.length sl) /\
                   RT.ref_table_sound_with free' g' sl (Seq.length sl))
  = let f (x: obj_addr)
      : Lemma (requires in_use free g x)
              (ensures wosize_of_object x g' == wosize_of_object x g /\
                       scannable g' x == scannable g x /\
                       (forall (j: nat). j < U64.v (wosize_of_object x g) /\ U64.v x + j * 8 + 8 <= heap_size ==>
                          read_word g' (U64.uint_to_t (U64.v x + j * 8)) == read_word g (U64.uint_to_t (U64.v x + j * 8))))
      = same_block_facts g g' x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires f)
#pop-options

/// ---------------------------------------------------------------------------
/// The shape
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let shape_after (r: real_state) (h: cycle_history) (r': real_state) (c c': U64.t)
  : Lemma (requires ctx r h r' c c' /\
                    GI.phase_shape r'.memory.nursery r'.memory.major r'.free_list r'.phase r'.scan_pos)
          (ensures phase_shape r')
  = let g = r.memory.major in
    let g' = r'.memory.major in
    GI.phase_free_sweeping c;
    let eq (x: obj_addr)
      : Lemma (in_use (GI.phase_free r'.phase) g' x == in_use (GI.phase_free r.phase) g x)
      = phase_free_after r' c' x
    in
    FStar.Classical.forall_intro eq;
    rt_transfer (GI.phase_free r.phase) (GI.phase_free r'.phase) g g' r.ref_table
#pop-options

/// No infix block after (from the collector's state).
let no_infix_after (r': real_state)
  : Lemma (requires GI.phase_shape r'.memory.nursery r'.memory.major r'.free_list r'.phase r'.scan_pos)
          (ensures no_infix_block r'.memory.major)
  = let ph = r'.phase in
    GI.phase_shape_collection r'.memory.nursery r'.memory.major r'.free_list ph r'.scan_pos;
    GenInv.collection_shape_with_elim ph (GI.phase_free ph) r'.memory.nursery r'.memory.major r'.free_list;
    GenInv.major_shape_with_elim ph (GI.phase_free ph) r'.memory.major r'.free_list

/// ---------------------------------------------------------------------------
/// B1
/// ---------------------------------------------------------------------------

let dark_after (r: real_state) (h: cycle_history) (r': real_state) (c c': U64.t) (x: obj_addr)
  : Lemma (requires ctx r h r' c c' /\ Seq.mem x (objects zero_addr r'.memory.major) /\
                    (is_gray x r'.memory.major \/ is_black x r'.memory.major))
          (ensures kept h x)
  = let g = r.memory.major in
    let g' = r'.memory.major in
    Mark.colors_exclusive x g';
    assert (in_use (SPI.free_incremental c') g' x);
    dark_was_black g g' r.free_list r'.free_list c c' x

#push-options "--z3rlimit 30"
let b1_after (r: real_state) (h: cycle_history) (r': real_state) (c c': U64.t)
  : Lemma (requires ctx r h r' c c' /\
                    GI.phase_shape r'.memory.nursery r'.memory.major r'.free_list r'.phase r'.scan_pos)
          (ensures MPC.within_snapshot (kept h) r'.memory.major /\
                   GenInv.minor_major_fields_not_free (MPC.outside_snapshot (kept h)) r'.memory.nursery r'.memory.major /\
                   (forall (i: nat). i < Seq.length r'.ref_table ==>
                      (exists (x: obj_addr) (j: nat). kept h x /\ j < U64.v (wosize_of_object x r'.memory.major) /\
                         U64.v (Seq.index r'.ref_table i) == U64.v x + j * 8)))
  = let g = r.memory.major in
    let g' = r'.memory.major in
    let k = kept h in
    let m = r.memory.nursery in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (dark_after r h r' c c'));
    FStar.Classical.forall_intro (outside_same r h r' c c');
    no_infix_after r';
    MPC.outside_snapshot_ok k;
    SPI.wf_transport g g' (MPC.outside_snapshot k) (MPC.outside_snapshot k);
    wf_with_parts ();
    GenInv.minor_major_fields_not_free_transfer_blocks (MPC.outside_snapshot k) (MPC.outside_snapshot k) m g g';
    FStar.Classical.forall_intro (FStar.Classical.move_requires (kept_in_use r h r' c c'))
#pop-options

/// ---------------------------------------------------------------------------
/// B2-B4
/// ---------------------------------------------------------------------------

/// A block allocated after was allocated before, with its size.
let alloc_back (r: real_state) (h: cycle_history) (r': real_state) (c c': U64.t) (x: obj_addr)
  : Lemma (requires ctx r h r' c c' /\ is_allocated r'.memory (Major x))
          (ensures is_allocated r.memory (Major x) /\
                   wosize_of_object x r'.memory.major == wosize_of_object x r.memory.major)
  = let g = r.memory.major in
    let g' = r'.memory.major in
    if in_use (SPI.free_incremental c') g' x then same_block_size g g' x
    else begin
      assert (SPI.pending_free c g x);
      Mark.colors_exclusive x g;
      front_size g g' c' x
    end

#push-options "--z3rlimit 30"
let b2_b4_after (r: real_state) (h: cycle_history) (r': real_state) (c c': U64.t)
  : Lemma (requires ctx r h r' c c')
          (ensures (let g = r'.memory.major in
                    let g0 = h.start_memory.major in
                    (forall (x: obj_addr). snapshot h x ==>
                       Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ wosize_of_object x g == wosize_of_object x g0) /\
                    (forall (x: obj_addr). garbage_at_start h x /\ is_allocated r'.memory (Major x) /\ ~(h.allocated_during_cycle x) ==>
                       wosize_of_object x g == wosize_of_object x g0) /\
                    W.walk_end g zero_addr == W.walk_end g0 zero_addr /\
                    (forall (x: obj_addr). h.allocated_during_cycle x ==> is_allocated r'.memory (Major x) /\ ~(snapshot h x)) /\
                    (forall (x: obj_addr). is_allocated r'.memory (Major x) ==>
                       snapshot h x \/ h.allocated_during_cycle x \/ garbage_at_start h x)))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (kept_in_use r h r' c c'));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (alloc_back r h r' c c'))
#pop-options

/// ---------------------------------------------------------------------------
/// B5
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30"
let b5_word (r: real_state) (h: cycle_history) (r': real_state) (c c': U64.t) (y: obj_addr) (p: nat)
  : Lemma (requires ctx r h r' c c' /\ Seq.mem y (objects zero_addr r'.memory.major) /\
                    (is_blue y r'.memory.major \/ h.allocated_during_cycle y) /\
                    LL.in_extent r'.memory.major y p)
          (ensures reclaimable_at_start h p)
  = let g = r.memory.major in
    let g' = r'.memory.major in
    let g0 = h.start_memory.major in
    if FStar.IndefiniteDescription.strong_excluded_middle (h.allocated_during_cycle y) then begin
      kept_in_use r h r' c c' y;
      assert (LL.in_extent g y p);
      assert (SPC.new_covered h.allocated_during_cycle g p)
    end else begin
      SPC.extent_below_end g' y p;
      let z = SPC.block_over g p in
      if is_blue z g then assert (LL.blue_covered g p)
      else if FStar.IndefiniteDescription.strong_excluded_middle (h.allocated_during_cycle z) then
        assert (SPC.new_covered h.allocated_during_cycle g p)
      else if FStar.IndefiniteDescription.strong_excluded_middle (snapshot h z) then begin
        kept_in_use r h r' c c' z;
        assert (LL.in_extent g' z p);
        Mark.colors_exclusive y g';
        SPC.extents_disjoint g' z y p
      end else begin
        assert (garbage_at_start h z);
        assert (wosize_of_object z g == wosize_of_object z g0);
        assert (LL.in_extent g0 z p)
      end
    end
#pop-options

let b5_after (r: real_state) (h: cycle_history) (r': real_state) (c c': U64.t)
  : Lemma (requires ctx r h r' c c')
          (ensures forall (p: nat). LL.blue_covered r'.memory.major p \/
                               SPC.new_covered h.allocated_during_cycle r'.memory.major p ==>
                               reclaimable_at_start h p)
  = let g' = r'.memory.major in
    let one (p: nat)
      : Lemma (requires LL.blue_covered g' p \/ SPC.new_covered h.allocated_during_cycle g' p)
              (ensures reclaimable_at_start h p)
      = if FStar.IndefiniteDescription.strong_excluded_middle (LL.blue_covered g' p) then
          eliminate exists (y: obj_addr). Seq.mem y (objects zero_addr g') /\ is_blue y g' /\ LL.in_extent g' y p
          with b5_word r h r' c c' y p
        else
          eliminate exists (y: obj_addr). Seq.mem y (objects zero_addr g') /\ h.allocated_during_cycle y /\ LL.in_extent g' y p
          with b5_word r h r' c c' y p
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// ---------------------------------------------------------------------------
/// The phase's clause, and the slice
/// ---------------------------------------------------------------------------

/// A kept block past the new cursor is black.
#push-options "--z3rlimit 20"
let kept_black_after (r: real_state) (h: cycle_history) (r': real_state) (c c': U64.t) (x: obj_addr)
  : Lemma (requires ctx r h r' c c' /\ kept h x /\ U64.v x > U64.v c')
          (ensures is_black x r'.memory.major)
  = let g' = r'.memory.major in
    kept_in_use r h r' c c' x;
    SPI.sweep_inv_incremental_elim g' r'.free_list c';
    SPI.obj_pos g' x; SPI.colour_of g' x;
    hd_address_spec x;
    SPI.front_unswept_elim g' (U64.v c') (hd_address x);
    Mark.colors_exclusive x g'
#pop-options

#push-options "--z3rlimit 40"
let slice_keeps_sweeping r h budget r' =
  let c = Ph.Sweeping?._0 r.phase in
  let m = r.memory.nursery in
  let g = r.memory.major in
  let fp = r.free_list in
  let sp = r.scan_pos in
  GI.phase_shape_sweeping m g fp c sp;
  slice_facts g fp c budget;
  let (g1, fp1, st1) = SL.sweep_slice g fp (SPI.state_at g c) budget in
  let c' = st1.GC.Spec.FusedSweep.cursor in
  assert (r'.memory.major == g1 /\ r'.free_list == fp1 /\ r'.scan_pos == sp /\
          r'.phase == (if SPI.sweep_done c' then Ph.Idle else Ph.Sweeping c'));
  GI.phase_slice_shape m g fp r.phase budget sp;
  assert (ctx r h r' c c');
  shape_after r h r' c c';
  b1_after r h r' c c';
  b2_b4_after r h r' c c';
  b5_after r h r' c c';
  GMC.cycle_slice (kept h) m g sp fp r.phase budget r'.memory.major r'.scan_pos r'.free_list r'.phase;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (kept_black_after r h r' c c'))
#pop-options
