module GC.Gen.Run.Invariant.Collector

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
module MP = GC.Spec.MarkPhase
module MPC = GC.Spec.MarkPhase.Completeness
module SPC = GC.Spec.SweepPhase.Completeness
module SPI = GC.Spec.SweepPhase.Intrinsic
module LL = GC.Spec.FusedSweep.Lossless
module W = GC.Spec.Walk
module GI = GC.Gen.Incremental
module RT = GC.Gen.RefTable
module GenInv = GC.Gen.HeapInvariant
module GMC = GC.Gen.MarkPhase.Completeness
module GMS = GC.Gen.MarkPhase.Safety
module MC = GC.Gen.MarkPhase.Cycle
module MStart = GC.Gen.MarkPhase.Start
module S = GC.Spec.MarkPhase.Slice

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// Recolouring: the same blocks, with the same bodies
/// ---------------------------------------------------------------------------

/// `g'` has the blocks of `g`, each with its size, tag and body, and blue
/// exactly where `g` is.
let recoloured (g g': heap) : prop =
  objects zero_addr g' == objects zero_addr g /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
     SPI.same_block g g' (hd_address x) /\ (is_blue x g' <==> is_blue x g))

let recoloured_field (g g': heap) (x: obj_addr) (j: nat)
  : Lemma (requires recoloured g g' /\ Seq.mem x (objects zero_addr g) /\
                    j < U64.v (wosize_of_object x g) /\ U64.v x + j * 8 + 8 <= heap_size)
          (ensures read_word g' (U64.uint_to_t (U64.v x + j * 8)) == read_word g (U64.uint_to_t (U64.v x + j * 8)))
  = wosize_of_object_spec x g;
    hd_address_spec x;
    assert (SPI.same_block g g' (hd_address x));
    let a : hp_addr = U64.uint_to_t (U64.v x + j * 8) in
    assert (U64.v (hd_address x) < U64.v a /\ U64.v a < W.bnext g (hd_address x))

let recoloured_block (g g': heap) (x: obj_addr)
  : Lemma (requires recoloured g g' /\ Seq.mem x (objects zero_addr g))
          (ensures wosize_of_object x g' == wosize_of_object x g /\
                   tag_of_object x g' == tag_of_object x g /\
                   scannable g' x == scannable g x /\
                   (forall (j: nat). j < U64.v (wosize_of_object x g) /\ U64.v x + j * 8 + 8 <= heap_size ==>
                      read_word g' (U64.uint_to_t (U64.v x + j * 8)) == read_word g (U64.uint_to_t (U64.v x + j * 8))))
  = wosize_of_object_spec x g; wosize_of_object_spec x g';
    tag_of_object_spec x g; tag_of_object_spec x g';
    is_no_scan_spec x g; is_no_scan_spec x g';
    assert (SPI.same_block g g' (hd_address x));
    introduce forall (j: nat). j < U64.v (wosize_of_object x g) /\ U64.v x + j * 8 + 8 <= heap_size ==>
                        read_word g' (U64.uint_to_t (U64.v x + j * 8)) == read_word g (U64.uint_to_t (U64.v x + j * 8))
    with introduce _ ==> _ with recoloured_field g g' x j

let recoloured_blocks (g g': heap)
  : Lemma (requires recoloured g g')
          (ensures forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                     wosize_of_object x g' == wosize_of_object x g /\
                     tag_of_object x g' == tag_of_object x g /\
                     scannable g' x == scannable g x /\
                     (forall (j: nat). j < U64.v (wosize_of_object x g) /\ U64.v x + j * 8 + 8 <= heap_size ==>
                        read_word g' (U64.uint_to_t (U64.v x + j * 8)) == read_word g (U64.uint_to_t (U64.v x + j * 8))))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (recoloured_block g g'))

/// The remembered set, stop-the-world, survives a recolouring.
#push-options "--z3rlimit 20"
let recoloured_ref_table (g g': heap) (sl: seq U64.t) (n: nat)
  : Lemma (requires recoloured g g' /\
                    RT.ref_table_covers_with free_stw g sl n /\ RT.ref_table_sound_with free_stw g sl n)
          (ensures RT.ref_table_covers_with free_stw g' sl n /\ RT.ref_table_sound_with free_stw g' sl n)
  = recoloured_blocks g g'
#pop-options

/// The walk of a recoloured dense heap ends where it did.
let recoloured_walk_end (g g': heap)
  : Lemma (requires recoloured g g' /\
                    heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                    heap_objects_dense g')
          (ensures W.walk_end g' zero_addr == W.walk_end g zero_addr)
  = recoloured_blocks g g';
    SPC.walk_end_same_blocks g g'

/// ---------------------------------------------------------------------------
/// The start of a cycle
/// ---------------------------------------------------------------------------

/// The shape the idle state gives, taken apart.
let idle_parts (m: minor_state) (g: heap) (fp: U64.t) (sp: MP.scan_pos)
  : Lemma (requires GI.phase_shape m g fp Ph.Idle sp)
          (ensures GenInv.collection_heap_shape m g fp /\ heap_objects_dense g /\
                   Seq.length (objects zero_addr g) > 0)
  = GI.phase_shape_idle m g fp sp;
    GenInv.collection_heap_shape_elim m g fp;
    GenInv.major_heap_shape_elim g fp

let marking_dense (m: minor_state) (g: heap) (fp: U64.t) (sp: MP.scan_pos)
  : Lemma (requires GI.phase_shape m g fp Ph.Marking sp)
          (ensures heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0)
  = GI.phase_shape_marking m g fp sp;
    GenInv.collection_shape_with_elim Ph.Marking free_stw m g fp;
    GenInv.major_shape_with_elim Ph.Marking free_stw g fp

/// The empty nursery points nowhere.
let reset_points_nowhere (free: free_def) (m: minor_state) (g: heap)
  : Lemma (requires m == minor_reset m) (ensures GenInv.minor_major_fields_not_free free m g)
  = let h (obj: U64.t) (j: nat)
      : Lemma (requires Seq.mem obj (minor_objects m) /\ j < minor_scan_wosize m obj /\
                        is_pointer_field (minor_read_field m obj j))
              (ensures in_use free g ((minor_read_field m obj j) <: obj_addr))
      = minor_reset_objects_not_mem m obj
    in
    GenInv.minor_major_fields_not_free_intro free m g h

/// The phase shape after the start.
#push-options "--z3rlimit 20"
let start_shape (r: real_state) (roots: seq U64.t) (r': real_state)
  : Lemma (requires phase_shape r /\ start_step r roots r')
          (ensures phase_shape r' /\ recoloured r.memory.major r'.memory.major)
  = let m = r.memory.nursery in
    let g = r.memory.major in
    let gd = r'.memory.major in
    idle_parts m g r.free_list r.scan_pos;
    MStart.mark_start_shape m g r.free_list roots;
    GMS.start_keeps_blocks m g r.free_list roots;
    assert (recoloured g gd);
    marking_dense m gd r.free_list MP.scan_none;
    recoloured_walk_end g gd;
    minor_reset_objects_empty m;
    GI.phase_free_idle ();
    GI.phase_free_marking ();
    recoloured_ref_table g gd r.ref_table (Seq.length r.ref_table)
#pop-options

/// The accounting after the start.
#push-options "--z3rlimit 40"
let start_accounting (r: real_state) (h: cycle_history) (roots: seq U64.t) (r': real_state)
  : Lemma (requires run_invariant r h /\ start_step r roots r' /\ recoloured r.memory.major r'.memory.major)
          (ensures snapshot_accounting r' (update_history h r (StartCycle roots) r'))
  = let m = r.memory.nursery in
    let g = r.memory.major in
    let gd = r'.memory.major in
    let h' = update_history h r (StartCycle roots) r' in
    assert (h'.start_memory == r.memory /\ h'.start_roots == roots /\
            h'.allocated_during_cycle == SPC.nothing_new);
    idle_parts m g r.free_list r.scan_pos;
    MC.start_inv m g r.free_list roots;
    recoloured_blocks g gd;
    // B1
    MPC.within_snapshot_ext (MC.snapshot g roots SPC.nothing_new) (kept h') gd;
    reset_points_nowhere (MPC.outside_snapshot (kept h')) r'.memory.nursery gd;
    // the remembered set is empty (the nursery is), the walk
    minor_reset_objects_empty m;
    MStart.mark_start_shape m g r.free_list roots;
    marking_dense m gd r.free_list MP.scan_none;
    recoloured_walk_end g gd;
    // B5
    let b5 (p: nat)
      : Lemma (requires LL.blue_covered gd p \/ SPC.new_covered h'.allocated_during_cycle gd p)
              (ensures reclaimable_at_start h' p)
      = eliminate exists (x: obj_addr). Seq.mem x (objects zero_addr gd) /\ is_blue x gd /\ LL.in_extent gd x p
        with assert (free_at_start h' x /\ LL.in_extent g x p)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires b5)
#pop-options

let start_keeps r h roots r' =
  start_shape r roots r';
  start_accounting r h roots r'

/// ---------------------------------------------------------------------------
/// Slices
/// ---------------------------------------------------------------------------

let slice_keeps_idle r h budget r' = ()

/// The nursery's pointers into the major heap stay in kept blocks when the
/// major heap only darkens.
let darker_nursery (k: obj_addr -> prop) (m: minor_state) (g g': heap)
  : Lemma (requires S.darker g g' /\ GenInv.minor_major_fields_not_free (MPC.outside_snapshot k) m g)
          (ensures GenInv.minor_major_fields_not_free (MPC.outside_snapshot k) m g')
  = let f (obj: U64.t) (j: nat)
      : Lemma (requires Seq.mem obj (minor_objects m) /\ j < minor_scan_wosize m obj /\
                        is_pointer_field (minor_read_field m obj j))
              (ensures in_use (MPC.outside_snapshot k) g' ((minor_read_field m obj j) <: obj_addr))
      = let y : obj_addr = minor_read_field m obj j in
        GenInv.minor_major_fields_not_free_elim (MPC.outside_snapshot k) m g obj j;
        MPC.in_use_outside_snapshot k g y;
        MPC.in_use_outside_snapshot k g' y
    in
    GenInv.minor_major_fields_not_free_intro (MPC.outside_snapshot k) m g' f

#push-options "--z3rlimit 40"
let slice_keeps_marking r h budget r' =
  let m = r.memory.nursery in
  let g = r.memory.major in
  let g' = r'.memory.major in
  let sp = r.scan_pos in
  let sp' = r'.scan_pos in
  let s = snapshot h in
  GI.phase_shape_marking m g r.free_list sp;
  assert (MP.marking_inv g s sp);
  GI.mark_slice_shape m g sp r.free_list budget g' sp' r'.free_list Ph.Marking;
  S.mark_steps_inv g g' sp sp' s;
  MPC.mark_steps_keep_blocks g g' sp sp';
  S.mark_steps_darker g g' sp sp';
  assert (recoloured g g');
  marking_dense m g r.free_list sp;
  marking_dense m g' r'.free_list sp';
  recoloured_walk_end g g';
  recoloured_blocks g g';
  GI.phase_free_marking ();
  recoloured_ref_table g g' r.ref_table (Seq.length r.ref_table);
  MPC.account_steps (kept h) g g' sp sp';
  darker_nursery (kept h) m g g';
  let b5 (p: nat)
    : Lemma (requires LL.blue_covered g' p \/ SPC.new_covered h.allocated_during_cycle g' p)
            (ensures LL.blue_covered g p \/ SPC.new_covered h.allocated_during_cycle g p)
    = ()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires b5)
#pop-options

/// ---------------------------------------------------------------------------
/// At idle
/// ---------------------------------------------------------------------------

let idle_survives r h = ()
