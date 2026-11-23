/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Invariant.Write - the program's writes keep the run invariant
/// ---------------------------------------------------------------------------
///
/// A write into the major heap (the barrier into a scannable block, a raw
/// store into a no-scan one) or into the nursery keeps `run_invariant`
/// (`GC.Gen.Run.Invariant.Defs`), and so does a nursery allocation.  For the
/// nursery, the frames (`nursery_store_frame`, `nursery_alloc_frame`, with the
/// trusted nursery shape) are what `nursery_write_step` / `nursery_alloc_step`
/// state.  A value stored into the nursery may be an interior pointer into a
/// major closure: the cross-generation condition is stated on what it names.

module GC.Gen.Run.Invariant.Write

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module MPC = GC.Spec.MarkPhase.Completeness
module SPC = GC.Spec.SweepPhase.Completeness
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module SPU = GC.Spec.SweepPhase.Util
module LL = GC.Spec.FusedSweep.Lossless
module W = GC.Spec.Walk
module GI = GC.Gen.Incremental
module GB = GC.Gen.Barrier
module GBase = GC.Gen.Base
module RT = GC.Gen.RefTable
module Promote = GC.Gen.Promote
module GenInv = GC.Gen.HeapInvariant
module GMM = GC.Gen.MarkPhase.Minor
module Mark = GC.Spec.Mark
module FLA = GC.Spec.FreeList.Ascending
module PCS = GC.Gen.PostCollectionShape
module SweepInv = GC.Spec.SweepInv
module Header = GC.Lib.Header
module PD = GC.Gen.Run.Invariant.Defs
module D = GC.Gen.Run.Invariant.Defs
module I = GC.Model.Ideal

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The missing hypotheses
/// ---------------------------------------------------------------------------


/// ---------------------------------------------------------------------------
/// The collector's state, taken apart
/// ---------------------------------------------------------------------------

let walk_ok (g: heap) (fp: U64.t) : prop =
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\ FLA.fl_ascending g fp

#push-options "--z3rlimit 20"
let shape_facts (ph: Ph.gc_phase) (minor: minor_state) (g: heap) (fp: U64.t) (sp: MP.scan_pos)
  : Lemma (requires GI.phase_shape minor g fp ph sp)
          (ensures free_def_ok (GI.phase_free ph) /\ well_formed_heap_with (GI.phase_free ph) g /\
                   walk_ok g fp /\ GenInv.minor_heap_shape minor /\
                   GenInv.minor_major_fields_not_free (GI.phase_free ph) minor g /\
                   (~(Ph.Sweeping? ph) ==> well_formed_heap g) /\ no_infix_block g /\ blocks_fit g)
  = match ph with
    | Ph.Idle ->
        GI.phase_shape_idle minor g fp sp;
        GI.phase_free_idle ();
        free_stw_ok ();
        GenInv.collection_heap_shape_elim minor g fp;
        GenInv.major_heap_shape_elim g fp;
        GenInv.major_heap_shape_walk g fp;
        wf_parts ();
        GenInv.minor_major_fields_not_free_stw minor g
    | Ph.Marking ->
        GI.phase_shape_marking minor g fp sp;
        GI.phase_free_marking ();
        GenInv.collection_shape_with_elim Ph.Marking free_stw minor g fp;
        GenInv.major_shape_with_elim Ph.Marking free_stw g fp;
        wf_parts ()
    | Ph.Sweeping c ->
        GI.phase_shape_sweeping minor g fp c sp;
        GI.phase_free_sweeping c;
        SPI.free_incremental_ok c;
        SPI.sweep_inv_incremental_iff g fp c;
        SPI.sweep_shape_elim g fp c;
        wf_with_parts ()
#pop-options

/// Every phase's shape has the walk reach the end of the heap.
let shape_walk_end (ph: Ph.gc_phase) (minor: minor_state) (g: heap) (fp: U64.t) (sp: MP.scan_pos)
  : Lemma (requires GI.phase_shape minor g fp ph sp)
          (ensures W.walk_end g zero_addr + 8 >= heap_size)
  = shape_facts ph minor g fp sp;
    W.reaches_end_of_dense g

/// ---------------------------------------------------------------------------
/// The accounting across a change that keeps every block
/// ---------------------------------------------------------------------------

/// `g'` has the blocks of `g`, free exactly when they were, at their sizes.
let blocks_same (g g': heap) : prop =
  objects zero_addr g' == objects zero_addr g /\
  (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==>
     (is_blue y g' <==> is_blue y g) /\ wosize_of_object y g' == wosize_of_object y g)

/// The accounting's base clauses but B1's heap clause.
let base_ok (h: cycle_history) (m: real_memory) : prop =
  let g = m.major in
  let g0 = h.start_memory.major in
  GenInv.minor_major_fields_not_free (MPC.outside_snapshot (kept h)) m.nursery g /\
  (forall (x: obj_addr). snapshot h x ==>
     Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ wosize_of_object x g == wosize_of_object x g0) /\
  (forall (x: obj_addr). h.allocated_during_cycle x ==> is_allocated m (Major x) /\ ~(snapshot h x)) /\
  (forall (x: obj_addr). is_allocated m (Major x) ==>
     snapshot h x \/ h.allocated_during_cycle x \/ garbage_at_start h x) /\
  (forall (p: nat). LL.blue_covered g p \/ SPC.new_covered h.allocated_during_cycle g p ==>
     reclaimable_at_start h p)

/// Under the accounting, a block not free outside the snapshot is a kept,
/// allocated block.
let in_use_outside_kept (s: obj_addr -> prop) (g: heap) (y: obj_addr)
  : Lemma (requires MPC.within_snapshot s g)
          (ensures in_use (MPC.outside_snapshot s) g y <==>
                   (Seq.mem y (objects zero_addr g) /\ ~(is_blue y g) /\ s y))
  = MPC.in_use_outside_snapshot s g y;
    Mark.color_exhaustive y g;
    Mark.colors_exclusive y g

let in_extent_same (g g': heap) (y: obj_addr) (p: nat)
  : Lemma (requires wosize_of_object y g' == wosize_of_object y g)
          (ensures LL.in_extent g' y p <==> LL.in_extent g y p)
  = ()

/// The nursery's names stay in kept blocks across darkening, which only
/// greys a white block.
#push-options "--z3rlimit 20"
let darken_mmf (k: obj_addr -> prop) (ms: minor_state) (g: heap) (w: U64.t)
  : Lemma (requires GenInv.minor_major_fields_not_free (MPC.outside_snapshot k) ms g)
          (ensures GenInv.minor_major_fields_not_free (MPC.outside_snapshot k) ms (MM.darken g w))
  = if is_pointer w &&
       Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
       is_white (resolve_object (w <: obj_addr) g) g
    then begin
      let t = resolve_object (w <: obj_addr) g in
      let g1 = makeGray t g in
      makeGray_eq t g;
      Mark.colors_exclusive t g;
      MPC.grey_keeps_blocks g t;
      makeGray_is_gray t g;
      Mark.colors_exclusive t g1;
      let iu (y: obj_addr)
        : Lemma (requires in_use (MPC.outside_snapshot k) g y)
                (ensures in_use (MPC.outside_snapshot k) g1 y)
        = MPC.in_use_outside_snapshot k g y;
          MPC.in_use_outside_snapshot k g1 y;
          if y <> t then MM.header_kept_facts g g1 y
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires iu);
      GenInv.minor_major_fields_not_free_recolour (MPC.outside_snapshot k) ms t g Header.Gray
    end
#pop-options

/// ... and across a write into the body of a block that is not blue and not
/// a closure.
let write_mmf (k: obj_addr -> prop) (ms: minor_state) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires GenInv.minor_major_fields_not_free (MPC.outside_snapshot k) ms g /\ no_infix_block g /\
                    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ ~(is_closure x g) /\ SPM.in_body g x a)
          (ensures GenInv.minor_major_fields_not_free (MPC.outside_snapshot k) ms (write_word g a v))
  = MPC.outside_snapshot_ok k;
    GMM.write_keeps_nursery (MPC.outside_snapshot k) ms g x a v

/// ... and across the barrier while marking: darken the old value, then
/// write.
#push-options "--z3rlimit 20"
let barrier_mmf (k: obj_addr -> prop) (ms: minor_state) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires GenInv.minor_major_fields_not_free (MPC.outside_snapshot k) ms g /\ no_infix_block g /\
                    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ ~(is_closure x g) /\ SPM.in_body g x a)
          (ensures GenInv.minor_major_fields_not_free (MPC.outside_snapshot k) ms
                     (write_word (MM.darken g (read_word g a)) a v))
  = let w = read_word g a in
    let g1 = MM.darken g w in
    darken_mmf k ms g w;
    if is_pointer w &&
       Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
       is_white (resolve_object (w <: obj_addr) g) g
    then begin
      let t = resolve_object (w <: obj_addr) g in
      makeGray_eq t g;
      Mark.colors_exclusive t g;
      MPC.grey_keeps_blocks g t;
      color_change_preserves_is_closure t x g Header.Gray;
      color_change_preserves_wosize_any t x g Header.Gray;
      FStar.Classical.forall_intro (fun (y: obj_addr) -> color_change_preserves_is_infix t y g Header.Gray)
    end;
    write_mmf k ms g1 x a v
#pop-options

#push-options "--z3rlimit 20"
let base_transfer (h: cycle_history) (m m': real_memory)
  : Lemma (requires base_ok h m /\ MPC.within_snapshot (kept h) m.major /\
                    MPC.within_snapshot (kept h) m'.major /\
                    m'.nursery == m.nursery /\ blocks_same m.major m'.major /\
                    GenInv.minor_major_fields_not_free (MPC.outside_snapshot (kept h)) m'.nursery m'.major)
          (ensures base_ok h m')
  = let g = m.major in
    let g' = m'.major in
    let s = kept h in
    let ext (y: obj_addr) (p: nat)
      : Lemma (Seq.mem y (objects zero_addr g) ==> (LL.in_extent g' y p <==> LL.in_extent g y p))
      = if Seq.mem y (objects zero_addr g) then in_extent_same g g' y p
    in
    FStar.Classical.forall_intro_2 ext;
    let b5 (p: nat)
      : Lemma (requires LL.blue_covered g' p \/ SPC.new_covered h.allocated_during_cycle g' p)
              (ensures reclaimable_at_start h p)
      = assert (LL.blue_covered g' p ==> LL.blue_covered g p);
        assert (SPC.new_covered h.allocated_during_cycle g' p ==> SPC.new_covered h.allocated_during_cycle g p)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires b5)
#pop-options

/// ---------------------------------------------------------------------------
/// The invariant, split into core clauses and extra ones (`inv_split`)
/// ---------------------------------------------------------------------------

/// The collector's state, the remembered set's shape, the walk.
let shape_core (r: real_state) : prop =
  let g = r.memory.major in
  let free = GI.phase_free r.phase in
  GI.phase_shape r.memory.nursery g r.free_list r.phase r.scan_pos /\
  RT.ref_table_covers_with free g r.ref_table (Seq.length r.ref_table) /\
  RT.ref_table_sound_with free g r.ref_table (Seq.length r.ref_table) /\
  W.walk_end g zero_addr + 8 >= heap_size

/// The nursery's own pointers, and the remembered set empty with it.
let shape_extra (r: real_state) : prop =
  D.nursery_fields_valid r.memory.nursery /\
  (minor_objects r.memory.nursery == Seq.empty ==> Seq.length r.ref_table == 0)

/// The phase's core clause: snapshot at the beginning and black allocation
/// while marking, the account mid-sweep (the cursor and idle clauses are in
/// `blk_extra`).
let phase_core (r: real_state) (h: cycle_history) : prop =
  let g = r.memory.major in
  match r.phase with
  | Ph.Marking ->
      MP.outside_refs_reached g r.scan_pos (snapshot h) /\
      (forall (x: obj_addr). h.allocated_during_cycle x ==> is_black x g)
  | Ph.Sweeping c -> MPC.sweep_in_snapshot (kept h) g c
  | Ph.Idle -> True

let acc_core (r: real_state) (h: cycle_history) : prop =
  MPC.within_snapshot (kept h) r.memory.major /\ base_ok h r.memory /\ phase_core r h

/// Every remembered slot is a field of a kept block.
let rt_kept_of (h: cycle_history) (rt: seq U64.t) (g: heap) : prop =
  forall (i: nat). i < Seq.length rt ==>
    (exists (x: obj_addr) (j: nat). kept h x /\ j < U64.v (wosize_of_object x g) /\
       U64.v (Seq.index rt i) == U64.v x + j * 8)

/// Garbage keeps its size, the walk its end; mid-sweep, kept blocks past the
/// cursor are black; idle, every allocated block is kept.
let blk_extra (h: cycle_history) (m: real_memory) (ph: Ph.gc_phase) : prop =
  let g = m.major in
  let g0 = h.start_memory.major in
  (forall (x: obj_addr). snapshot h x ==> is_allocated h.start_memory (Major x)) /\
  (forall (x: obj_addr). garbage_at_start h x /\ is_allocated m (Major x) /\ ~(h.allocated_during_cycle x) ==>
     wosize_of_object x g == wosize_of_object x g0) /\
  W.walk_end g zero_addr == W.walk_end g0 zero_addr /\
  (match ph with
   | Ph.Sweeping c -> (forall (x: obj_addr). kept h x /\ U64.v x > U64.v c ==> is_black x g)
   | Ph.Idle -> (forall (x: obj_addr). is_allocated m (Major x) ==> kept h x)
   | Ph.Marking -> True)

#push-options "--z3rlimit 30"
let inv_split (r: real_state) (h: cycle_history)
  : Lemma (PD.run_invariant r h <==>
           (shape_core r /\ shape_extra r /\ acc_core r h /\
            rt_kept_of h r.ref_table r.memory.major /\ blk_extra h r.memory r.phase))
  = match r.phase with
    | Ph.Marking -> ()
    | Ph.Sweeping _ -> ()
    | Ph.Idle -> ()
#pop-options

let mod_diff (a x: nat)
  : Lemma (requires a % 8 == 0 /\ x % 8 == 0 /\ x <= a) (ensures (a - x) % 8 == 0)
  = FStar.Math.Lemmas.lemma_mod_sub_distr a x 8

/// Kept blocks are blocks of the heap.
let kept_mem (h: cycle_history) (m: real_memory) (x: obj_addr)
  : Lemma (requires base_ok h m /\ kept h x)
          (ensures Seq.mem x (objects zero_addr m.major) /\ ~(is_blue x m.major))
  = ()

/// The added clauses across a change of the major heap that keeps every
/// block (and, outside marking, every header).
#push-options "--z3rlimit 30"
let blk_transfer (h: cycle_history) (m m': real_memory) (ph: Ph.gc_phase) (fp fp': U64.t)
  : Lemma (requires blk_extra h m ph /\ base_ok h m /\ blocks_same m.major m'.major /\
                    walk_ok m.major fp /\ walk_ok m'.major fp' /\
                    (~(Ph.Marking? ph) ==>
                       (forall (y: obj_addr). Seq.mem y (objects zero_addr m.major) ==>
                          read_word m'.major (hd_address y) == read_word m.major (hd_address y))))
          (ensures blk_extra h m' ph)
  = let g = m.major in
    let g' = m'.major in
    SPC.walk_end_same_blocks g g';
    match ph with
    | Ph.Sweeping c ->
        let bl (x: obj_addr)
          : Lemma (requires kept h x /\ U64.v x > U64.v c) (ensures is_black x g')
          = kept_mem h m x;
            SPI.colour_of g x; SPI.colour_of g' x
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires bl)
    | _ -> ()
#pop-options

/// The remembered slots across such a change, with possibly the slot `a` of
/// the kept block `x` appended.
#push-options "--z3rlimit 30"
let rt_transfer (h: cycle_history) (m: real_memory) (g': heap) (rt rt': seq U64.t) (x: obj_addr) (a: U64.t)
  : Lemma (requires rt_kept_of h rt m.major /\ base_ok h m /\ blocks_same m.major g' /\
                    (rt' == rt \/
                     (rt' == Seq.snoc rt a /\ kept h x /\ U64.v x <= U64.v a /\
                      U64.v a < U64.v x + U64.v (wosize_of_object x m.major) * 8 /\
                      (U64.v a - U64.v x) % 8 == 0)))
          (ensures rt_kept_of h rt' g')
  = let g = m.major in
    let one (i: nat)
      : Lemma (i < Seq.length rt' ==>
               (exists (y: obj_addr) (j: nat). kept h y /\ j < U64.v (wosize_of_object y g') /\
                  U64.v (Seq.index rt' i) == U64.v y + j * 8))
      = if i >= Seq.length rt' then ()
        else if i < Seq.length rt then begin
          (if Seq.length rt' <> Seq.length rt then Seq.lemma_index_app1 rt (Seq.create 1 a) i);
          assert (Seq.index rt' i == Seq.index rt i);
          eliminate exists (y: obj_addr) (j: nat). kept h y /\ j < U64.v (wosize_of_object y g) /\
              U64.v (Seq.index rt i) == U64.v y + j * 8
          with (kept_mem h m y;
                introduce exists (y: obj_addr) (j: nat). kept h y /\ j < U64.v (wosize_of_object y g') /\
                    U64.v (Seq.index rt' i) == U64.v y + j * 8
                with y j and ())
        end else begin
          Seq.lemma_index_app2 rt (Seq.create 1 a) i;
          kept_mem h m x;
          let j = (U64.v a - U64.v x) / 8 in
          introduce exists (y: obj_addr) (j: nat). kept h y /\ j < U64.v (wosize_of_object y g') /\
              U64.v (Seq.index rt' i) == U64.v y + j * 8
          with x j and ()
        end
    in
    FStar.Classical.forall_intro one
#pop-options

/// ---------------------------------------------------------------------------
/// Nursery resolution across a nursery change
/// ---------------------------------------------------------------------------

/// A change of the nursery that keeps every old object (and the fields of
/// every old closure, which hold the infix headers) keeps every resolution
/// to an old object an object.
#push-options "--z3rlimit 40"
let resolve_kept (ms ms': minor_state) (t: U64.t)
  : Lemma (requires GenInv.minor_heap_shape ms /\ GenInv.minor_heap_shape ms' /\
                    (forall (y: U64.t). Seq.mem y (minor_objects ms) ==> Seq.mem y (minor_objects ms')) /\
                    (forall (y: U64.t) (j: nat). Seq.mem y (minor_objects ms) /\ minor_tag ms y == 247 /\
                       j < minor_wosize ms y ==> minor_read_field ms' y j == minor_read_field ms y j) /\
                    Seq.mem (resolve_minor ms t) (minor_objects ms))
          (ensures Seq.mem (resolve_minor ms' t) (minor_objects ms'))
  = GenInv.minor_heap_shape_elim ms;
    GenInv.minor_heap_shape_elim ms';
    if is_infix_in_minor ms' t then resolve_minor_in_objects ms' t
    else begin
      resolve_minor_non_infix ms' t;
      if is_infix_in_minor ms t then begin
        infix_parent_in_minor_objects ms t;
        infix_parent_value ms t;
        let p = infix_parent ms t in
        let wz = minor_wosize ms t in
        let j : nat = wz - 1 in
        assert (U64.v p + j * 8 == U64.v t - 8);
        assert (minor_read_field ms' p j == minor_read_field ms p j);
        assert (minor_tag ms' t == minor_tag ms t)
      end
      else resolve_minor_non_infix ms t
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The barrier keeps every block
/// ---------------------------------------------------------------------------

let size_of_header (g g': heap) (x: obj_addr)
  : Lemma (requires read_word g' (hd_address x) == read_word g (hd_address x))
          (ensures wosize_of_object x g' == wosize_of_object x g)
  = wosize_of_object_spec x g; wosize_of_object_spec x g'

let size_of_block (g g': heap) (x: obj_addr)
  : Lemma (requires SPI.same_block g g' (hd_address x))
          (ensures wosize_of_object x g' == wosize_of_object x g)
  = wosize_of_object_spec x g; wosize_of_object_spec x g'

/// A write into the body of a block that is not free keeps every block.
let write_blocks (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ SPM.in_body g x a)
          (ensures blocks_same g (write_word g a v) /\
                   (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==>
                      read_word (write_word g a v) (hd_address y) == read_word g (hd_address y)))
  = MM.write_heads g x a v;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (size_of_header g (write_word g a v)))

/// The barrier while marking (darken the old value, then write) keeps every
/// block, and every black block black.
#push-options "--z3rlimit 20"
let marking_blocks (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    SPM.in_body g x a)
          (ensures (let g' = write_word (MM.darken g (read_word g a)) a v in
                    blocks_same g g' /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==> (is_black y g ==> is_black y g'))))
  = let w = read_word g a in
    let g1 = MM.darken g w in
    (if is_pointer w &&
        Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
        is_white (resolve_object (w <: obj_addr) g) g
     then begin
       let t = resolve_object (w <: obj_addr) g in
       Mark.colors_exclusive t g;
       MPC.grey_keeps_blocks g t;
       FStar.Classical.forall_intro (FStar.Classical.move_requires (size_of_block g g1));
       let bl (y: obj_addr)
         : Lemma (requires Seq.mem y (objects zero_addr g) /\ is_black y g) (ensures is_black y g1)
         = Mark.colors_exclusive y g;
           MM.header_kept_facts g g1 y
       in
       FStar.Classical.forall_intro (FStar.Classical.move_requires bl)
     end);
    write_blocks g1 x a v;
    let bl' (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g1) /\ is_black y g1)
              (ensures is_black y (write_word g1 a v))
      = MM.header_kept_facts g1 (write_word g1 a v) y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires bl')
#pop-options

/// ---------------------------------------------------------------------------
/// The remembered set: the slot appended
/// ---------------------------------------------------------------------------

let snoc_appended (b: bool) (a: U64.t) (sl: seq U64.t)
  : Lemma (let sl' = if b then Seq.snoc sl a else sl in
           GB.appended b a sl (Seq.length sl) sl' (Seq.length sl'))
  = if b then begin
      let sl' = Seq.snoc sl a in
      let pre (i: nat) : Lemma (i < Seq.length sl ==> Seq.index sl' i == Seq.index sl i)
        = if i < Seq.length sl then Seq.lemma_index_app1 sl (Seq.create 1 a) i
      in
      FStar.Classical.forall_intro pre;
      Seq.lemma_index_app2 sl (Seq.create 1 a) (Seq.length sl)
    end

/// ---------------------------------------------------------------------------
/// A write into a major scannable block: the barrier
/// ---------------------------------------------------------------------------

/// The program's write, for the accounting: a kept block, a value pointing at
/// a kept block.
#push-options "--z3rlimit 20"
let kept_program_write (free: free_def) (h: cycle_history) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires free_def_ok free /\ SPM.program_write free g x a v /\ scannable g x /\
                    MPC.within_snapshot (kept h) g /\ kept h x /\
                    (is_pointer v ==> kept h (resolve_object (v <: obj_addr) g)))
          (ensures SPM.program_write (MPC.outside_snapshot (kept h)) g x a v)
  = in_use_not_blue free g x;
    in_use_outside_kept (kept h) g x;
    if is_pointer v then begin
      let t = resolve_object (v <: obj_addr) g in
      in_use_not_blue free g t;
      in_use_outside_kept (kept h) g t
    end
#pop-options

/// The phase's clause of the accounting, marking: the deletion barrier keeps
/// every white object of the snapshot one the marker will reach, and the
/// blocks allocated since black.
#push-options "--z3rlimit 30"
let barrier_marking_clause (ms: minor_state) (h: cycle_history) (g: heap) (fp: U64.t) (sp: MP.scan_pos)
    (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires GI.phase_shape ms g fp Ph.Marking sp /\ GB.modify_ok Ph.Marking ms g sp x a v /\
                    MP.outside_refs_reached g sp (snapshot h) /\
                    (forall (y: obj_addr). h.allocated_during_cycle y ==> Seq.mem y (objects zero_addr g) /\ is_black y g))
          (ensures (let g' = GB.modify_heap Ph.Marking g a v in
                    MP.outside_refs_reached g' sp (snapshot h) /\
                    (forall (y: obj_addr). h.allocated_during_cycle y ==> is_black y g')))
  = let o (w: obj_addr) : prop = GMM.nursery_refs ms g w \/ snapshot h w in
    GI.phase_shape_marking ms g fp sp;
    GI.phase_free_marking ();
    assert (MP.marking_inv g o sp);
    MM.marking_write_barrier g o sp x a v;
    shape_facts Ph.Marking ms g fp sp;
    in_use_not_blue free_stw g x;
    marking_blocks g x a v
#pop-options

/// The accounting after the barrier.
#push-options "--z3rlimit 40"
let barrier_accounting (r: real_state) (h: cycle_history) (x: obj_addr) (a: hp_addr) (v: U64.t) (r': real_state)
  : Lemma (requires PD.run_invariant r h /\ scannable r.memory.major x /\ kept h x /\ PD.in_kept r h v /\
                    GB.modify_ok r.phase r.memory.nursery r.memory.major r.scan_pos x a v /\
                    r'.memory.nursery == r.memory.nursery /\ r'.phase == r.phase /\ r'.scan_pos == r.scan_pos /\
                    r'.memory.major == GB.modify_heap r.phase r.memory.major a v)
          (ensures acc_core r' h)
  = let g = r.memory.major in
    let g' = r'.memory.major in
    let ms = r.memory.nursery in
    let ph = r.phase in
    let fp = r.free_list in
    let sp = r.scan_pos in
    let free = GI.phase_free ph in
    GB.modify_heap_facts ph ms g fp sp x a v;
    shape_facts ph ms g fp sp;
    in_use_not_blue free g x;
    kept_program_write free h g x a v;
    (match ph with
     | Ph.Marking ->
         GI.phase_free_marking ();
         MPC.account_barrier (kept h) g x a v;
         marking_blocks g x a v;
         barrier_marking_clause ms h g fp sp x a v;
         barrier_mmf (kept h) ms g x a v
     | Ph.Sweeping c ->
         MPC.account_write (kept h) g x a v;
         write_blocks g x a v;
         SPI.free_incremental_ok c;
         SPI.same_heads_facts g g';
         write_mmf (kept h) ms g x a v
     | Ph.Idle ->
         MPC.account_write (kept h) g x a v;
         write_blocks g x a v;
         write_mmf (kept h) ms g x a v);
    base_transfer h r.memory r'.memory
#pop-options

/// The collector's state and the remembered set after the barrier.
#push-options "--z3rlimit 20"
let barrier_shape (r: real_state) (x: obj_addr) (a: hp_addr) (v: U64.t) (r': real_state)
  : Lemma (requires PD.phase_shape r /\
                    GB.modify_ok r.phase r.memory.nursery r.memory.major r.scan_pos x a v /\
                    r' == { r with memory = { r.memory with major = GB.modify_heap r.phase r.memory.major a v };
                                   ref_table = if GB.modify_records r.memory.major a v
                                               then Seq.snoc r.ref_table (a <: U64.t) else r.ref_table })
          (ensures shape_core r')
  = let g = r.memory.major in
    let ms = r.memory.nursery in
    GB.modify_phase_shape r.phase ms g r.free_list r.scan_pos x a v;
    snoc_appended (GB.modify_records g a v) a r.ref_table;
    GB.modify_ref_table r.phase ms g r.free_list r.scan_pos x a v r.ref_table r'.ref_table
      (Seq.length r.ref_table) (Seq.length r'.ref_table);
    shape_walk_end r.phase ms r'.memory.major r.free_list r.scan_pos
#pop-options

#push-options "--z3rlimit 40"
let barrier_keeps (r: real_state) (h: cycle_history) (x: obj_addr) (a: hp_addr) (v: U64.t) (r': real_state)
  : Lemma (requires PD.run_invariant r h /\ scannable r.memory.major x /\ kept h x /\ PD.in_kept r h v /\
                    GB.modify_ok r.phase r.memory.nursery r.memory.major r.scan_pos x a v /\
                    (is_young v ==> storable_value r v) /\
                    r' == { r with memory = { r.memory with major = GB.modify_heap r.phase r.memory.major a v };
                                   ref_table = if GB.modify_records r.memory.major a v
                                               then Seq.snoc r.ref_table (a <: U64.t) else r.ref_table })
          (ensures PD.run_invariant r' h)
  = let g = r.memory.major in
    let g' = r'.memory.major in
    let ms = r.memory.nursery in
    let ph = r.phase in
    let fp = r.free_list in
    let sp = r.scan_pos in
    let free = GI.phase_free ph in
    inv_split r h;
    barrier_shape r x a v r';
    barrier_accounting r h x a v r';
    shape_facts ph ms g fp sp;
    shape_facts ph ms g' fp sp;
    GB.modify_heap_facts ph ms g fp sp x a v;
    in_use_not_blue free g x;
    (match ph with
     | Ph.Marking -> marking_blocks g x a v
     | _ -> write_blocks g x a v);
    blk_transfer h r.memory r'.memory ph fp fp;
    (if GB.modify_records g a v then begin
       assert (r'.ref_table == Seq.snoc r.ref_table (a <: U64.t));
       assert (SPM.in_body g x a);
       assert (U64.v a % 8 == 0 /\ U64.v x % 8 == 0);
       mod_diff (U64.v a) (U64.v x);
       rt_transfer h r.memory g' r.ref_table r'.ref_table x (a <: U64.t)
     end else rt_transfer h r.memory g' r.ref_table r'.ref_table x (a <: U64.t));
    (if GB.modify_records g a v then
       FStar.Seq.Properties.mem_index (resolve_minor ms (GBase.to_minor_offset v)) (minor_objects ms));
    inv_split r' h
#pop-options

/// ---------------------------------------------------------------------------
/// A raw store into a major no-scan block
/// ---------------------------------------------------------------------------

/// (After `GC.Gen.Barrier`'s private lemmas of the same names.)
let dense_transport (g g': heap)
  : Lemma (requires heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\ SPI.same_heads g g')
          (ensures heap_objects_dense g' /\ Seq.length (objects zero_addr g') > 0)
  = SPI.same_heads_facts g g';
    W.reaches_end_of_dense g;
    W.reaches_refl g zero_addr;
    W.dense_of_reaches_end g' (W.walk_end g zero_addr)

#push-options "--z3rlimit 20"
let body_write_facts (g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ SPM.in_body g x a /\ walk_ok g fp)
          (ensures (let g' = write_word g a v in
                    SPI.same_heads g g' /\ walk_ok g' fp /\
                    objects zero_addr g' == objects zero_addr g /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==>
                       read_word g' (hd_address y) == read_word g (hd_address y)) /\
                    (forall (y: obj_addr) (free: free_def). free_def_ok free ==>
                       in_use free g' y == in_use free g y)))
  = let g' = write_word g a v in
    SPM.in_body_block g x a;
    SPI.colour_of g x;
    SPI.body_write g fp (hd_address x) a v;
    SPI.same_heads_facts g g';
    dense_transport g g'
#pop-options

/// A no-scan block is no closure.
let no_scan_not_closure (g: heap) (x: obj_addr)
  : Lemma (requires is_no_scan x g) (ensures ~(is_closure x g))
  = is_no_scan_spec x g; is_closure_spec x g; no_scan_tag_val (); closure_tag_val ()

#push-options "--z3rlimit 30"
let store_idle (minor: minor_state) (g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires GenInv.collection_heap_shape minor g fp /\ SPM.program_write free_stw g x a v)
          (ensures GenInv.collection_heap_shape minor (write_word g a v) fp)
  = let g' = write_word g a v in
    free_stw_ok ();
    free_def_ok_elim free_stw;
    GenInv.collection_heap_shape_elim minor g fp;
    GenInv.major_heap_shape_elim g fp;
    body_write_facts g fp x a v;
    MM.write_wf g x a v;
    MM.write_heads g x a v;
    PCS.free_list_shape_of_ascending g' fp;
    let ng (y: obj_addr) : Lemma (Seq.mem y (objects zero_addr g) ==> ~(is_gray y g))
      = if Seq.mem y (objects zero_addr g) then SweepInv.no_gray_elim y g
    in
    FStar.Classical.forall_intro ng;
    SweepInv.no_gray_intro g';
    GenInv.major_heap_shape_intro g' fp;
    GenInv.minor_major_fields_not_free_stw minor g;
    GenInv.minor_major_fields_not_free_stw minor g';
    wf_parts ();
    GMM.write_keeps_nursery free_stw minor g x a v;
    GenInv.collection_heap_shape_intro minor g' fp
#pop-options

#push-options "--z3rlimit 20"
let store_sweeping (minor: minor_state) (g: heap) (fp: U64.t) (c: U64.t) (sp: MP.scan_pos)
  (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires GI.phase_shape minor g fp (Ph.Sweeping c) sp /\
                    SPM.program_write (SPI.free_incremental c) g x a v)
          (ensures GI.phase_shape minor (write_word g a v) fp (Ph.Sweeping c) sp)
  = let g' = write_word g a v in
    GI.phase_shape_sweeping minor g fp c sp;
    GI.phase_shape_sweeping minor g' fp c sp;
    SPI.free_incremental_ok c;
    free_def_ok_elim (SPI.free_incremental c);
    SPM.write_sweep_phase g fp c x a v;
    SPI.sweep_inv_incremental_iff g fp c;
    SPI.sweep_shape_elim g fp c;
    body_write_facts g fp x a v;
    wf_with_parts ();
    GMM.write_keeps_nursery (SPI.free_incremental c) minor g x a v
#pop-options

/// While marking, a store into a no-scan block (no barrier: it holds no
/// pointer field), for the nursery's references and any other outside ones.
#push-options "--z3rlimit 30"
let store_marking (minor: minor_state) (g: heap) (fp: U64.t) (sp: MP.scan_pos) (o: obj_addr -> prop)
  (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires GI.phase_shape minor g fp Ph.Marking sp /\ MP.outside_refs_reached g sp o /\
                    SPM.program_write free_stw g x a v /\ is_no_scan x g)
          (ensures GI.phase_shape minor (write_word g a v) fp Ph.Marking sp /\
                   MP.outside_refs_reached (write_word g a v) sp o)
  = let refs (w: obj_addr) : prop = GMM.nursery_refs minor g w \/ o w in
    let g' = write_word g a v in
    GI.phase_shape_marking minor g fp sp;
    GI.phase_shape_marking minor g' fp sp;
    free_stw_ok ();
    free_def_ok_elim free_stw;
    GenInv.collection_shape_with_elim Ph.Marking free_stw minor g fp;
    GenInv.major_shape_with_elim Ph.Marking free_stw g fp;
    assert (MP.marking_inv g refs sp);
    MM.marking_write g refs sp x a v;
    body_write_facts g fp x a v;
    PCS.free_list_shape_of_ascending g' fp;
    GenInv.major_shape_with_intro Ph.Marking free_stw g' fp;
    wf_parts ();
    GMM.write_keeps_nursery free_stw minor g x a v;
    GenInv.collection_shape_with_intro Ph.Marking free_stw minor g' fp
#pop-options

/// The remembered set (after `GC.Gen.Barrier`'s private lemmas).
let field_addr (obj: obj_addr) (j: nat{U64.v obj + j * 8 + 8 <= heap_size}) : hp_addr =
  U64.uint_to_t (U64.v obj + j * 8)

let slot_of (free: free_def) (g: heap) (addr: nat) : prop =
  exists (obj: obj_addr) (j: nat).
    is_block g obj /\ not (free g obj) /\ scannable g obj /\
    j < U64.v (wosize_of_object obj g) /\ addr == U64.v obj + j * 8

let slot_of_transport (free: free_def) (g g': heap) (addr: nat)
  : Lemma (requires slot_of free g addr /\
                    (forall (obj: obj_addr). in_use free g obj ==>
                       in_use free g' obj /\ scannable g' obj == scannable g obj /\
                       wosize_of_object obj g' == wosize_of_object obj g))
          (ensures slot_of free g' addr)
  = eliminate exists (obj: obj_addr) (j: nat).
      is_block g obj /\ not (free g obj) /\ scannable g obj /\
      j < U64.v (wosize_of_object obj g) /\ addr == U64.v obj + j * 8
    with introduce exists (obj: obj_addr) (j: nat).
      is_block g' obj /\ not (free g' obj) /\ scannable g' obj /\
      j < U64.v (wosize_of_object obj g') /\ addr == U64.v obj + j * 8
    with obj j and ()

let sound_intro (free: free_def) (g: heap) (sl: seq U64.t) (n: nat{n <= Seq.length sl})
  (h: (i: nat) -> Lemma (requires i < n /\ n <= Seq.length sl)
                       (ensures U64.v (Seq.index sl i) < heap_size /\ U64.v (Seq.index sl i) % 8 == 0 /\
                                slot_of free g (U64.v (Seq.index sl i))))
  : Lemma (requires n <= Seq.length sl) (ensures RT.ref_table_sound_with free g sl n)
  = let aux (i: nat)
      : Lemma (i < n ==> U64.v (Seq.index sl i) < heap_size /\ U64.v (Seq.index sl i) % 8 == 0 /\
                         slot_of free g (U64.v (Seq.index sl i)))
      = if i < n then h i
    in
    FStar.Classical.forall_intro aux

let covers_intro (free: free_def) (g: heap) (sl: seq U64.t) (n: nat{n <= Seq.length sl})
  (h: (obj: obj_addr) -> (j: nat) ->
      Lemma (requires n <= Seq.length sl /\ is_block g obj /\ not (free g obj) /\ scannable g obj /\
                      j < U64.v (wosize_of_object obj g) /\ U64.v obj + j * 8 + 8 <= heap_size /\
                      Promote.is_minor_pointer (GBase.to_minor_offset
                        (read_word g (U64.uint_to_t (U64.v obj + j * 8)))))
            (ensures exists (i: nat). i < n /\ U64.v (Seq.index sl i) == U64.v obj + j * 8))
  : Lemma (requires n <= Seq.length sl) (ensures RT.ref_table_covers_with free g sl n)
  = FStar.Classical.forall_intro_2 (fun obj -> FStar.Classical.move_requires (h obj))

/// A store into a no-scan block keeps the remembered set: no field of a
/// scannable block is the slot.
#push-options "--z3rlimit 30"
let store_ref_table (free: free_def) (g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  (sl: seq U64.t) (n: nat)
  : Lemma (requires free_def_ok free /\ in_use free g x /\ is_no_scan x g /\ SPM.in_body g x a /\
                    walk_ok g fp /\
                    RT.ref_table_covers_with free g sl n /\ RT.ref_table_sound_with free g sl n)
          (ensures RT.ref_table_covers_with free (write_word g a v) sl n /\
                   RT.ref_table_sound_with free (write_word g a v) sl n)
  = let g' = write_word g a v in
    free_def_ok_elim free;
    body_write_facts g fp x a v;
    let keep (obj: obj_addr)
      : Lemma (in_use free g' obj == in_use free g obj /\
               (in_use free g obj ==> scannable g' obj == scannable g obj /\
                                      wosize_of_object obj g' == wosize_of_object obj g))
      = if in_use free g obj then MM.header_kept_facts g g' obj
    in
    FStar.Classical.forall_intro keep;
    let cov (obj: obj_addr) (j: nat)
      : Lemma (requires n <= Seq.length sl /\ is_block g' obj /\ not (free g' obj) /\ scannable g' obj /\
                        j < U64.v (wosize_of_object obj g') /\ U64.v obj + j * 8 + 8 <= heap_size /\
                        Promote.is_minor_pointer (GBase.to_minor_offset
                          (read_word g' (U64.uint_to_t (U64.v obj + j * 8)))))
              (ensures exists (i: nat). i < n /\ U64.v (Seq.index sl i) == U64.v obj + j * 8)
      = keep obj;
        let fa = field_addr obj j in
        assert (obj <> x);
        assert (SPM.in_body g obj fa);
        SPM.in_body_block g obj fa;
        SPM.other_body g x obj a;
        read_write_different g a fa v
    in
    covers_intro free g' sl n cov;
    let snd_ok (i: nat)
      : Lemma (requires i < n /\ n <= Seq.length sl)
              (ensures U64.v (Seq.index sl i) < heap_size /\ U64.v (Seq.index sl i) % 8 == 0 /\
                       slot_of free g' (U64.v (Seq.index sl i)))
      = assert (slot_of free g (U64.v (Seq.index sl i)));
        slot_of_transport free g g' (U64.v (Seq.index sl i))
    in
    sound_intro free g' sl n snd_ok
#pop-options

/// The account of the snapshot after a store into the body of the no-scan
/// block `x` (kept or not: its fields are no edges).
#push-options "--z3rlimit 30"
let store_within (s: obj_addr -> prop) (g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires MPC.within_snapshot s g /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    is_no_scan x g /\ SPM.in_body g x a /\ walk_ok g fp /\ no_infix_block g)
          (ensures MPC.within_snapshot s (write_word g a v))
  = let g' = write_word g a v in
    let free = MPC.outside_snapshot s in
    MPC.outside_snapshot_ok s;
    body_write_facts g fp x a v;
    write_blocks g x a v;
    no_scan_not_closure g x;
    let col (y: obj_addr)
      : Lemma (Seq.mem y (objects zero_addr g) ==>
               (is_gray y g' <==> is_gray y g) /\ (is_black y g' <==> is_black y g))
      = if Seq.mem y (objects zero_addr g) then MM.header_kept_facts g g' y
    in
    FStar.Classical.forall_intro col;
    if in_use free g x then
      MM.write_wf_with free g x a v
    else begin
      SPM.same_heads_part4 g g';
      let blk (y: obj_addr)
        : Lemma (requires in_use free g y) (ensures SPI.same_block g g' (hd_address y))
        = free_def_ok_elim free;
          assert (y <> x);
          let body (b: hp_addr)
            : Lemma (requires U64.v (hd_address y) < U64.v b /\ U64.v b < W.bnext g (hd_address y))
                    (ensures read_word g' b == read_word g b)
            = SPM.other_body g x y a;
              read_write_different g a b v
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires body)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires blk);
      SPI.wf_transport g g' free free
    end
#pop-options

/// The accounting after the store.
#push-options "--z3rlimit 40"
let store_accounting (r: real_state) (h: cycle_history) (x: obj_addr) (a: hp_addr) (v: U64.t) (r': real_state)
  : Lemma (requires PD.run_invariant r h /\ ~(scannable r.memory.major x) /\
                    in_use (GI.phase_free r.phase) r.memory.major x /\ SPM.in_body r.memory.major x a /\
                    r' == { r with memory = { r.memory with major = write_word r.memory.major a v } })
          (ensures acc_core r' h)
  = let g = r.memory.major in
    let g' = r'.memory.major in
    let ms = r.memory.nursery in
    let ph = r.phase in
    let fp = r.free_list in
    let sp = r.scan_pos in
    let free = GI.phase_free ph in
    shape_facts ph ms g fp sp;
    in_use_not_blue free g x;
    store_within (kept h) g fp x a v;
    write_blocks g x a v;
    body_write_facts g fp x a v;
    no_scan_not_closure g x;
    (match ph with
     | Ph.Marking ->
         GI.phase_free_marking ();
         store_marking ms g fp sp (snapshot h) x a v;
         let bl (y: obj_addr)
           : Lemma (requires Seq.mem y (objects zero_addr g) /\ is_black y g) (ensures is_black y g')
           = MM.header_kept_facts g g' y
         in
         FStar.Classical.forall_intro (FStar.Classical.move_requires bl)
     | Ph.Sweeping c -> SPI.free_incremental_ok c
     | Ph.Idle -> ());
    write_mmf (kept h) ms g x a v;
    base_transfer h r.memory r'.memory
#pop-options

/// The collector's state and the remembered set after the store.
#push-options "--z3rlimit 30"
let store_shape (r: real_state) (h: cycle_history) (x: obj_addr) (a: hp_addr) (v: U64.t) (r': real_state)
  : Lemma (requires PD.run_invariant r h /\ ~(scannable r.memory.major x) /\
                    in_use (GI.phase_free r.phase) r.memory.major x /\ SPM.in_body r.memory.major x a /\
                    r' == { r with memory = { r.memory with major = write_word r.memory.major a v } })
          (ensures shape_core r')
  = let g = r.memory.major in
    let ms = r.memory.nursery in
    let ph = r.phase in
    let fp = r.free_list in
    let sp = r.scan_pos in
    let free = GI.phase_free ph in
    shape_facts ph ms g fp sp;
    no_scan_not_closure g x;
    assert (SPM.program_write free g x a v);
    (match ph with
     | Ph.Idle ->
         GI.phase_free_idle ();
         GI.phase_shape_idle ms g fp sp;
         GI.phase_shape_idle ms (write_word g a v) fp sp;
         store_idle ms g fp x a v
     | Ph.Marking ->
         GI.phase_free_marking ();
         store_marking ms g fp sp (fun _ -> False) x a v
     | Ph.Sweeping c ->
         GI.phase_free_sweeping c;
         store_sweeping ms g fp c sp x a v);
    store_ref_table free g fp x a v r.ref_table (Seq.length r.ref_table);
    shape_walk_end ph ms r'.memory.major fp sp
#pop-options

#push-options "--z3rlimit 40"
let store_keeps (r: real_state) (h: cycle_history) (x: obj_addr) (a: hp_addr) (v: U64.t) (r': real_state)
  : Lemma (requires PD.run_invariant r h /\ ~(scannable r.memory.major x) /\
                    in_use (GI.phase_free r.phase) r.memory.major x /\ SPM.in_body r.memory.major x a /\
                    r' == { r with memory = { r.memory with major = write_word r.memory.major a v } })
          (ensures PD.run_invariant r' h)
  = let g = r.memory.major in
    let g' = r'.memory.major in
    let ms = r.memory.nursery in
    let ph = r.phase in
    let fp = r.free_list in
    let sp = r.scan_pos in
    inv_split r h;
    store_shape r h x a v r';
    store_accounting r h x a v r';
    shape_facts ph ms g fp sp;
    shape_facts ph ms g' fp sp;
    in_use_not_blue (GI.phase_free ph) g x;
    write_blocks g x a v;
    blk_transfer h r.memory r'.memory ph fp fp;
    rt_transfer h r.memory g' r.ref_table r'.ref_table x 0UL;
    inv_split r' h
#pop-options

/// ---------------------------------------------------------------------------
/// A store into the nursery
/// ---------------------------------------------------------------------------

/// The cross-generation condition after a nursery store of a value the
/// condition allows: one that names a non-free block, possibly through an
/// interior pointer (`SPI.storable`).
#push-options "--z3rlimit 20"
let nursery_mmf (free: free_def) (ms ms': minor_state) (g: heap) (o: U64.t) (i: nat) (v: U64.t)
  : Lemma (requires GenInv.minor_major_fields_not_free free ms g /\ nursery_store_frame ms ms' o i v /\
                    (minor_tag ms o < 251 ==> SPI.storable free g v))
          (ensures GenInv.minor_major_fields_not_free free ms' g)
  = let h (obj: U64.t) (j: nat)
      : Lemma (requires Seq.mem obj (minor_objects ms') /\ j < minor_scan_wosize ms' obj /\
                        is_pointer_field (minor_read_field ms' obj j))
              (ensures in_use free g (resolve_object ((minor_read_field ms' obj j) <: obj_addr) g) /\
                       infix_addr_wf g (objects zero_addr g) ((minor_read_field ms' obj j) <: obj_addr))
      = minor_scan_wosize_cases ms obj;
        minor_scan_wosize_cases ms' obj;
        if obj = o && j = i then ()
        else GenInv.minor_major_fields_not_free_elim free ms g obj j
    in
    GenInv.minor_major_fields_not_free_intro free ms' g h
#pop-options

/// The nursery's references after a store.
#push-options "--z3rlimit 20"
let nursery_refs_store (ms ms': minor_state) (g: heap) (o: U64.t) (i: nat) (v: U64.t) (w: obj_addr)
  : Lemma (requires nursery_store_frame ms ms' o i v /\ GMM.nursery_refs ms' g w)
          (ensures GMM.nursery_refs ms g w \/ (is_pointer v /\ resolve_object (v <: obj_addr) g == w))
  = eliminate exists (obj: U64.t) (j: nat).
      Seq.mem obj (minor_objects ms') /\ j < minor_scan_wosize ms' obj /\
      is_pointer_field (minor_read_field ms' obj j) /\
      resolve_object ((minor_read_field ms' obj j) <: obj_addr) g == w
    with begin
      minor_scan_wosize_cases ms obj;
      minor_scan_wosize_cases ms' obj
    end
#pop-options

/// The collector's state at each phase after a nursery store.
#push-options "--z3rlimit 30"
let nursery_shape (ph: Ph.gc_phase) (ms ms': minor_state) (g: heap) (fp: U64.t) (sp: MP.scan_pos)
    (o: U64.t) (i: nat) (v: U64.t)
  : Lemma (requires GI.phase_shape ms g fp ph sp /\ nursery_store_frame ms ms' o i v /\
                    (minor_tag ms o < 251 ==>
                       SPI.storable (GI.phase_free ph) g v /\
                       (Ph.Marking? ph ==> MM.target_ok g (fun _ -> False) sp v)))
          (ensures GI.phase_shape ms' g fp ph sp)
  = match ph with
    | Ph.Idle ->
        GI.phase_free_idle ();
        GI.phase_shape_idle ms g fp sp;
        GI.phase_shape_idle ms' g fp sp;
        GenInv.collection_heap_shape_elim ms g fp;
        GenInv.minor_major_fields_not_free_stw ms g;
        GenInv.minor_major_fields_not_free_stw ms' g;
        nursery_mmf free_stw ms ms' g o i v;
        GenInv.collection_heap_shape_intro ms' g fp
    | Ph.Marking ->
        GI.phase_free_marking ();
        GI.phase_shape_marking ms g fp sp;
        GI.phase_shape_marking ms' g fp sp;
        GenInv.collection_shape_with_elim Ph.Marking free_stw ms g fp;
        nursery_mmf free_stw ms ms' g o i v;
        GenInv.collection_shape_with_intro Ph.Marking free_stw ms' g fp;
        let reach (w: obj_addr)
          : Lemma (requires GMM.nursery_refs ms' g w /\ Seq.mem w (objects zero_addr g) /\ is_white w g)
                  (ensures MP.marker_will_reach g sp w)
          = eliminate exists (obj: U64.t) (j: nat).
              Seq.mem obj (minor_objects ms') /\ j < minor_scan_wosize ms' obj /\
              is_pointer_field (minor_read_field ms' obj j) /\
              resolve_object ((minor_read_field ms' obj j) <: obj_addr) g == w
            with begin
              minor_scan_wosize_cases ms obj;
              minor_scan_wosize_cases ms' obj;
              if obj = o && j = i then ()
              else assert (GMM.nursery_refs ms g w)
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires reach);
        assert (MP.marking_inv g (GMM.nursery_refs ms' g) sp)
    | Ph.Sweeping c ->
        GI.phase_free_sweeping c;
        GI.phase_shape_sweeping ms g fp c sp;
        GI.phase_shape_sweeping ms' g fp c sp;
        nursery_mmf (SPI.free_incremental c) ms ms' g o i v
#pop-options

/// The nursery's own pointers after a store.
#push-options "--z3rlimit 40"
let store_fields_valid (ms ms': minor_state) (o: U64.t) (i: nat) (v: U64.t)
  : Lemma (requires D.nursery_fields_valid ms /\ GenInv.minor_heap_shape ms /\ nursery_store_frame ms ms' o i v /\
                    Seq.mem o (minor_objects ms) /\ minor_tag ms o <> 247 /\
                    (minor_tag ms o < 251 /\ is_young v ==>
                       Seq.mem (resolve_minor ms (GBase.to_minor_offset v)) (minor_objects ms)))
          (ensures D.nursery_fields_valid ms')
  = let one (y: U64.t) (j: nat)
      : Lemma (requires Seq.mem y (minor_objects ms') /\ j < minor_scan_wosize ms' y /\
                        is_young (minor_read_field ms' y j))
              (ensures Seq.mem (resolve_minor ms' (GBase.to_minor_offset (minor_read_field ms' y j)))
                               (minor_objects ms'))
      = minor_scan_wosize_cases ms y;
        minor_scan_wosize_cases ms' y;
        resolve_kept ms ms' (GBase.to_minor_offset (minor_read_field ms' y j))
    in
    FStar.Classical.forall_intro_2 (fun y -> FStar.Classical.move_requires (one y))
#pop-options


#push-options "--z3rlimit 40"
let nursery_keeps (r: real_state) (h: cycle_history) (o: U64.t) (i: nat) (v: U64.t) (r': real_state)
  : Lemma (requires PD.run_invariant r h /\
                    (minor_tag r.memory.nursery o < 251 ==> storable_value r v /\ PD.in_kept r h v) /\
                    Seq.mem o (minor_objects r.memory.nursery) /\ minor_tag r.memory.nursery o <> 247 /\
                    r'.memory.major == r.memory.major /\ r'.free_list == r.free_list /\
                    r'.phase == r.phase /\ r'.scan_pos == r.scan_pos /\ r'.ref_table == r.ref_table /\
                    nursery_store_frame r.memory.nursery r'.memory.nursery o i v)
          (ensures PD.run_invariant r' h)
  = let g = r.memory.major in
    let ms = r.memory.nursery in
    let ms' = r'.memory.nursery in
    let ph = r.phase in
    let free = GI.phase_free ph in
    shape_facts ph ms g r.free_list r.scan_pos;
    (if minor_tag ms o < 251 && is_pointer v then begin
       let t = resolve_object (v <: obj_addr) g in
       in_use_not_blue free g t;
       in_use_outside_kept (kept h) g t
     end);
    inv_split r h;
    nursery_shape ph ms ms' g r.free_list r.scan_pos o i v;
    nursery_mmf (MPC.outside_snapshot (kept h)) ms ms' g o i v;
    store_fields_valid ms ms' o i v;
    inv_split r' h
#pop-options

/// ---------------------------------------------------------------------------
/// Every write
/// ---------------------------------------------------------------------------

/// For a nursery write, the frame of the store (trusted shape, and the walk's
/// facts about a body store that `GC.Gen.MinorHeap` does not export).
let nursery_write_frame (r r': real_state) (b: block_addr) (i: nat) (v: U64.t) : prop =
  match b with
  | Nursery o -> nursery_store_frame r.memory.nursery r'.memory.nursery o i v
  | Major _ -> True

#push-options "--z3rlimit 30"
let major_write_keeps (r: real_state) (h: cycle_history) (x: obj_addr) (i: nat) (v: U64.t) (r': real_state)
  : Lemma (requires PD.run_invariant r h /\ PD.stores_in_kept r h (Write (Major x) i v) /\
                    major_write_step r x i v r')
          (ensures PD.run_invariant r' h)
  = let g = r.memory.major in
    eliminate exists (a: hp_addr). U64.v a == U64.v x + 8 * i /\
      (if scannable g x then
         GB.modify_ok r.phase r.memory.nursery g r.scan_pos x a v /\
         (is_young v ==> storable_value r v) /\
         r' == { r with memory = { r.memory with major = GB.modify_heap r.phase g a v };
                        ref_table = if GB.modify_records g a v then Seq.snoc r.ref_table (a <: U64.t)
                                    else r.ref_table }
       else
         in_use (GI.phase_free r.phase) g x /\ SPM.in_body g x a /\
         r' == { r with memory = { r.memory with major = write_word g a v } })
    with begin
      if scannable g x then barrier_keeps r h x a v r'
      else store_keeps r h x a v r'
    end
#pop-options

let write_keeps (r: real_state) (h: cycle_history) (b: block_addr) (i: nat) (v: U64.t) (r': real_state)
  : Lemma (requires PD.run_invariant r h /\ PD.stores_in_kept r h (Write b i v) /\ step r (Write b i v) r' /\
                    nursery_write_frame r r' b i v)
          (ensures PD.run_invariant r' (update_history h r (Write b i v) r'))
  = assert (update_history h r (Write b i v) r' == h);
    match b with
    | Major x -> major_write_keeps r h x i v r'
    | Nursery o -> nursery_keeps r h o i v r'

/// ---------------------------------------------------------------------------
/// A nursery allocation
/// ---------------------------------------------------------------------------

/// The history up to the blocks allocated since, as a predicate.
#push-options "--z3rlimit 40"
let history_ext (r: real_state) (h h': cycle_history)
  : Lemma (requires PD.run_invariant r h /\ h'.start_memory == h.start_memory /\
                    h'.start_roots == h.start_roots /\
                    (forall (x: obj_addr). h'.allocated_during_cycle x <==> h.allocated_during_cycle x))
          (ensures PD.run_invariant r h')
  = let g = r.memory.major in
    assert (forall (x: obj_addr). snapshot h' x <==> snapshot h x);
    assert (forall (x: obj_addr). kept h' x <==> kept h x);
    MPC.within_snapshot_ext (kept h) (kept h') g;
    let same (y: obj_addr)
      : Lemma (in_use (MPC.outside_snapshot (kept h')) g y == in_use (MPC.outside_snapshot (kept h)) g y)
      = ()
    in
    FStar.Classical.forall_intro same;
    GenInv.minor_major_fields_not_free_intro (MPC.outside_snapshot (kept h')) r.memory.nursery g
      (fun obj j -> GenInv.minor_major_fields_not_free_elim (MPC.outside_snapshot (kept h)) r.memory.nursery g obj j);
    assert (forall (p: nat). SPC.new_covered h'.allocated_during_cycle g p <==> SPC.new_covered h.allocated_during_cycle g p);
    assert (forall (p: nat). reclaimable_at_start h' p <==> reclaimable_at_start h p);
    assert (forall (x: obj_addr). garbage_at_start h' x <==> garbage_at_start h x);
    match r.phase with
    | Ph.Marking -> ()
    | Ph.Sweeping c -> ()
    | Ph.Idle -> ()
#pop-options

#push-options "--z3rlimit 20"
let alloc_mmf (free: free_def) (ms ms': minor_state) (g: heap) (a: U64.t) (tag: nat) (init: seq U64.t)
  : Lemma (requires GenInv.minor_major_fields_not_free free ms g /\ nursery_alloc_frame ms ms' a tag init /\
                    (forall (j: nat). tag < 251 /\ j < Seq.length init ==> SPI.storable free g (Seq.index init j)))
          (ensures GenInv.minor_major_fields_not_free free ms' g)
  = let h (obj: U64.t) (j: nat)
      : Lemma (requires Seq.mem obj (minor_objects ms') /\ j < minor_scan_wosize ms' obj /\
                        is_pointer_field (minor_read_field ms' obj j))
              (ensures in_use free g (resolve_object ((minor_read_field ms' obj j) <: obj_addr) g) /\
                       infix_addr_wf g (objects zero_addr g) ((minor_read_field ms' obj j) <: obj_addr))
      = minor_scan_wosize_cases ms obj;
        minor_scan_wosize_cases ms' obj;
        if obj = a then ()
        else GenInv.minor_major_fields_not_free_elim free ms g obj j
    in
    GenInv.minor_major_fields_not_free_intro free ms' g h
#pop-options

#push-options "--z3rlimit 40"
let alloc_nursery_shape (ph: Ph.gc_phase) (ms ms': minor_state) (g: heap) (fp: U64.t) (sp: MP.scan_pos)
    (a: U64.t) (tag: nat) (init: seq U64.t)
  : Lemma (requires GI.phase_shape ms g fp ph sp /\ nursery_alloc_frame ms ms' a tag init /\
                    (forall (j: nat). tag < 251 /\ j < Seq.length init ==>
                       SPI.storable (GI.phase_free ph) g (Seq.index init j) /\
                       (Ph.Marking? ph ==> MM.target_ok g (fun _ -> False) sp (Seq.index init j))))
          (ensures GI.phase_shape ms' g fp ph sp)
  = match ph with
    | Ph.Idle ->
        GI.phase_free_idle ();
        GI.phase_shape_idle ms g fp sp;
        GI.phase_shape_idle ms' g fp sp;
        GenInv.collection_heap_shape_elim ms g fp;
        GenInv.minor_major_fields_not_free_stw ms g;
        GenInv.minor_major_fields_not_free_stw ms' g;
        alloc_mmf free_stw ms ms' g a tag init;
        GenInv.collection_heap_shape_intro ms' g fp
    | Ph.Marking ->
        GI.phase_free_marking ();
        GI.phase_shape_marking ms g fp sp;
        GI.phase_shape_marking ms' g fp sp;
        GenInv.collection_shape_with_elim Ph.Marking free_stw ms g fp;
        alloc_mmf free_stw ms ms' g a tag init;
        GenInv.collection_shape_with_intro Ph.Marking free_stw ms' g fp;
        let reach (w: obj_addr)
          : Lemma (requires GMM.nursery_refs ms' g w /\ Seq.mem w (objects zero_addr g) /\ is_white w g)
                  (ensures MP.marker_will_reach g sp w)
          = eliminate exists (obj: U64.t) (j: nat).
              Seq.mem obj (minor_objects ms') /\ j < minor_scan_wosize ms' obj /\
              is_pointer_field (minor_read_field ms' obj j) /\
              resolve_object ((minor_read_field ms' obj j) <: obj_addr) g == w
            with begin
              minor_scan_wosize_cases ms obj;
              minor_scan_wosize_cases ms' obj;
              if obj = a then ()
              else assert (GMM.nursery_refs ms g w)
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires reach);
        assert (MP.marking_inv g (GMM.nursery_refs ms' g) sp)
    | Ph.Sweeping c ->
        GI.phase_free_sweeping c;
        GI.phase_shape_sweeping ms g fp c sp;
        GI.phase_shape_sweeping ms' g fp c sp;
        alloc_mmf (SPI.free_incremental c) ms ms' g a tag init
#pop-options

/// The nursery's own pointers after an allocation.
#push-options "--z3rlimit 40"
let alloc_fields_valid (ms ms': minor_state) (a: U64.t) (tag: nat) (init: seq U64.t)
  : Lemma (requires D.nursery_fields_valid ms /\ GenInv.minor_heap_shape ms /\ nursery_alloc_frame ms ms' a tag init /\
                    (forall (j: nat). tag < 251 /\ j < Seq.length init /\ is_young (Seq.index init j) ==>
                       Seq.mem (resolve_minor ms (GBase.to_minor_offset (Seq.index init j))) (minor_objects ms)))
          (ensures D.nursery_fields_valid ms')
  = let one (y: U64.t) (j: nat)
      : Lemma (requires Seq.mem y (minor_objects ms') /\ j < minor_scan_wosize ms' y /\
                        is_young (minor_read_field ms' y j))
              (ensures Seq.mem (resolve_minor ms' (GBase.to_minor_offset (minor_read_field ms' y j)))
                               (minor_objects ms'))
      = minor_scan_wosize_cases ms y;
        minor_scan_wosize_cases ms' y;
        resolve_kept ms ms' (GBase.to_minor_offset (minor_read_field ms' y j))
    in
    FStar.Classical.forall_intro_2 (fun y -> FStar.Classical.move_requires (one y))
#pop-options

/// The new object's initial values, for the conditions above.
#push-options "--z3rlimit 30"
let init_values (r: real_state) (h: cycle_history) (tag: I.tag_t) (init: seq U64.t) (j: nat)
  : Lemma (requires PD.run_invariant r h /\ init_storable r tag init /\
                    PD.stores_in_kept r h (Alloc InNursery tag (Seq.length init) init) /\
                    U64.v tag < 251 /\ j < Seq.length init)
          (ensures (let w = Seq.index init j in
                    SPI.storable (GI.phase_free r.phase) r.memory.major w /\
                    SPI.storable (MPC.outside_snapshot (kept h)) r.memory.major w /\
                    (Ph.Marking? r.phase ==> MM.target_ok r.memory.major (fun _ -> False) r.scan_pos w)))
  = let g = r.memory.major in
    let w = Seq.index init j in
    no_scan_tag_val ();
    shape_facts r.phase r.memory.nursery g r.free_list r.scan_pos;
    if is_pointer w then begin
      let t = resolve_object (w <: obj_addr) g in
      in_use_not_blue (GI.phase_free r.phase) g t;
      in_use_outside_kept (kept h) g t
    end
#pop-options

/// A change of the nursery alone keeps every clause about the major heap.
#push-options "--z3rlimit 40"
let nursery_change (r r': real_state) (h: cycle_history)
  : Lemma (requires shape_core r /\ acc_core r h /\ rt_kept_of h r.ref_table r.memory.major /\
                    blk_extra h r.memory r.phase /\
                    r'.memory.major == r.memory.major /\ r'.free_list == r.free_list /\
                    r'.phase == r.phase /\ r'.scan_pos == r.scan_pos /\ r'.ref_table == r.ref_table /\
                    GI.phase_shape r'.memory.nursery r'.memory.major r'.free_list r'.phase r'.scan_pos /\
                    GenInv.minor_major_fields_not_free (MPC.outside_snapshot (kept h)) r'.memory.nursery r'.memory.major)
          (ensures shape_core r' /\ acc_core r' h /\ rt_kept_of h r'.ref_table r'.memory.major /\
                   blk_extra h r'.memory r'.phase)
  = assert (forall (x: obj_addr). is_allocated r'.memory (Major x) <==> is_allocated r.memory (Major x))
#pop-options

#push-options "--z3rlimit 40"
let nursery_alloc_keeps (r: real_state) (h: cycle_history) (tag: I.tag_t) (size: nat) (init: seq U64.t) (r': real_state)
  : Lemma (requires PD.run_invariant r h /\ PD.stores_in_kept r h (Alloc InNursery tag size init) /\
                    step r (Alloc InNursery tag size init) r' /\
                    (size >= 1 /\ size <= GBase.max_young_wosize /\ U64.v tag <> 249 ==>
                     nursery_alloc_frame r.memory.nursery r'.memory.nursery
                       (minor_alloc_spec r.memory.nursery size (U64.v tag)).obj_addr (U64.v tag) init))
          (ensures PD.run_invariant r' (update_history h r (Alloc InNursery tag size init) r'))
  = let g = r.memory.major in
    let ms = r.memory.nursery in
    let ms' = r'.memory.nursery in
    let a = (minor_alloc_spec ms size (U64.v tag)).obj_addr in
    let ph = r.phase in
    let ok (j: nat)
      : Lemma (U64.v tag < 251 /\ j < Seq.length init ==>
               (let w = Seq.index init j in
                SPI.storable (GI.phase_free r.phase) g w /\
                SPI.storable (MPC.outside_snapshot (kept h)) g w /\
                (Ph.Marking? r.phase ==> MM.target_ok g (fun _ -> False) r.scan_pos w)))
      = if U64.v tag < 251 && j < Seq.length init
        then init_values r h tag init j
    in
    FStar.Classical.forall_intro ok;
    assert (r'.memory.major == g /\ r'.free_list == r.free_list /\ r'.phase == ph /\
            r'.scan_pos == r.scan_pos /\ r'.ref_table == r.ref_table);
    alloc_nursery_shape ph ms ms' g r.free_list r.scan_pos a (U64.v tag) init;
    alloc_mmf (MPC.outside_snapshot (kept h)) ms ms' g a (U64.v tag) init;
    inv_split r h;
    nursery_change r r' h;
    shape_facts ph ms g r.free_list r.scan_pos;
    let yg (j: nat)
      : Lemma (U64.v tag < 251 /\ j < Seq.length init /\ is_young (Seq.index init j) ==>
               Seq.mem (resolve_minor ms (GBase.to_minor_offset (Seq.index init j))) (minor_objects ms))
      = no_scan_tag_val ()
    in
    FStar.Classical.forall_intro yg;
    alloc_fields_valid ms ms' a (U64.v tag) init;
    FStar.Seq.Properties.mem_index a (minor_objects ms');
    inv_split r' h;
    assert (PD.run_invariant r' h);
    let h' = update_history h r (Alloc InNursery tag size init) r' in
    assert (forall (x: obj_addr). ~(made r r' x));
    assert (forall (x: obj_addr). h'.allocated_during_cycle x <==> h.allocated_during_cycle x);
    history_ext r' h h'
#pop-options
