/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Simulation.Frame - what real writes do to the blocks
/// ---------------------------------------------------------------------------
///
/// The real writes meet `GC.Gen.Run.Simulation.Program.write_frame`: a store
/// into the body of an allocated major block keeps the walk and every header
/// (`MM.write_heads`), and every other field, since two blocks of the walk
/// have disjoint extents (`SPC.extents_disjoint`); and recolouring a
/// non-free block (the barrier's darkening while marking) changes nothing
/// the program sees (`same_blocks`).  So every major write -- a raw no-scan
/// store, or the barrier at any phase -- meets it
/// (`major_write_keeps_given`).  (Nursery stores: to do, from the nursery
/// step relation's frame.)

module GC.Gen.Run.Simulation.Frame

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents
open GC.Gen.Run.Simulation.Program
open GC.Gen.Run.Simulation.Enabled

module U64 = FStar.UInt64
module MM = GC.Spec.MarkPhase.Mutator
module SPM = GC.Spec.SweepPhase.Mutator
module SPC = GC.Spec.SweepPhase.Completeness
module LL = GC.Spec.FusedSweep.Lossless
module Ph = GC.Spec.Phase
module GB = GC.Gen.Barrier
module I = GC.Model.Ideal
module Header = GC.Lib.Header

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// The real state with the major heap's word `a` now `v`.
let with_major_word (r: real_state) (a: hp_addr) (v: U64.t) : real_state =
  { r with memory = { r.memory with major = write_word r.memory.major a v } }

#push-options "--z3rlimit 60"
let other_field (g: heap) (x y: obj_addr) (i j: nat) (a: hp_addr) (v: U64.t)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
                    U64.v a == U64.v x + 8 * i /\ i < U64.v (wosize_of_object x g) /\
                    j < U64.v (wosize_of_object y g) /\ ~(y == x /\ j == i))
          (ensures major_field (write_word g a v) y j == major_field g y j)
  = let p = U64.v y + j * 8 in
    if p + 8 <= heap_size then begin
      let q : hp_addr = U64.uint_to_t p in
      if U64.v q = U64.v a then begin
        hd_address_spec x;
        hd_address_spec y;
        assert (LL.in_extent g x p);
        assert (LL.in_extent g y p);
        SPC.extents_disjoint g x y p
      end else
        read_write_different g a q v
    end
#pop-options

#push-options "--z3rlimit 60"
/// **A store into the body of an allocated major block meets `write_frame`.**
let major_body_write_frame (r: real_state) (x: obj_addr) (i: nat) (a: hp_addr) (v: U64.t)
  : Lemma (requires is_allocated r.memory (Major x) /\ U64.v a == U64.v x + 8 * i /\
                    i < U64.v (wosize_of_object x r.memory.major))
          (ensures write_frame r (with_major_word r a v) (Major x) i v)
  = let g = r.memory.major in
    let g' = write_word g a v in
    let r' = with_major_word r a v in
    assert (SPM.in_body g x a);
    MM.write_heads g x a v;
    let aux (y: obj_addr) : Lemma (is_allocated r'.memory (Major y) <==> is_allocated r.memory (Major y)) = () in
    FStar.Classical.forall_intro aux;
    let aux2 (y: obj_addr)
      : Lemma (is_allocated r.memory (Major y) ==>
               block_tag r'.memory (Major y) == block_tag r.memory (Major y) /\
               block_size r'.memory (Major y) == block_size r.memory (Major y))
      = tag_of_object_spec y g; tag_of_object_spec y g';
        wosize_of_object_spec y g; wosize_of_object_spec y g' in
    FStar.Classical.forall_intro aux2;
    let aux3 (b': block_addr) (j: nat)
      : Lemma (is_allocated r.memory b' /\ j < block_size r.memory b' /\ ~(b' == Major x /\ j == i) ==>
               block_field r'.memory b' j == block_field r.memory b' j)
      = match b' with
        | Major y -> FStar.Classical.move_requires (other_field g x y i j a) v
        | Nursery _ -> () in
    FStar.Classical.forall_intro_2 aux3;
    read_write_same g a v;
    assert (U64.v x + i * 8 == U64.v a);
    assert (block_field r'.memory (Major x) i == v)
#pop-options

/// ---------------------------------------------------------------------------
/// Recolouring, and the barrier while marking
/// ---------------------------------------------------------------------------

/// The real state with the major heap `g'`.
let with_major (r: real_state) (g': heap) : real_state =
  { r with memory = { r.memory with major = g' } }

/// Nothing a block of the program sees changes: the same blocks allocated,
/// with their tags, sizes and fields.
let same_blocks (r r': real_state) : prop =
  (forall (b: block_addr). is_allocated r'.memory b <==> is_allocated r.memory b) /\
  (forall (b: block_addr). is_allocated r.memory b ==>
     block_tag r'.memory b == block_tag r.memory b /\ block_size r'.memory b == block_size r.memory b) /\
  (forall (b: block_addr) (j: nat). is_allocated r.memory b /\ j < block_size r.memory b ==>
     block_field r'.memory b j == block_field r.memory b j)

#push-options "--z3rlimit 60"
let recolor_block (g: heap) (t: obj_addr) (c: color) (y: obj_addr)
  : Lemma (requires c <> Header.Blue /\ Seq.mem t (objects zero_addr g) /\ ~(is_blue t g) /\
                    Seq.mem y (objects zero_addr g))
          (ensures (let g' = set_object_color t g c in
                    (is_blue y g' <==> is_blue y g) /\
                    tag_of_object y g' == tag_of_object y g /\
                    wosize_of_object y g' == wosize_of_object y g /\
                    (forall (j: nat). j < U64.v (wosize_of_object y g) ==> major_field g' y j == major_field g y j)))
  = let g' = set_object_color t g c in
    is_blue_iff y g; is_blue_iff y g';
    if y = t then begin
      set_color_preserves_not_blue t t g c;
      color_preserves_tag t g c;
      color_preserves_wosize t g c
    end else begin
      hd_address_injective t y;
      color_change_locality t y g c;
      color_change_header_locality t (hd_address y) g c;
      tag_of_object_spec y g; tag_of_object_spec y g';
      wosize_of_object_spec y g; wosize_of_object_spec y g'
    end;
    let aux (j: nat) : Lemma (j < U64.v (wosize_of_object y g) ==> major_field g' y j == major_field g y j) =
      let p = U64.v y + j * 8 in
      if j < U64.v (wosize_of_object y g) && p + 8 <= heap_size then begin
        let q : hp_addr = U64.uint_to_t p in
        if q = hd_address t then begin
          hd_address_spec t;
          hd_address_spec y;
          assert (LL.in_extent g y p);
          assert (LL.in_extent g t p);
          if y = t then () else SPC.extents_disjoint g y t p
        end else
          color_change_header_locality t q g c
      end in
    FStar.Classical.forall_intro aux
#pop-options

#push-options "--z3rlimit 40"
/// **Recolouring a non-free block to a non-blue colour changes nothing the
/// program sees.**
let recolor_same_blocks (r: real_state) (t: obj_addr) (c: color)
  : Lemma (requires c <> Header.Blue /\ Seq.mem t (objects zero_addr r.memory.major) /\ ~(is_blue t r.memory.major))
          (ensures same_blocks r (with_major r (set_object_color t r.memory.major c)))
  = let g = r.memory.major in
    color_change_preserves_objects g t c;
    let aux (y: obj_addr) : Lemma (Seq.mem y (objects zero_addr g) ==>
        (let g' = set_object_color t g c in
         (is_blue y g' <==> is_blue y g) /\ tag_of_object y g' == tag_of_object y g /\
         wosize_of_object y g' == wosize_of_object y g /\
         (forall (j: nat). j < U64.v (wosize_of_object y g) ==> major_field g' y j == major_field g y j))) =
      FStar.Classical.move_requires (recolor_block g t c) y in
    FStar.Classical.forall_intro aux
#pop-options

/// **The deletion barrier's darkening changes nothing the program sees.**
let darken_same_blocks (r: real_state) (w: U64.t)
  : Lemma (same_blocks r (with_major r (MM.darken r.memory.major w)))
  = let g = r.memory.major in
    if is_pointer w &&
       Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
       is_white (resolve_object (w <: obj_addr) g) g
    then begin
      let t = resolve_object (w <: obj_addr) g in
      makeGray_eq t g;
      is_white_iff t g; is_blue_iff t g;
      recolor_same_blocks r t Header.Gray
    end

/// `same_blocks` then `write_frame` is `write_frame`.
let same_then_write (r r1 r': real_state) (b: block_addr) (i: nat) (v: U64.t)
  : Lemma (requires same_blocks r r1 /\ write_frame r1 r' b i v)
          (ensures write_frame r r' b i v)
  = ()

#push-options "--z3rlimit 60"
/// Every major write -- the barrier at any phase, or a raw store -- meets
/// `write_frame`.
let major_write_frame (r r': real_state) (x: obj_addr) (i: nat) (a: hp_addr) (v: U64.t)
  : Lemma (requires is_allocated r.memory (Major x) /\ i < U64.v (wosize_of_object x r.memory.major) /\
                    U64.v a == U64.v x + 8 * i /\
                    (let g = r.memory.major in
                     if scannable g x
                     then r'.memory == { r.memory with major = GB.modify_heap r.phase g a v }
                     else r'.memory == { r.memory with major = write_word g a v }))
          (ensures write_frame r r' (Major x) i v)
  = let g = r.memory.major in
    let r1 = if scannable g x && Ph.Marking? r.phase
             then with_major r (MM.darken g (read_word g a)) else r in
    darken_same_blocks r (read_word g a);
    assert (same_blocks r r1);
    assert (is_allocated r1.memory (Major x));
    assert (i < U64.v (wosize_of_object x r1.memory.major));
    major_body_write_frame r1 x i a v;
    assert (r'.memory == (with_major_word r1 a v).memory);
    same_then_write r r1 r' (Major x) i v
#pop-options

#push-options "--z3rlimit 60"
/// A major write step meets `write_frame`.
let major_step_frame (r: real_state) (x: obj_addr) (i: nat) (v: U64.t) (r': real_state)
  : Lemma (requires step r (Write (Major x) i v) r' /\ is_allocated r.memory (Major x) /\
                    i < U64.v (wosize_of_object x r.memory.major))
          (ensures write_frame r r' (Major x) i v)
  = let g = r.memory.major in
    eliminate exists (a: hp_addr). U64.v a == U64.v x + 8 * i /\
      (if scannable g x then
         GB.modify_ok r.phase r.memory.nursery g r.scan_pos x a v /\
         (is_young v ==> storable_value r v) /\
         r' == { r with memory = { r.memory with major = GB.modify_heap r.phase g a v };
                        ref_table = if GB.modify_records g a v then Seq.snoc r.ref_table (a <: U64.t)
                                    else r.ref_table }
       else
         in_use (GC.Gen.Incremental.phase_free r.phase) g x /\ SPM.in_body g x a /\
         r' == { r with memory = { r.memory with major = write_word g a v } })
    with begin
      major_write_frame r r' x i a v
    end
#pop-options

#push-options "--z3rlimit 60"
/// **`write_keeps_sim_inv` for a major write**: a raw store into a no-scan
/// block, or the barrier (while marking it first darkens the old value's
/// target, which changes only a colour).
let major_write_keeps_given (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (x: obj_addr) (i: nat) (v: U64.t) (obj: I.obj_id) (v': I.value) (r': real_state)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im (I.Write obj i v') /\
                    translates r.memory ids (Write (Major x) i v) (I.Write obj i v') /\
                    step r (Write (Major x) i v) r')
          (ensures sim_inv_parts r' (update_history h r (Write (Major x) i v) r')
                     (I.ideal_step im (I.Write obj i v'))
                     (update_block_ids ids (Seq.length im.I.objects) r (Write (Major x) i v) r'))
  = let e = Write (Major x) i v in
    let pe = I.Write obj i v' in
    let g = r.memory.major in
    stores_in_kept_given r h im ids e pe;
    write_keeps_run_invariant r h (Major x) i v r';
    I.ideal_step_wf im pe;
    copies_faithful_elim r.memory h im ids (Major x) obj;
    assert (is_allocated r.memory (Major x));
    assert (i < U64.v (wosize_of_object x g));
    major_step_frame r x i v r';
    write_represents r r' h im ids (Major x) i v obj v'
#pop-options

