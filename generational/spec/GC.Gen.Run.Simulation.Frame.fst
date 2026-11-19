/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Simulation.Frame - what real writes do to the blocks
/// ---------------------------------------------------------------------------
///
/// The real writes meet `GC.Gen.Run.Simulation.Program.write_frame`: a store
/// into the body of an allocated major block keeps the walk and every header
/// (`MM.write_heads`), and every other field, since two blocks of the walk
/// have disjoint extents (`SPC.extents_disjoint`).  So a raw no-scan store,
/// and the barrier outside marking (`GB.modify_heap` is then the store),
/// meet it.  (The barrier while marking also darkens the old value's target;
/// a nursery store needs the nursery walk to be unchanged by a body store,
/// which `GC.Gen.MinorHeap` does not export: both remain to be done.)

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

#push-options "--z3rlimit 60"
/// **`write_keeps_sim_inv` for a major write that is a plain store**: into a
/// no-scan block, or through the barrier outside marking -- given
/// `infix_exact` (see `GC.Gen.Run.Simulation.Enabled`).
let major_write_keeps_given (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (x: obj_addr) (i: nat) (v: U64.t) (obj: I.obj_id) (v': I.value) (r': real_state)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im (I.Write obj i v') /\
                    translates ids (Write (Major x) i v) (I.Write obj i v') /\
                    step r (Write (Major x) i v) r' /\ infix_exact im v' /\
                    (scannable r.memory.major x ==> ~(Ph.Marking? r.phase)))
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
      major_body_write_frame r x i a v;
      assert (r'.memory == (with_major_word r a v).memory);
      assert (write_frame r r' (Major x) i v);
      write_represents r r' h im ids (Major x) i v obj v'
    end
#pop-options
