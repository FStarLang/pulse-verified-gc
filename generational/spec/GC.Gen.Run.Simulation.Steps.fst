/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Simulation.Steps - allocations and writes keep the simulation
/// ---------------------------------------------------------------------------
///
/// `GC.Gen.Run.Simulation.alloc_keeps_sim_inv` and `write_keeps_sim_inv`:
/// the run invariant from `GC.Gen.Run.Invariant` (its hypothesis,
/// `stores_in_kept`, from `GC.Gen.Run.Simulation.Enabled.stores_in_kept_given`),
/// and `represents` from what each real step does to the blocks --
/// `write_frame` (`GC.Gen.Run.Simulation.Program.write_represents`) or
/// `alloc_frame` (`GC.Gen.Run.Simulation.Alloc.alloc_represents`).  The
/// nursery's frames are the step relation's (`nursery_store_frame`,
/// `nursery_alloc_frame`); the major heap's are proved
/// (`GC.Gen.Run.Simulation.Frame`, and `major_alloc_frame` below).

module GC.Gen.Run.Simulation.Steps

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
open GC.Gen.Run.Simulation.Alloc

module U64 = FStar.UInt64
module I = GC.Model.Ideal
module SPC = GC.Spec.SweepPhase.Completeness
module LL = GC.Spec.FusedSweep.Lossless
module Fr = GC.Gen.Run.Simulation.Frame

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Frames of the real steps
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 60"
/// A nursery store meets `write_frame` (the step relation's frame).
let nursery_step_frame (r: real_state) (o: U64.t) (i: nat) (v: U64.t) (r': real_state)
  : Lemma (requires step r (Write (Nursery o) i v) r')
          (ensures write_frame r r' (Nursery o) i v)
  = ()
#pop-options

/// The block `a` a direct allocation makes was not allocated: its first
/// word was in a free block, and blocks of the walk do not overlap.
let was_free_not_allocated (r r': real_state) (a: obj_addr)
  : Lemma (requires was_free r.memory.major r'.memory.major a)
          (ensures ~(is_allocated r.memory (Major a)))
  = let g = r.memory.major in
    let p = U64.v (hd_address a) in
    introduce is_allocated r.memory (Major a) ==> False
    with begin
      assert (LL.in_extent r'.memory.major a p);
      assert (LL.blue_covered g p);
      eliminate exists (y: obj_addr). Seq.mem y (objects zero_addr g) /\ is_blue y g /\ LL.in_extent g y p
      with begin
        assert (LL.in_extent g a p);
        SPC.extents_disjoint g a y p
      end
    end

#push-options "--z3rlimit 80"
/// A direct major allocation meets `alloc_frame`.
let major_alloc_frame (r: real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t) (r': real_state)
  : Lemma (requires step r (Alloc InMajor tag size init) r')
          (ensures exists (a: obj_addr). alloc_frame r r' (Major a) tag size init)
  = eliminate exists (a: obj_addr).
      was_free r.memory.major r'.memory.major a /\
      is_allocated r'.memory (Major a) /\
      tag_of_object a r'.memory.major == tag /\ U64.v (wosize_of_object a r'.memory.major) == size /\
      color_of_object a r'.memory.major == GC.Spec.Phase.allocation_color r.phase (hd_address a) /\
      (forall (i: nat). i < size ==> block_field r'.memory (Major a) i == Seq.index init i) /\
      (forall (x: obj_addr). x <> a ==>
         (is_allocated r.memory (Major x) <==> is_allocated r'.memory (Major x)) /\
         (is_allocated r.memory (Major x) ==> same_block r.memory.major r'.memory.major x)) /\
      r'.ref_table == (if I.tag_scannable tag then Seq.append r.ref_table (young_slots a init)
                       else r.ref_table)
    with begin
      was_free_not_allocated r r' a;
      let g = r.memory.major in
      let g' = r'.memory.major in
      let aux (x: obj_addr)
        : Lemma (is_allocated r.memory (Major x) ==>
                 U64.v (tag_of_object x g') == U64.v (tag_of_object x g) /\
                 U64.v (wosize_of_object x g') == U64.v (wosize_of_object x g))
        = if x = a then ()
          else begin
            tag_of_object_spec x g; tag_of_object_spec x g';
            wosize_of_object_spec x g; wosize_of_object_spec x g'
          end in
      FStar.Classical.forall_intro aux;
      assert (alloc_frame r r' (Major a) tag size init)
    end
#pop-options

#push-options "--z3rlimit 80"
/// A nursery allocation meets `alloc_frame` (the step relation's frame).
let nursery_alloc_frame_of (r: real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t) (r': real_state)
  : Lemma (requires step r (Alloc InNursery tag size init) r')
          (ensures exists (a: U64.t). alloc_frame r r' (Nursery a) tag size init)
  = let res = minor_alloc_spec r.memory.nursery size (U64.v tag) in
    let a = res.obj_addr in
    assert (alloc_frame r r' (Nursery a) tag size init)
#pop-options

/// ---------------------------------------------------------------------------
/// The two lemmas
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 60"
/// **`GC.Gen.Run.Simulation.write_keeps_sim_inv`.**
let write_keeps (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im pe /\ translates r.memory ids e pe /\
                    step r e r' /\ Write? e)
          (ensures sim_inv_parts r' (update_history h r e r') (I.ideal_step im pe)
                     (update_block_ids ids (Seq.length im.I.objects) r e r'))
  = match e, pe with
    | Write (Major x) i v, I.Write obj _ v' ->
        Fr.major_write_keeps_given r h im ids x i v obj v' r'
    | Write (Nursery o) i v, I.Write obj _ v' ->
        stores_in_kept_given r h im ids e pe;
        write_keeps_run_invariant r h (Nursery o) i v r';
        I.ideal_step_wf im pe;
        nursery_step_frame r o i v r';
        write_represents r r' h im ids (Nursery o) i v obj v'
#pop-options

#push-options "--z3rlimit 60"
let alloc_keeps_at (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (site: alloc_site) (tag: I.tag_t) (size: nat) (init: seq U64.t) (f: I.ideal_fields) (r': real_state)
    (nb: block_addr)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im (I.Alloc tag size f) /\
                    translates r.memory ids (Alloc site tag size init) (I.Alloc tag size f) /\
                    step r (Alloc site tag size init) r' /\ alloc_frame r r' nb tag size init)
          (ensures (let e = Alloc site tag size init in
                    sim_inv_parts r' (update_history h r e r') (I.ideal_step im (I.Alloc tag size f))
                      (update_block_ids ids (Seq.length im.I.objects) r e r')))
  = let e = Alloc site tag size init in
    let pe = I.Alloc tag size f in
    stores_in_kept_given r h im ids e pe;
    alloc_keeps_run_invariant r h site tag size init r';
    I.ideal_step_wf im pe;
    let h' = update_history h r e r' in
    assert (history_grows h h' nb);
    alloc_represents r r' h h' im ids nb tag size f init
#pop-options

/// **`GC.Gen.Run.Simulation.alloc_keeps_sim_inv`.**
let alloc_keeps (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires sim_inv_parts r h im ids /\ I.wf_event im pe /\ translates r.memory ids e pe /\
                    step r e r' /\ Alloc? e)
          (ensures sim_inv_parts r' (update_history h r e r') (I.ideal_step im pe)
                     (update_block_ids ids (Seq.length im.I.objects) r e r'))
  = match e, pe with
    | Alloc InMajor tag size init, I.Alloc _ _ f ->
        major_alloc_frame r tag size init r';
        eliminate exists (a: obj_addr). alloc_frame r r' (Major a) tag size init
        with alloc_keeps_at r h im ids InMajor tag size init f r' (Major a)
    | Alloc InNursery tag size init, I.Alloc _ _ f ->
        nursery_alloc_frame_of r tag size init r';
        eliminate exists (a: U64.t). alloc_frame r r' (Nursery a) tag size init
        with alloc_keeps_at r h im ids InNursery tag size init f r' (Nursery a)
