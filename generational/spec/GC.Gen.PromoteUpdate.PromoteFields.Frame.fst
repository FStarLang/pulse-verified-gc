/// Frame lemma: promote_all_spec preserves body reads — implementation
module GC.Gen.PromoteUpdate.PromoteFields.Frame

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas
open GC.Gen.PromoteUpdate.PromoteFields.ReadOther
open GC.Gen.PromoteUpdate.PromoteFields.Step

module AllocLemmas = GC.Spec.Allocator.Lemmas
module WriteBody = GC.Gen.WriteBodyLemmas

private let copy_fields_preserves_wfh_part1 = WriteBody.copy_fields_preserves_wfh_part1
private let copy_fields_preserves_fl_valid_aux = WriteBody.copy_fields_preserves_fl_valid_aux
private let copy_fields_preserves_fl_chain_terminates = WriteBody.copy_fields_preserves_fl_chain_terminates

/// Helper: establish recursive preconditions after a successful promote step.
/// Factored out so each sub-goal is small and fast.
#restart-solver
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0 --z3refresh"
private let promote_step_frame_preconditions
  (minor: minor_state) (major: heap) (fp: U64.t)
  (obj: U64.t) (wz: nat{wz > 0})
  (other: obj_addr) (addr: hp_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      Seq.mem other (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp other heap_words = true /\
      U64.v addr >= U64.v other /\
      U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other major) * 8 /\
      (promote_object minor major obj fp wz).new_addr <> 0UL)
    (ensures
      (let res = promote_object minor major obj fp wz in
       well_formed_heap_part1 res.major_out /\
       AllocLemmas.fl_valid res.major_out res.fp_out heap_words /\
       AllocLemmas.fl_chain_terminates res.major_out res.fp_out heap_words /\
       Seq.mem other (objects zero_addr res.major_out) /\
       AllocLemmas.chain_avoids res.major_out res.fp_out other heap_words = true /\
       read_word res.major_out addr == read_word major addr /\
       wosize_of_object other res.major_out == wosize_of_object other major))
  = let fuel = heap_words in
    promote_object_read_other minor major obj fp wz other addr;
    // promote_object preserves all allocator invariants
    promote_object_preserves_alloc_invariants minor major obj fp wz;
    // chain_avoids
    promote_object_preserves_chain_avoids minor major obj fp wz other;
    // objects membership
    promote_object_preserves_objects_part1 minor major obj fp wz;
    // wosize preservation
    promote_object_wosize_preserved minor major obj fp wz other
#pop-options

#restart-solver
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0 --z3refresh"
private let rec promote_all_aux_read_other
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  (other: obj_addr) (addr: hp_addr) (bound: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      Seq.mem other (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp other heap_words = true /\
      U64.v addr >= U64.v other /\
      U64.v addr + 8 <= U64.v other + bound * 8 /\
      U64.v (wosize_of_object other major) >= bound)
    (ensures
      (let res = promote_all_aux minor major fp live_set fwd idx in
       read_word res.major_final addr == read_word major addr))
    (decreases (Seq.length live_set - idx))
  = if idx >= Seq.length live_set then ()
    else begin
      let obj = Seq.index live_set idx in
      let wz = minor_wosize minor obj in
      if wz = 0 then begin
        promote_all_aux_read_other minor major fp live_set fwd (idx + 1) other addr bound;
        assert (promote_all_aux minor major fp live_set fwd idx ==
                promote_all_aux minor major fp live_set fwd (idx + 1))
      end
      else begin
        let res = promote_object minor major obj fp wz in
        if res.new_addr = 0UL then ()
        else begin
          promote_step_frame_preconditions minor major fp obj wz other addr;
          assert (wosize_of_object other res.major_out == wosize_of_object other major);
          let fwd' = extend_forwarding fwd obj res.new_addr in
          promote_all_aux_read_other minor res.major_out res.fp_out
                                     live_set fwd' (idx + 1) other addr bound;
          assert (promote_all_aux minor major fp live_set fwd idx ==
                  promote_all_aux minor res.major_out res.fp_out live_set fwd' (idx + 1))
        end
      end
    end
#pop-options

let promote_all_read_other
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  (other: obj_addr) (addr: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    Seq.mem other (objects zero_addr major) /\
                    AllocLemmas.chain_avoids major fp other heap_words = true /\
                    U64.v addr >= U64.v other /\
                    U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other major) * 8)
          (ensures (let res = promote_all_spec minor major fp live_set in
                    read_word res.major_final addr == read_word major addr))
  = let bound = U64.v (wosize_of_object other major) in
    promote_all_aux_read_other minor major fp live_set empty_forwarding 0 other addr bound
