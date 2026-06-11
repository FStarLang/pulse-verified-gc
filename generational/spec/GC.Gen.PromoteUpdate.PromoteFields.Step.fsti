/// Step lemma: one promote_object call preserves the inductive invariant
module GC.Gen.PromoteUpdate.PromoteFields.Step

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
open GC.Gen.PromoteUpdate.PromoteFields.ChainInv

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// promote_object preserves wosize_of_object for any other object with chain_avoids
val promote_object_wosize_preserved
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wz: nat{wz > 0}) (other: obj_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      Seq.mem other (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp other (heap_size / U64.v mword) = true)
    (ensures
      wosize_of_object other (promote_object minor major obj fp wz).major_out ==
      wosize_of_object other major)

val promote_step_preserves_invariant
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      idx < Seq.length live_set /\
      (let obj = Seq.index live_set idx in
       let wz = minor_wosize minor obj in
       wz > 0 /\
       (promote_object minor major obj fp wz).new_addr <> 0UL) /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      fields_match_minor minor major fwd live_set idx /\
      chain_all_inv minor major fp live_set fwd idx)
    (ensures (let obj = Seq.index live_set idx in
              let wz = minor_wosize minor obj in
              let res = promote_object minor major obj fp wz in
              let fwd' = extend_forwarding fwd obj res.new_addr in
              well_formed_heap_part1 res.major_out /\
              AllocLemmas.fl_valid res.major_out res.fp_out (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates res.major_out res.fp_out (heap_size / U64.v mword) /\
              fields_match_minor minor res.major_out fwd' live_set (idx + 1) /\
              chain_all_inv minor res.major_out res.fp_out live_set fwd' (idx + 1)))
