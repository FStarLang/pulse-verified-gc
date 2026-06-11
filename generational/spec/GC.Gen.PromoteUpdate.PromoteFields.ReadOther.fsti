/// Helpers: promote_object read/chain preservation for OTHER objects
module GC.Gen.PromoteUpdate.PromoteFields.ReadOther

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

module AllocLemmas = GC.Spec.Allocator.Lemmas

#push-options "--z3rlimit 20"

val promote_object_read_other
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0}) (other: obj_addr) (addr: hp_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      Seq.mem other (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp other (heap_size / U64.v mword) = true /\
      U64.v addr >= U64.v other /\
      U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other major) * 8 /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures read_word (promote_object minor major obj fp wosize).major_out addr ==
             read_word major addr)

val promote_object_preserves_chain_avoids
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0}) (excl: U64.t)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      AllocLemmas.chain_avoids major fp excl (heap_size / U64.v mword) = true /\
      U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
      U64.v excl % U64.v mword == 0 /\
      Seq.mem (excl <: obj_addr) (objects zero_addr major) /\
      U64.v (wosize_of_object (excl <: obj_addr) major) >= 1 /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      (let res = promote_object minor major obj fp wosize in
       AllocLemmas.chain_avoids res.major_out res.fp_out excl (heap_size / U64.v mword) = true))

val promote_object_preserves_one_field
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wz: nat{wz > 0})
  (prev_addr: obj_addr) (j: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      Seq.mem prev_addr (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp prev_addr (heap_size / U64.v mword) = true /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      U64.v prev_addr + j * 8 + 8 <= heap_size /\
      U64.v prev_addr % 8 == 0 /\
      U64.v prev_addr + j * 8 < U64.v prev_addr + U64.v (wosize_of_object prev_addr major) * 8)
    (ensures read_word (promote_object minor major obj fp wz).major_out
                       (U64.uint_to_t (U64.v prev_addr + j * 8)) ==
             read_word major (U64.uint_to_t (U64.v prev_addr + j * 8)))
