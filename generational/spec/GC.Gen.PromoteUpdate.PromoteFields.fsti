/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.PromoteFields — promote_all field/read preservation
/// ---------------------------------------------------------------------------

module GC.Gen.PromoteUpdate.PromoteFields

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// Re-export distinct_live_set from FieldsPres
let distinct_live_set = GC.Gen.PromoteUpdate.PromoteFields.FieldsPres.distinct_live_set

val promote_all_preserves_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    distinct_live_set live_set)
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fields_match_minor minor res.major_final res.fwd_map
                                       live_set (Seq.length live_set)))

val promote_all_read_other
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  (other: obj_addr) (addr: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Seq.mem other (objects 0UL major) /\
                    AllocLemmas.chain_avoids major fp other (heap_size / U64.v mword) = true /\
                    U64.v addr >= U64.v other /\
                    U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other major) * 8)
          (ensures (let res = promote_all_spec minor major fp live_set in
                    read_word res.major_final addr == read_word major addr))
