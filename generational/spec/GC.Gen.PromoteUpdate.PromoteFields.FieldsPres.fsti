/// Recursive field preservation through promote_all_aux
module GC.Gen.PromoteUpdate.PromoteFields.FieldsPres

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate.PromoteFields.ChainInv

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// Distinctness: no two positions in live_set share the same address.
let distinct_live_set (live_set: seq U64.t) : prop =
  forall (i j: nat). i < Seq.length live_set /\ j < Seq.length live_set /\ i <> j ==>
    Seq.index live_set i <> Seq.index live_set j

val promote_all_preserves_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    distinct_live_set live_set)
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fields_match_minor minor res.major_final res.fwd_map
                                       live_set (Seq.length live_set)))
