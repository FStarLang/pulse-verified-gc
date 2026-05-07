/// ---------------------------------------------------------------------------
/// GC.Gen.Cheney.Dense — Density preservation through Cheney promotion
/// ---------------------------------------------------------------------------
///
/// Proves that promote_object (= alloc_spec + copy_fields) preserves
/// heap_objects_dense. This is used by cheney_promote_preserves_dense
/// in GC.Gen.Cheney.fst.

module GC.Gen.Cheney.Dense

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// alloc_spec preserves heap_objects_dense under well_formed_heap_part1.
val alloc_spec_preserves_dense_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    heap_objects_dense g /\
                    AllocLemmas.fl_valid g fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates g fp (heap_size / U64.v mword))
          (ensures (let r = GC.Spec.Allocator.alloc_spec g fp requested_wz in
                    heap_objects_dense r.heap_out))

/// promote_object preserves heap_objects_dense.
val promote_object_preserves_dense
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_object minor major obj fp wz in
                    heap_objects_dense res.major_out))
