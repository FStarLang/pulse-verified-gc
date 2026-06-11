module GC.Gen.PromoteUpdate.BlueProm

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
module FreeListShape = GC.Gen.FreeListShape

val promote_object_preserves_bfc
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      blue_fields_closed major /\
      chain_objects_blue major fp /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      blue_fields_closed (promote_object minor major obj fp wosize).major_out)

/// promote_object preserves chain_objects_blue
val promote_object_preserves_chain_objects_blue
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      chain_objects_blue (promote_object minor major obj fp wosize).major_out
                         (promote_object minor major obj fp wosize).fp_out)

val promote_object_preserves_free_list_shape
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      FreeListShape.fp_pointer_or_zero fp /\
      FreeListShape.blue_link_fields_valid major /\
      chain_objects_blue major fp /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      FreeListShape.fp_pointer_or_zero
        (promote_object minor major obj fp wosize).fp_out /\
      FreeListShape.blue_link_fields_valid
        (promote_object minor major obj fp wosize).major_out)

/// After promote_all_spec, blue objects' pointer fields still target valid objects.
val promote_all_preserves_blue_fields_closed
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp)
          (ensures blue_fields_closed (promote_all_spec minor major fp live_set).major_final)

/// Unfold: mc_major of all-objects collection
val minor_collect_all_spec_unfold (minor: minor_state) (major: heap)
                                   (fp: U64.t) (roots: seq U64.t)
  : Lemma (let all_objs = minor_objects minor in
           let prom_res = promote_all_spec minor major fp all_objs in
           (minor_collect_all_spec minor major fp roots).mc_major ==
             update_major_pointers prom_res.major_final prom_res.fwd_map /\
           (minor_collect_all_spec minor major fp roots).mc_fwd == prom_res.fwd_map /\
           (minor_collect_all_spec minor major fp roots).mc_fp == prom_res.fp_final)
