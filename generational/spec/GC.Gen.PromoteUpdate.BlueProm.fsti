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
module FLs = GC.Spec.FreeLists

/// promote_object preserves chain_objects_blue
val promote_object_preserves_chain_objects_blue
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: FLs.fl_state)
  (wosize: nat{wosize > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      FLs.fls_valid major fp /\
      FLs.fls_terminates major fp /\
      chain_objects_blue major fp /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      chain_objects_blue (promote_object minor major obj fp wosize).major_out
                         (promote_object minor major obj fp wosize).fp_out)

val promote_object_preserves_free_list_shape
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: FLs.fl_state)
  (wosize: nat{wosize > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      FLs.fls_valid major fp /\
      FLs.fls_terminates major fp /\
      FreeListShape.fls_pointer_or_zero fp /\
      FreeListShape.blue_link_fields_valid major /\
      chain_objects_blue major fp /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      FreeListShape.fls_pointer_or_zero
        (promote_object minor major obj fp wosize).fp_out /\
      FreeListShape.blue_link_fields_valid
        (promote_object minor major obj fp wosize).major_out)
