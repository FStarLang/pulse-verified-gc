module GC.Gen.PromoteUpdate.BlueAlloc

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
module SAL = GC.Spec.Allocator.Lists

val alloc_spec_preserves_fp_pointer_or_zero
  (g: heap) (fp: FLs.fl_state) (wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    FLs.fls_valid g fp /\
                    FLs.fls_terminates g fp /\
                    FreeListShape.blue_link_fields_valid g /\
                    FreeListShape.fls_pointer_or_zero fp /\
                    wz >= 1 /\
                    (SAL.alloc_lists_spec g fp wz).obj_out <> 0UL /\
                    chain_objects_blue g fp)
          (ensures FreeListShape.fls_pointer_or_zero
                     (SAL.alloc_lists_spec g fp wz).fls_out)

/// The heads' shape is needed when the allocation moves a block to another
/// list: the block's link becomes that list's old head.
val alloc_spec_preserves_blue_link_fields_valid
  (g: heap) (fp: FLs.fl_state) (wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    FLs.fls_valid g fp /\
                    FLs.fls_terminates g fp /\
                    FreeListShape.blue_link_fields_valid g /\
                    FreeListShape.fls_pointer_or_zero fp /\
                    wz >= 1 /\
                    (SAL.alloc_lists_spec g fp wz).obj_out <> 0UL /\
                    chain_objects_blue g fp)
          (ensures FreeListShape.blue_link_fields_valid
                     (SAL.alloc_lists_spec g fp wz).heap_out)
