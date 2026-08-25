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

/// well_formed_heap_part2 implies blue_fields_closed
val wfh_part2_implies_blue_fields_closed (g: heap)
  : Lemma (requires well_formed_heap_part1 g /\ well_formed_heap_part2 g /\
                    blue_fields_non_infix g)
          (ensures blue_fields_closed g)

/// The converse: `blue_fields_closed` (raw) plus part 4 gives back the clause
/// `major_heap_shape` carries.  This is what makes `blue_fields_non_infix` free
/// to re-establish after a collection --- the Cheney machinery already proves
/// `blue_fields_closed` for the result.
val blue_fields_closed_implies_blue_fields_non_infix (g: heap)
  : Lemma (requires well_formed_heap_part1 g /\ well_formed_heap_part4 g /\
                    blue_fields_closed g)
          (ensures blue_fields_non_infix g)

/// alloc_spec preserves blue_fields_closed
val alloc_spec_preserves_blue_fields_closed
  (g: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words /\
                    blue_fields_closed g /\
                    wz >= 1 /\
                    (GC.Spec.Allocator.alloc_spec g fp wz).obj_out <> 0UL /\
                    chain_objects_blue g fp)
          (ensures blue_fields_closed (GC.Spec.Allocator.alloc_spec g fp wz).heap_out)

val alloc_spec_preserves_fp_pointer_or_zero
  (g: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words /\
                    FreeListShape.blue_link_fields_valid g /\
                    FreeListShape.fp_pointer_or_zero fp /\
                    wz >= 1 /\
                    (GC.Spec.Allocator.alloc_spec g fp wz).obj_out <> 0UL /\
                    chain_objects_blue g fp)
          (ensures FreeListShape.fp_pointer_or_zero
                     (GC.Spec.Allocator.alloc_spec g fp wz).fp_out)

val alloc_spec_preserves_blue_link_fields_valid
  (g: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words /\
                    FreeListShape.blue_link_fields_valid g /\
                    wz >= 1 /\
                    (GC.Spec.Allocator.alloc_spec g fp wz).obj_out <> 0UL /\
                    chain_objects_blue g fp)
          (ensures FreeListShape.blue_link_fields_valid
                     (GC.Spec.Allocator.alloc_spec g fp wz).heap_out)
