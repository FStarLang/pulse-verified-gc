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

/// well_formed_heap_part2 implies blue_fields_closed
val wfh_part2_implies_blue_fields_closed (g: heap)
  : Lemma (requires well_formed_heap_part1 g /\ well_formed_heap_part2 g)
          (ensures blue_fields_closed g)

/// alloc_spec preserves blue_fields_closed
val alloc_spec_preserves_blue_fields_closed
  (g: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates g fp (heap_size / U64.v mword) /\
                    blue_fields_closed g /\
                    wz >= 1 /\
                    (GC.Spec.Allocator.alloc_spec g fp wz).obj_out <> 0UL /\
                    chain_objects_blue g fp)
          (ensures blue_fields_closed (GC.Spec.Allocator.alloc_spec g fp wz).heap_out)
