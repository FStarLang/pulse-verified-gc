module GC.Test.Bridge

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas
open GC.Spec.Mark
open GC.Spec.SweepInv
open GC.Spec.HeapModel
open GC.Spec.Graph

/// Reading any word from a zeroed heap gives 0UL.
val zeroed_heap_read_word (addr: hp_addr)
  : Lemma (read_word (Seq.create heap_size 0uy) addr == 0UL)

/// After init_heap_spec on a zeroed heap, objects 0UL g' == [mword].
val init_objects_eq (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', fp) = init_heap_spec g in
                    fp == mword /\
                    objects 0UL g' == Seq.cons (mword <: obj_addr) Seq.empty))

/// well_formed_heap holds after init_heap_spec on a zeroed heap.
val init_wf (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in well_formed_heap g'))

/// fl_valid holds after init_heap_spec on a zeroed heap.
val init_fl_valid (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', fp) = init_heap_spec g in
                    fl_valid g' fp (heap_size / FStar.UInt64.v mword)))

/// no_black_objects holds after init_heap_spec on a zeroed heap.
val init_no_black (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in no_black_objects g'))

/// no_gray_objects holds after init_heap_spec on a zeroed heap.
val init_no_gray (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in no_gray_objects g'))

/// no_pointer_to_blue holds after init_heap_spec on a zeroed heap.
val init_no_pointer_to_blue (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in no_pointer_to_blue g'))

/// objects list is non-empty after init_heap_spec on a zeroed heap.
val init_objects_nonempty (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in
                    Seq.length (objects 0UL g') > 0))

/// graph_wf holds for the init heap (no edges → vacuously well-formed).
val init_graph_wf (g: heap)
  : Lemma (requires g == Seq.create heap_size 0uy /\ heap_size >= 16)
          (ensures (let (g', _) = init_heap_spec g in
                    graph_wf (create_graph g')))
