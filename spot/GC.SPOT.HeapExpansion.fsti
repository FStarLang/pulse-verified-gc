module GC.SPOT.HeapExpansion

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object

module MH = GC.Spec.MajorHeap
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module CG = GC.Gen.CombinedGraph

val spot_expand_on_oom_pre
  : mh:MH.major_heap -> fp:U64.t -> requested_wz:nat -> fuel:nat ->
    fresh:MH.heap_chunk -> old_addr:hp_addr -> old_value:U64.t -> Tot prop

val spot_expand_on_oom_allocates_fresh_and_preserves_old_read
  : mh:MH.major_heap -> fp:U64.t -> requested_wz:nat -> fuel:nat ->
    fresh:MH.heap_chunk -> old_addr:hp_addr -> old_value:U64.t ->
    Lemma
      (requires spot_expand_on_oom_pre
        mh fp requested_wz fuel fresh old_addr old_value)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_expand_on_oom
             mh fp requested_wz fuel fresh in
         r.major_obj_out == SpecMajorAlloc.fresh_chunk_object fresh /\
         r.major_obj_out <> 0UL /\
         MH.read_word_in_major r.major_alloc_out old_addr == Some old_value /\
         ~(FStar.Seq.mem
            (SpecMajorAlloc.fresh_chunk_object fresh)
            (MH.major_objects mh))))

val spot_ensure_capacity_pre
  : mh:MH.major_heap -> fp:obj_addr -> fuel:nat -> needed:nat ->
    fresh:MH.heap_chunk -> old_addr:hp_addr -> old_value:U64.t -> Tot prop

val spot_ensure_capacity_expands_and_preserves_old_read
  : mh:MH.major_heap -> fp:obj_addr -> fuel:nat -> needed:nat ->
    fresh:MH.heap_chunk -> old_addr:hp_addr -> old_value:U64.t ->
    Lemma
      (requires spot_ensure_capacity_pre
        mh fp fuel needed fresh old_addr old_value)
      (ensures
        (let r =
           SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh in
         SpecMajorAlloc.major_fl_capacity
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out >= needed /\
         SpecMajorAlloc.major_fl_valid
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_above_zero
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
         MH.well_formed_major_heap r.capacity_major_out /\
         MH.read_word_in_major r.capacity_major_out old_addr == Some old_value))

val spot_chunked_classify_minor_field
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap -> v:U64.t ->
    GTot (option CG.combined_vertex)

val spot_chunked_classify_major_field
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap -> v:U64.t ->
    GTot (option CG.combined_vertex)

val spot_major_member_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t -> v:obj_addr ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
               ~(MH.pointer_in_chunk fresh v))
      (ensures
        Seq.mem v
         (MH.major_objects
           (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out) ==
        Seq.mem v (MH.major_objects mh))

val spot_chunked_classify_minor_field_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state ->
    mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t -> v:U64.t ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
               ~(MH.pointer_in_chunk fresh v))
      (ensures
        spot_chunked_classify_minor_field ms
         (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out v ==
        spot_chunked_classify_minor_field ms mh v)

val spot_chunked_classify_major_field_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state ->
    mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t -> v:U64.t ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
               ~(MH.pointer_in_chunk fresh v))
      (ensures
        spot_chunked_classify_major_field ms
         (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out v ==
        spot_chunked_classify_major_field ms mh v)

val spot_chunked_header_of_object_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t -> obj:obj_addr ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_header_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_header_of_object mh obj)

val spot_chunked_wosize_of_object_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t -> obj:obj_addr ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_wosize_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_wosize_of_object mh obj)

val spot_chunked_major_field_edges
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    src:obj_addr -> wz:nat -> i:nat -> GTot (Seq.seq CG.combined_edge)

val spot_chunked_major_field_edges_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state ->
    mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    src:obj_addr -> wz:nat -> i:nat ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_major_field_expansion_safe mh fresh src wz i)
      (ensures
        spot_chunked_major_field_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out src wz i ==
        spot_chunked_major_field_edges ms mh src wz i)

val spot_chunked_all_major_field_edges
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    objs:Seq.seq obj_addr -> wz_of:(obj_addr -> GTot nat) -> idx:nat ->
    GTot (Seq.seq CG.combined_edge)

val spot_chunked_all_major_field_edges_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state ->
    mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    objs:Seq.seq obj_addr -> wz_of:(obj_addr -> GTot nat) -> idx:nat ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_field_expansion_safe
                  mh fresh objs wz_of idx)
      (ensures
        spot_chunked_all_major_field_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out objs wz_of idx ==
        spot_chunked_all_major_field_edges ms mh objs wz_of idx)
