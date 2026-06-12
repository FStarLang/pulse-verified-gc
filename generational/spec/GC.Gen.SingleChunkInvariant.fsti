module GC.Gen.SingleChunkInvariant

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module Alloc = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module FreeListShape = GC.Gen.FreeListShape
module SpecMajorAlloc = GC.Spec.MajorAllocator
module GenInv = GC.Gen.HeapInvariant
module Mark = GC.Spec.Mark
module CG = GC.Gen.CombinedGraph

let dense_chain_nonblue_avoids (g: heap) (fp: U64.t) (fuel: nat) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (objects zero_addr g) /\
    is_blue obj g = false ==>
    AllocLemmas.chain_avoids g fp obj fuel = true

val alloc_search_fuel_positive
  : unit -> Lemma (ensures Alloc.alloc_search_fuel > 0)

val dense_free_list_node_fits_link
  : g:heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires
        well_formed_heap g /\
        fuel > 0 /\
        U64.v fp >= U64.v mword /\
        U64.v fp < heap_size /\
        U64.v fp % U64.v mword == 0 /\
        AllocLemmas.fl_valid g fp fuel)
      (ensures
        U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size)

val dense_object_header_in_single_chunk
  : g:heap -> obj:obj_addr ->
    Lemma
      (requires Seq.mem obj (objects zero_addr g))
      (ensures
        U64.v (hd_address obj) >= U64.v zero_addr /\
        U64.v (hd_address obj) + U64.v mword <= heap_size)

val dense_free_list_node_blue
  : g:heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires
        fuel > 0 /\
        U64.v fp >= U64.v mword /\
        U64.v fp < heap_size /\
        U64.v fp % U64.v mword == 0 /\
        Seq.mem fp (objects zero_addr g) /\
        chain_objects_blue g fp)
      (ensures is_blue (fp <: obj_addr) g)

val dense_chain_nonblue_avoids_of_chain_objects_blue
  : g:heap -> fp:U64.t ->
    Lemma
      (requires chain_objects_blue g fp)
      (ensures dense_chain_nonblue_avoids g fp Alloc.alloc_search_fuel)

val dense_chain_nonblue_avoids_tail
  : g:heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires
        dense_chain_nonblue_avoids g fp fuel /\
        fuel > 0 /\
        U64.v fp >= U64.v mword /\
        U64.v fp < heap_size /\
        U64.v fp % U64.v mword == 0 /\
        U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size)
      (ensures
        dense_chain_nonblue_avoids
          g (read_word g (fp <: obj_addr)) (fuel - 1))

val dense_free_list_node_blue_from_avoids
  : g:heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires
        dense_chain_nonblue_avoids g fp fuel /\
        fuel > 0 /\
        U64.v fp >= U64.v mword /\
        U64.v fp < heap_size /\
        U64.v fp % U64.v mword == 0 /\
        Seq.mem fp (objects zero_addr g))
      (ensures is_blue (fp <: obj_addr) g)

val dense_free_list_link_pointer_or_zero
  : g:heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires
        well_formed_heap g /\
        FreeListShape.blue_link_fields_valid g /\
        chain_objects_blue g fp /\
        fuel > 0 /\
        U64.v fp >= U64.v mword /\
        U64.v fp < heap_size /\
        U64.v fp % U64.v mword == 0 /\
        AllocLemmas.fl_valid g fp fuel)
      (ensures
        read_word g (fp <: obj_addr) = 0UL \/
        GC.Spec.HeapGraph.is_pointer_field (read_word g (fp <: obj_addr)))

val dense_free_list_link_pointer_or_zero_from_avoids
  : g:heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires
        well_formed_heap g /\
        FreeListShape.blue_link_fields_valid g /\
        dense_chain_nonblue_avoids g fp fuel /\
        fuel > 0 /\
        U64.v fp >= U64.v mword /\
        U64.v fp < heap_size /\
        U64.v fp % U64.v mword == 0 /\
        AllocLemmas.fl_valid g fp fuel)
      (ensures
        read_word g (fp <: obj_addr) = 0UL \/
        GC.Spec.HeapGraph.is_pointer_field (read_word g (fp <: obj_addr)))

val major_fl_head_wosize_single_chunk_from_dense
  : g:heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires
        well_formed_heap g /\
        FreeListShape.fp_pointer_or_zero fp /\
        AllocLemmas.fl_valid g fp fuel /\
        fuel > 0)
      (ensures
        SpecMajorAlloc.major_fl_head_wosize
          (MH.single_chunk_major_heap g) fp ==
        (if fp = 0UL then 0
         else if GC.Spec.HeapGraph.is_pointer_field fp
         then U64.v (wosize_of_object (fp <: obj_addr) g)
         else 0))

val major_fl_valid_single_chunk_from_dense
  : g:heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires
        well_formed_heap g /\
        FreeListShape.fp_pointer_or_zero fp /\
        FreeListShape.blue_link_fields_valid g /\
        dense_chain_nonblue_avoids g fp fuel /\
        AllocLemmas.fl_valid g fp fuel)
      (ensures
        SpecMajorAlloc.major_fl_valid
          (MH.single_chunk_major_heap g) fp fuel)

val major_fl_above_zero_single_chunk_from_dense
  : g:heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires
        well_formed_heap g /\
        FreeListShape.fp_pointer_or_zero fp /\
        FreeListShape.blue_link_fields_valid g /\
        dense_chain_nonblue_avoids g fp fuel /\
        AllocLemmas.fl_valid g fp fuel)
      (ensures
        SpecMajorAlloc.major_fl_above_zero
          (MH.single_chunk_major_heap g) fp fuel)

val major_fl_blocks_fit_single_chunk_from_dense
  : g:heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires
        well_formed_heap g /\
        FreeListShape.fp_pointer_or_zero fp /\
        FreeListShape.blue_link_fields_valid g /\
        dense_chain_nonblue_avoids g fp fuel /\
        AllocLemmas.fl_valid g fp fuel)
      (ensures
        SpecMajorAlloc.major_fl_blocks_fit
          (MH.single_chunk_major_heap g) fp fuel)

val major_fl_chain_terminates_single_chunk_from_dense
  : g:heap -> fp:U64.t -> fuel:nat ->
    Lemma
      (requires
        well_formed_heap g /\
        FreeListShape.fp_pointer_or_zero fp /\
        FreeListShape.blue_link_fields_valid g /\
        dense_chain_nonblue_avoids g fp fuel /\
        AllocLemmas.fl_valid g fp fuel /\
        AllocLemmas.fl_chain_terminates g fp fuel = true)
      (ensures
        SpecMajorAlloc.major_fl_chain_terminates
          (MH.single_chunk_major_heap g) fp fuel = true)

val major_fl_chain_avoids_single_chunk_from_dense
  : g:heap -> fp:U64.t -> excl:U64.t -> fuel:nat ->
    Lemma
      (requires
        well_formed_heap g /\
        FreeListShape.fp_pointer_or_zero fp /\
        FreeListShape.blue_link_fields_valid g /\
        dense_chain_nonblue_avoids g fp fuel /\
        AllocLemmas.fl_valid g fp fuel /\
        AllocLemmas.chain_avoids g fp excl fuel = true)
      (ensures
        SpecMajorAlloc.major_fl_chain_avoids
          (MH.single_chunk_major_heap g) fp excl fuel = true)

val chunked_chain_objects_blue_single_chunk_from_dense
  : g:heap -> fp:U64.t ->
    Lemma
      (requires
        well_formed_heap g /\
        FreeListShape.fp_pointer_or_zero fp /\
        FreeListShape.blue_link_fields_valid g /\
        chain_objects_blue g fp /\
        AllocLemmas.fl_valid g fp Alloc.alloc_search_fuel)
      (ensures
        GenInv.chunked_chain_objects_blue
          (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel)

val chunked_major_alloc_shape_single_chunk_from_dense
  : g:heap -> fp:U64.t ->
    Lemma
      (requires GenInv.major_heap_shape g fp)
      (ensures
        GenInv.chunked_major_alloc_shape
          (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel = true /\
        GenInv.chunked_chain_objects_blue
          (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel)

val chunked_is_blue_single_chunk_compat
  : g:heap -> obj:obj_addr ->
    Lemma
      (requires Seq.mem obj (objects zero_addr g))
      (ensures
        GenInv.chunked_is_blue (MH.single_chunk_major_heap g) obj ==
        is_blue obj g)

val chunked_is_black_single_chunk_compat
  : g:heap -> obj:obj_addr ->
    Lemma
      (requires Seq.mem obj (objects zero_addr g))
      (ensures
        GenInv.chunked_is_black (MH.single_chunk_major_heap g) obj ==
        is_black obj g)

val chunked_no_black_objects_single_chunk_from_dense
  : g:heap ->
    Lemma
      (requires Mark.no_black_objects g)
      (ensures
        GenInv.chunked_no_black_objects (MH.single_chunk_major_heap g))

val chunked_minor_major_fields_no_blue_single_chunk_from_dense
  : minor:minor_state -> g:heap ->
    Lemma
      (requires GenInv.minor_major_fields_no_blue minor g)
      (ensures
        GenInv.chunked_minor_major_fields_no_blue
          minor (MH.single_chunk_major_heap g))

val chunked_wosize_single_chunk_compat
  : g:heap -> obj:obj_addr ->
    Lemma
      (requires Seq.mem obj (objects zero_addr g))
      (ensures
        CG.chunked_wosize_nat_of_object
          (MH.single_chunk_major_heap g) obj ==
        U64.v (wosize_of_object obj g))

val chunked_is_no_scan_single_chunk_compat
  : g:heap -> obj:obj_addr ->
    Lemma
      (requires Seq.mem obj (objects zero_addr g))
      (ensures
        CG.chunked_is_no_scan (MH.single_chunk_major_heap g) obj ==
        is_no_scan obj g)

val chunked_no_scan_invariant_single_chunk_from_dense
  : g:heap ->
    Lemma
      (requires no_scan_invariant g)
      (ensures
        GenInv.chunked_no_scan_invariant (MH.single_chunk_major_heap g))

val chunked_major_minor_fields_no_infix_targets_single_chunk_from_dense
  : minor:minor_state -> g:heap ->
    Lemma
      (requires GenInv.major_minor_fields_no_infix_targets minor g)
      (ensures
        GenInv.chunked_major_minor_fields_no_infix_targets
          minor (MH.single_chunk_major_heap g))

val chunked_no_pointer_to_blue_single_chunk_from_dense
  : g:heap ->
    Lemma
      (requires well_formed_heap g /\ Mark.no_pointer_to_blue g)
      (ensures
        GenInv.chunked_no_pointer_to_blue (MH.single_chunk_major_heap g))

val chunked_collection_heap_shape_single_chunk_from_dense
  : minor:minor_state -> g:heap -> fp:U64.t ->
    Lemma
      (requires GenInv.collection_heap_shape minor g fp)
      (ensures
        GenInv.chunked_collection_heap_shape
          minor (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel = true /\
        GenInv.chunked_chain_objects_blue
          (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel)
