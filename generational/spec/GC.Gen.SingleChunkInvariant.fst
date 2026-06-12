module GC.Gen.SingleChunkInvariant

open FStar.Seq
module U64 = FStar.UInt64
module Fields = GC.Spec.Fields

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module Alloc = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module FreeListShape = GC.Gen.FreeListShape
module SpecMajorAlloc = GC.Spec.MajorAllocator
module HeapGraph = GC.Spec.HeapGraph

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 1"
let alloc_search_fuel_positive ()
  : Lemma (ensures Alloc.alloc_search_fuel > 0)
  =
  assert (U64.v mword == 8);
  assert (heap_size >= 16);
  assert (heap_size / U64.v mword > 0)

let dense_free_list_node_fits_link (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma
      (requires
        well_formed_heap g /\
        fuel > 0 /\
        U64.v fp >= U64.v mword /\
        U64.v fp < heap_size /\
        U64.v fp % U64.v mword == 0 /\
        AllocLemmas.fl_valid g fp fuel)
      (ensures
        U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size)
  =
  let obj : obj_addr = fp in
  AllocLemmas.fl_valid_elim g fp fuel;
  Fields.wf_object_size_bound g obj;
  assert (U64.v (wosize_of_object obj g) >= 1);
  assert (U64.v (hd_address obj) + 8 +
          U64.v (wosize_of_object obj g) * 8 <= heap_size);
  assert (U64.v (hd_address obj) + 16 <= heap_size)

let dense_free_list_node_blue (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        U64.v fp >= U64.v mword /\
        U64.v fp < heap_size /\
        U64.v fp % U64.v mword == 0 /\
        Seq.mem fp (objects zero_addr g) /\
        chain_objects_blue g fp)
      (ensures is_blue (fp <: obj_addr) g)
  =
  let obj : obj_addr = fp in
  if ~(is_blue obj g) then begin
    reveal_opaque (`%chain_objects_blue) chain_objects_blue;
    alloc_search_fuel_positive ();
    assert (AllocLemmas.chain_avoids g fp obj Alloc.alloc_search_fuel = true);
    AllocLemmas.chain_avoids_head_ne g fp obj Alloc.alloc_search_fuel;
    assert (fp == obj);
    assert False
  end

let dense_free_list_link_pointer_or_zero (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma
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
        HeapGraph.is_pointer_field (read_word g (fp <: obj_addr)))
  =
  let obj : obj_addr = fp in
  AllocLemmas.fl_valid_elim g fp fuel;
  dense_free_list_node_fits_link g fp fuel;
  dense_free_list_node_blue g fp fuel;
  FreeListShape.blue_link_fields_valid_elim g obj

let major_fl_head_wosize_single_chunk_from_dense (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma
      (requires
        well_formed_heap g /\
        FreeListShape.fp_pointer_or_zero fp /\
        AllocLemmas.fl_valid g fp fuel /\
        fuel > 0)
      (ensures
        SpecMajorAlloc.major_fl_head_wosize
          (MH.single_chunk_major_heap g) fp ==
        (if fp = 0UL then 0
         else if HeapGraph.is_pointer_field fp
         then U64.v (wosize_of_object (fp <: obj_addr) g)
         else 0))
  =
  if fp = 0UL then ()
  else begin
    assert (HeapGraph.is_pointer_field fp);
    let obj : obj_addr = fp in
    AllocLemmas.fl_valid_elim g fp fuel;
    wosize_of_object_spec obj g;
    hd_address_spec obj;
    hd_address_bounds obj;
    assert (U64.v obj >= U64.v zero_addr + U64.v mword);
    assert (U64.v (hd_address obj) >= U64.v zero_addr);
    assert (U64.v (hd_address obj) + U64.v mword <= heap_size);
    MH.single_chunk_read_word_compat g (hd_address obj);
    assert (SpecMajorAlloc.major_fl_head_wosize
              (MH.single_chunk_major_heap g) fp ==
            U64.v (wosize_of_object obj g))
  end
#pop-options
