module GC.Gen.SingleChunkInvariant

open FStar.Seq
module U64 = FStar.UInt64
module Fields = GC.Spec.Fields
module Classical = FStar.Classical
module Math = FStar.Math.Lemmas

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
module GenInv = GC.Gen.HeapInvariant
module HeapGraph = GC.Spec.HeapGraph

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 1"
let aligned_gt_ge_plus_mword (x z: nat)
  : Lemma
    (requires x > z /\ x % U64.v mword == 0 /\ z % U64.v mword == 0)
    (ensures x >= z + U64.v mword)
  =
  if x < z + U64.v mword then begin
    assert (x - z > 0);
    assert (x - z < U64.v mword);
    Math.lemma_mod_sub_distr x z (U64.v mword);
    assert ((x - z) % U64.v mword == 0);
    Math.small_mod (x - z) (U64.v mword);
    assert False
  end

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

let dense_object_header_in_single_chunk (g: heap) (obj: obj_addr)
  : Lemma
      (requires Seq.mem obj (objects zero_addr g))
      (ensures
        U64.v (hd_address obj) >= U64.v zero_addr /\
        U64.v (hd_address obj) + U64.v mword <= heap_size)
  =
  Fields.objects_addresses_gt_start zero_addr g obj;
  aligned_gt_ge_plus_mword (U64.v obj) (U64.v zero_addr);
  hd_address_spec obj;
  hd_address_bounds obj;
  assert (U64.v obj >= U64.v zero_addr + U64.v mword);
  assert (U64.v (hd_address obj) >= U64.v zero_addr);
  assert (U64.v (hd_address obj) + U64.v mword <= heap_size)

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

let dense_chain_nonblue_avoids_of_chain_objects_blue (g: heap) (fp: U64.t)
  : Lemma
      (requires chain_objects_blue g fp)
      (ensures dense_chain_nonblue_avoids g fp Alloc.alloc_search_fuel)
  =
  reveal_opaque (`%chain_objects_blue) chain_objects_blue

let dense_chain_nonblue_avoids_tail (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma
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
  =
  let aux (obj: obj_addr)
    : Lemma
      (requires Seq.mem obj (objects zero_addr g) /\ is_blue obj g = false)
      (ensures
        AllocLemmas.chain_avoids
          g (read_word g (fp <: obj_addr)) obj (fuel - 1) = true)
    =
    AllocLemmas.chain_avoids_tail g fp obj fuel
  in
  Classical.forall_intro (Classical.move_requires aux)

let dense_free_list_node_blue_from_avoids (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma
      (requires
        dense_chain_nonblue_avoids g fp fuel /\
        fuel > 0 /\
        U64.v fp >= U64.v mword /\
        U64.v fp < heap_size /\
        U64.v fp % U64.v mword == 0 /\
        Seq.mem fp (objects zero_addr g))
      (ensures is_blue (fp <: obj_addr) g)
  =
  let obj : obj_addr = fp in
  if ~(is_blue obj g) then begin
    assert (AllocLemmas.chain_avoids g fp obj fuel = true);
    AllocLemmas.chain_avoids_head_ne g fp obj fuel;
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

let dense_free_list_link_pointer_or_zero_from_avoids (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma
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
        HeapGraph.is_pointer_field (read_word g (fp <: obj_addr)))
  =
  let obj : obj_addr = fp in
  AllocLemmas.fl_valid_elim g fp fuel;
  dense_free_list_node_fits_link g fp fuel;
  dense_free_list_node_blue_from_avoids g fp fuel;
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

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 1"
let rec major_fl_valid_single_chunk_from_dense (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma
      (requires
        well_formed_heap g /\
        FreeListShape.fp_pointer_or_zero fp /\
        FreeListShape.blue_link_fields_valid g /\
        dense_chain_nonblue_avoids g fp fuel /\
        AllocLemmas.fl_valid g fp fuel)
      (ensures
        SpecMajorAlloc.major_fl_valid
          (MH.single_chunk_major_heap g) fp fuel)
      (decreases fuel)
  =
  if fuel = 0 then ()
  else if fp = 0UL then ()
  else begin
    assert (fuel > 0);
    let fuel' : f:nat{f < fuel} = fuel - 1 in
    assert (HeapGraph.is_pointer_field fp);
    assert (U64.v fp >= U64.v mword);
    assert (U64.v fp < heap_size);
    assert (U64.v fp % U64.v mword == 0);
    let obj : obj_addr = fp in
    AllocLemmas.fl_valid_elim g fp fuel;
    dense_free_list_node_fits_link g fp fuel;
    let next = read_word g obj in
    dense_free_list_link_pointer_or_zero_from_avoids g fp fuel;
    assert (FreeListShape.fp_pointer_or_zero next);
    dense_chain_nonblue_avoids_tail g fp fuel;
    major_fl_valid_single_chunk_from_dense g next fuel';
    MH.single_chunk_major_pointer_compat g fp;
    MH.single_chunk_major_objects_compat g;
    wosize_of_object_spec obj g;
    hd_address_spec obj;
    hd_address_bounds obj;
    assert (U64.v obj >= U64.v zero_addr + U64.v mword);
    assert (U64.v (hd_address obj) >= U64.v zero_addr);
    assert (U64.v (hd_address obj) + U64.v mword <= heap_size);
    MH.single_chunk_read_word_compat g (hd_address obj);
    MH.single_chunk_read_word_compat g obj;
    assert (Seq.mem obj (MH.major_objects (MH.single_chunk_major_heap g)));
    assert (MH.is_major_pointer (MH.single_chunk_major_heap g) fp);
    assert (SpecMajorAlloc.major_fl_valid
              (MH.single_chunk_major_heap g) next fuel');
    assert (SpecMajorAlloc.major_fl_valid
              (MH.single_chunk_major_heap g) fp fuel)
  end

let rec major_fl_above_zero_single_chunk_from_dense (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma
      (requires
        well_formed_heap g /\
        FreeListShape.fp_pointer_or_zero fp /\
        FreeListShape.blue_link_fields_valid g /\
        dense_chain_nonblue_avoids g fp fuel /\
        AllocLemmas.fl_valid g fp fuel)
      (ensures
        SpecMajorAlloc.major_fl_above_zero
          (MH.single_chunk_major_heap g) fp fuel)
      (decreases fuel)
  =
  if fuel = 0 then ()
  else if fp = 0UL then ()
  else begin
    assert (fuel > 0);
    let fuel' : f:nat{f < fuel} = fuel - 1 in
    assert (HeapGraph.is_pointer_field fp);
    assert (U64.v fp >= U64.v zero_addr + U64.v mword);
    assert (U64.v fp < heap_size);
    assert (U64.v fp % U64.v mword == 0);
    let obj : obj_addr = fp in
    AllocLemmas.fl_valid_elim g fp fuel;
    dense_free_list_node_fits_link g fp fuel;
    let next = read_word g obj in
    dense_free_list_link_pointer_or_zero_from_avoids g fp fuel;
    assert (FreeListShape.fp_pointer_or_zero next);
    dense_chain_nonblue_avoids_tail g fp fuel;
    major_fl_above_zero_single_chunk_from_dense g next fuel';
    MH.single_chunk_read_word_compat g obj;
    assert (SpecMajorAlloc.major_fl_above_zero
              (MH.single_chunk_major_heap g) next fuel');
    assert (SpecMajorAlloc.major_fl_above_zero
              (MH.single_chunk_major_heap g) fp fuel)
  end

let rec major_fl_blocks_fit_single_chunk_from_dense (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma
      (requires
        well_formed_heap g /\
        FreeListShape.fp_pointer_or_zero fp /\
        FreeListShape.blue_link_fields_valid g /\
        dense_chain_nonblue_avoids g fp fuel /\
        AllocLemmas.fl_valid g fp fuel)
      (ensures
        SpecMajorAlloc.major_fl_blocks_fit
          (MH.single_chunk_major_heap g) fp fuel)
      (decreases fuel)
  =
  if fuel = 0 then ()
  else if fp = 0UL then ()
  else begin
    assert (fuel > 0);
    let fuel' : f:nat{f < fuel} = fuel - 1 in
    assert (HeapGraph.is_pointer_field fp);
    assert (U64.v fp >= U64.v mword);
    assert (U64.v fp < heap_size);
    assert (U64.v fp % U64.v mword == 0);
    let obj : obj_addr = fp in
    let base = hd_address obj in
    AllocLemmas.fl_valid_elim g fp fuel;
    dense_free_list_node_fits_link g fp fuel;
    let next = read_word g obj in
    dense_free_list_link_pointer_or_zero_from_avoids g fp fuel;
    assert (FreeListShape.fp_pointer_or_zero next);
    dense_chain_nonblue_avoids_tail g fp fuel;
    major_fl_blocks_fit_single_chunk_from_dense g next fuel';
    hd_address_spec obj;
    hd_address_bounds obj;
    assert (U64.v obj >= U64.v zero_addr + U64.v mword);
    assert (U64.v base >= U64.v zero_addr);
    assert (U64.v base + U64.v mword <= heap_size);
    MH.single_chunk_read_word_compat g base;
    MH.single_chunk_read_word_compat g obj;
    wosize_of_object_spec obj g;
    Fields.wf_object_size_bound g obj;
    assert (U64.v mword == 8);
    assert (U64.v base + 8 + U64.v (wosize_of_object obj g) * 8 <= heap_size);
    Math.distributivity_add_left 1 (U64.v (wosize_of_object obj g)) 8;
    assert ((1 + U64.v (wosize_of_object obj g)) * 8 ==
            8 + U64.v (wosize_of_object obj g) * 8);
    assert (MH.lookup_chunk_index (MH.single_chunk_major_heap g) base == Some 0);
    assert (0 < Seq.length (MH.single_chunk_major_heap g));
    assert (MH.word_in_chunk (Seq.index (MH.single_chunk_major_heap g) 0) base);
    assert (MH.chunk_end (Seq.index (MH.single_chunk_major_heap g) 0) == heap_size);
    assert (U64.v base + (1 + U64.v (wosize_of_object obj g)) * U64.v mword <= heap_size);
    assert (SpecMajorAlloc.major_fl_blocks_fit
              (MH.single_chunk_major_heap g) next fuel');
    assert (SpecMajorAlloc.major_fl_blocks_fit
              (MH.single_chunk_major_heap g) fp fuel)
  end

let rec major_fl_chain_terminates_single_chunk_from_dense (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma
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
      (decreases fuel)
  =
  if fp = 0UL then
    SpecMajorAlloc.major_fl_chain_terminates_null (MH.single_chunk_major_heap g) fuel
  else begin
    assert (HeapGraph.is_pointer_field fp);
    assert (U64.v fp >= U64.v mword);
    assert (U64.v fp < heap_size);
    assert (U64.v fp % U64.v mword == 0);
    if fuel = 0 then begin
      AllocLemmas.fl_chain_terminates_valid_zero g fp;
      assert False
    end else begin
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      let obj : obj_addr = fp in
      AllocLemmas.fl_valid_elim g fp fuel;
      dense_free_list_node_fits_link g fp fuel;
      AllocLemmas.fl_chain_terminates_elim g fp fuel;
      let next = read_word g obj in
      dense_free_list_link_pointer_or_zero_from_avoids g fp fuel;
      assert (FreeListShape.fp_pointer_or_zero next);
      dense_chain_nonblue_avoids_tail g fp fuel;
      major_fl_chain_terminates_single_chunk_from_dense g next fuel';
      MH.single_chunk_read_word_compat g obj;
      assert (SpecMajorAlloc.major_fl_chain_terminates
                (MH.single_chunk_major_heap g) next fuel' = true);
      SpecMajorAlloc.major_fl_chain_terminates_step
        (MH.single_chunk_major_heap g) fp fuel
    end
  end

let rec major_fl_chain_avoids_single_chunk_from_dense
  (g: heap) (fp excl: U64.t) (fuel: nat)
  : Lemma
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
      (decreases fuel)
  =
  if fp = 0UL then
    SpecMajorAlloc.major_fl_chain_avoids_null (MH.single_chunk_major_heap g) excl fuel
  else if fuel = 0 then ()
  else begin
    let fuel' : f:nat{f < fuel} = fuel - 1 in
    assert (HeapGraph.is_pointer_field fp);
    assert (U64.v fp >= U64.v mword);
    assert (U64.v fp < heap_size);
    assert (U64.v fp % U64.v mword == 0);
    let obj : obj_addr = fp in
    AllocLemmas.chain_avoids_head_ne g fp excl fuel;
    AllocLemmas.fl_valid_elim g fp fuel;
    dense_free_list_node_fits_link g fp fuel;
    AllocLemmas.chain_avoids_tail g fp excl fuel;
    let next = read_word g obj in
    dense_free_list_link_pointer_or_zero_from_avoids g fp fuel;
    assert (FreeListShape.fp_pointer_or_zero next);
    dense_chain_nonblue_avoids_tail g fp fuel;
    major_fl_chain_avoids_single_chunk_from_dense g next excl fuel';
    MH.single_chunk_read_word_compat g obj;
    assert (SpecMajorAlloc.major_fl_chain_avoids
              (MH.single_chunk_major_heap g) next excl fuel' = true);
    SpecMajorAlloc.major_fl_chain_avoids_step
      (MH.single_chunk_major_heap g) fp excl fuel
  end

let chunked_chain_objects_blue_single_chunk_from_dense (g: heap) (fp: U64.t)
  : Lemma
      (requires
        well_formed_heap g /\
        FreeListShape.fp_pointer_or_zero fp /\
        FreeListShape.blue_link_fields_valid g /\
        chain_objects_blue g fp /\
        AllocLemmas.fl_valid g fp Alloc.alloc_search_fuel)
      (ensures
        GenInv.chunked_chain_objects_blue
          (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel)
  =
  dense_chain_nonblue_avoids_of_chain_objects_blue g fp;
  let aux (obj: obj_addr)
    : Lemma
      (requires
        Seq.mem obj (MH.major_objects (MH.single_chunk_major_heap g)) /\
        ~(GenInv.chunked_is_blue (MH.single_chunk_major_heap g) obj))
      (ensures
        SpecMajorAlloc.major_fl_chain_avoids
          (MH.single_chunk_major_heap g) fp obj Alloc.alloc_search_fuel = true)
    =
    MH.single_chunk_major_objects_compat g;
    assert (Seq.mem obj (objects zero_addr g));
    dense_object_header_in_single_chunk g obj;
    MH.single_chunk_read_word_compat g (hd_address obj);
    color_of_object_spec obj g;
    is_blue_iff obj g;
    GenInv.chunked_is_blue_header
      (MH.single_chunk_major_heap g) obj (read_word g (hd_address obj));
    assert (is_blue obj g = false);
    reveal_opaque (`%chain_objects_blue) chain_objects_blue;
    assert (AllocLemmas.chain_avoids g fp obj Alloc.alloc_search_fuel = true);
    major_fl_chain_avoids_single_chunk_from_dense g fp obj Alloc.alloc_search_fuel
  in
  Classical.forall_intro (Classical.move_requires aux);
  GenInv.chunked_chain_objects_blue_intro
    (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel

let chunked_major_alloc_shape_single_chunk_from_dense (g: heap) (fp: U64.t)
  : Lemma
      (requires GenInv.major_heap_shape g fp)
      (ensures
        GenInv.chunked_major_alloc_shape
          (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel = true /\
        GenInv.chunked_chain_objects_blue
          (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel)
  =
  GenInv.major_heap_shape_elim g fp;
  dense_chain_nonblue_avoids_of_chain_objects_blue g fp;
  major_fl_valid_single_chunk_from_dense g fp Alloc.alloc_search_fuel;
  major_fl_above_zero_single_chunk_from_dense g fp Alloc.alloc_search_fuel;
  major_fl_blocks_fit_single_chunk_from_dense g fp Alloc.alloc_search_fuel;
  major_fl_chain_terminates_single_chunk_from_dense g fp Alloc.alloc_search_fuel;
  chunked_chain_objects_blue_single_chunk_from_dense g fp;
  MH.single_chunk_major_heap_wf g;
  GenInv.chunked_major_alloc_shape_intro
    (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel;
  assert (SpecMajorAlloc.major_fl_chain_terminates
            (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel = true)
#pop-options
