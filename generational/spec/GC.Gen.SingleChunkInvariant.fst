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
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module Alloc = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module FreeListShape = GC.Gen.FreeListShape
module SpecMajorAlloc = GC.Spec.MajorAllocator
module GenInv = GC.Gen.HeapInvariant
module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module CG = GC.Gen.CombinedGraph
module NoBlueUtil = GC.Gen.NoBlueUtil

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

let chunked_is_blue_single_chunk_compat (g: heap) (obj: obj_addr)
  : Lemma
      (requires Seq.mem obj (objects zero_addr g))
      (ensures
        GenInv.chunked_is_blue (MH.single_chunk_major_heap g) obj ==
        is_blue obj g)
  =
  dense_object_header_in_single_chunk g obj;
  MH.single_chunk_read_word_compat g (hd_address obj);
  color_of_object_spec obj g;
  is_blue_iff obj g;
  GenInv.chunked_is_blue_header
    (MH.single_chunk_major_heap g) obj (read_word g (hd_address obj))

let chunked_is_black_single_chunk_compat (g: heap) (obj: obj_addr)
  : Lemma
      (requires Seq.mem obj (objects zero_addr g))
      (ensures
        GenInv.chunked_is_black (MH.single_chunk_major_heap g) obj ==
        is_black obj g)
  =
  dense_object_header_in_single_chunk g obj;
  MH.single_chunk_read_word_compat g (hd_address obj);
  color_of_object_spec obj g;
  is_black_iff obj g;
  GenInv.chunked_is_black_header
    (MH.single_chunk_major_heap g) obj (read_word g (hd_address obj))

let chunked_no_black_objects_single_chunk_from_dense (g: heap)
  : Lemma
      (requires Mark.no_black_objects g)
      (ensures
        GenInv.chunked_no_black_objects (MH.single_chunk_major_heap g))
  =
  let mh = MH.single_chunk_major_heap g in
  let aux (obj: obj_addr)
    : Lemma
      (requires Seq.mem obj (MH.major_objects mh))
      (ensures ~(GenInv.chunked_is_black mh obj))
    =
    MH.single_chunk_major_objects_compat g;
    assert (Seq.mem obj (objects zero_addr g));
    chunked_is_black_single_chunk_compat g obj;
    assert (~(is_black obj g))
  in
  Classical.forall_intro (Classical.move_requires aux);
  GenInv.chunked_no_black_objects_intro mh

let chunked_minor_major_fields_no_blue_single_chunk_from_dense
  (minor: minor_state) (g: heap)
  : Lemma
      (requires GenInv.minor_major_fields_no_blue minor g)
      (ensures
        GenInv.chunked_minor_major_fields_no_blue
          minor (MH.single_chunk_major_heap g))
  =
  let mh = MH.single_chunk_major_heap g in
  let aux (obj: U64.t) (j: nat)
    : Lemma
      (requires
        Seq.mem obj (minor_objects minor) /\
          j < minor_wosize minor obj)
        (ensures
          is_pointer_field (minor_read_field minor obj j) ==>
            Seq.mem ((minor_read_field minor obj j) <: obj_addr)
                    (MH.major_objects mh) /\
            ~(GenInv.chunked_is_blue mh
                ((minor_read_field minor obj j) <: obj_addr)))
    =
      let v = minor_read_field minor obj j in
      if is_pointer_field v then begin
        GenInv.minor_major_fields_no_blue_elim minor g obj j;
        assert (HeapGraph.is_pointer_field v);
        HeapGraph.is_pointer_field_is_obj_addr v;
        assert (U64.v v < heap_size);
        assert (U64.v v % U64.v mword = 0);
        let dst : obj_addr = v in
        MH.single_chunk_major_objects_compat g;
        assert (Seq.mem dst (objects zero_addr g));
        assert (Seq.mem dst (MH.major_objects mh));
        chunked_is_blue_single_chunk_compat g dst;
        assert (~(is_blue dst g))
      end
  in
  Classical.forall_intro_2 (Classical.move_requires_2 aux);
  GenInv.chunked_minor_major_fields_no_blue_intro minor mh

let chunked_wosize_single_chunk_compat (g: heap) (obj: obj_addr)
  : Lemma
      (requires Seq.mem obj (objects zero_addr g))
      (ensures
        CG.chunked_wosize_nat_of_object
          (MH.single_chunk_major_heap g) obj ==
        U64.v (wosize_of_object obj g))
  =
  dense_object_header_in_single_chunk g obj;
  MH.single_chunk_read_word_compat g (hd_address obj);
  wosize_of_object_spec obj g;
  CG.chunked_wosize_nat_header
    (MH.single_chunk_major_heap g) obj (read_word g (hd_address obj))

let chunked_is_no_scan_single_chunk_compat (g: heap) (obj: obj_addr)
  : Lemma
      (requires Seq.mem obj (objects zero_addr g))
      (ensures
        CG.chunked_is_no_scan (MH.single_chunk_major_heap g) obj ==
        is_no_scan obj g)
  =
  dense_object_header_in_single_chunk g obj;
  MH.single_chunk_read_word_compat g (hd_address obj);
  tag_of_object_spec obj g;
  is_no_scan_spec obj g;
  CG.chunked_is_no_scan_header
    (MH.single_chunk_major_heap g) obj (read_word g (hd_address obj))

let chunked_no_scan_invariant_single_chunk_from_dense (g: heap)
  : Lemma
      (requires no_scan_invariant g)
      (ensures
        GenInv.chunked_no_scan_invariant (MH.single_chunk_major_heap g))
  =
  let mh = MH.single_chunk_major_heap g in
  let aux (src: obj_addr) (idx: nat) (field_addr: hp_addr) (raw: U64.t)
    : Lemma
      (ensures
        Seq.mem src (MH.major_objects mh) /\
        CG.chunked_is_no_scan mh src /\
        ~(GenInv.chunked_is_blue mh src) /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw ==>
        ~(is_pointer_field raw))
    =
    if Seq.mem src (MH.major_objects mh) &&
       CG.chunked_is_no_scan mh src &&
       ~(GenInv.chunked_is_blue mh src) &&
       idx < CG.chunked_wosize_nat_of_object mh src &&
       CG.chunked_major_field_slot src idx == Some field_addr &&
       MH.read_word_in_major mh field_addr == Some raw
    then begin
      MH.single_chunk_major_objects_compat g;
      assert (Seq.mem src (objects zero_addr g));
      chunked_is_blue_single_chunk_compat g src;
      chunked_is_no_scan_single_chunk_compat g src;
      chunked_wosize_single_chunk_compat g src;
      CG.chunked_major_field_slot_elim src idx field_addr;
      assert (U64.v field_addr == U64.v src + idx * U64.v mword);
      objects_addresses_gt_start zero_addr g src;
      assert (U64.v src > U64.v zero_addr);
      assert (U64.v field_addr >= U64.v zero_addr);
      assert (U64.v field_addr + U64.v mword <= heap_size);
      MH.single_chunk_read_word_compat g field_addr;
      assert (raw == read_word g field_addr);
      assert (U64.v field_addr == U64.v (U64.uint_to_t (U64.v src + idx * U64.v mword)));
      assert (field_addr == U64.uint_to_t (U64.v src + idx * U64.v mword));
      assert (U64.v src + idx * 8 < heap_size);
      no_scan_invariant_elim g src idx;
      assert (~(is_pointer_field raw))
    end
  in
  Classical.forall_intro_4 aux;
  GenInv.chunked_no_scan_invariant_intro mh

let chunked_major_minor_fields_no_infix_targets_single_chunk_from_dense
  (minor: minor_state) (g: heap)
  : Lemma
      (requires GenInv.major_minor_fields_no_infix_targets minor g)
      (ensures
        GenInv.chunked_major_minor_fields_no_infix_targets
          minor (MH.single_chunk_major_heap g))
  =
  let mh = MH.single_chunk_major_heap g in
  let aux
    (obj: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t)
    : Lemma
      (ensures
        Seq.mem obj (MH.major_objects mh) /\
        ~(GenInv.chunked_is_blue mh obj) /\
        ~(CG.chunked_is_no_scan mh obj) /\
        j < CG.chunked_wosize_nat_of_object mh obj /\
        CG.chunked_major_field_slot obj j == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw /\
        is_minor_pointer (to_minor_offset raw) ==>
        ~(is_infix_in_minor minor (to_minor_offset raw)))
    =
    if Seq.mem obj (MH.major_objects mh) &&
       ~(GenInv.chunked_is_blue mh obj) &&
       ~(CG.chunked_is_no_scan mh obj) &&
       j < CG.chunked_wosize_nat_of_object mh obj &&
       CG.chunked_major_field_slot obj j == Some field_addr &&
       MH.read_word_in_major mh field_addr == Some raw &&
       is_minor_pointer (to_minor_offset raw)
    then begin
      MH.single_chunk_major_objects_compat g;
      assert (Seq.mem obj (objects zero_addr g));
      chunked_is_blue_single_chunk_compat g obj;
      chunked_is_no_scan_single_chunk_compat g obj;
      chunked_wosize_single_chunk_compat g obj;
      CG.chunked_major_field_slot_elim obj j field_addr;
      assert (U64.v field_addr == U64.v obj + j * U64.v mword);
      objects_addresses_gt_start zero_addr g obj;
      assert (U64.v obj > U64.v zero_addr);
      assert (U64.v field_addr >= U64.v zero_addr);
      assert (U64.v field_addr + U64.v mword <= heap_size);
      MH.single_chunk_read_word_compat g field_addr;
      assert (raw == read_word g field_addr);
      assert (U64.v field_addr == U64.v (U64.uint_to_t (U64.v obj + j * U64.v mword)));
      assert (field_addr == U64.uint_to_t (U64.v obj + j * U64.v mword));
      assert (U64.v obj + j * 8 + 8 <= heap_size);
      assert ((U64.v obj + j * 8) % 8 == 0);
      GenInv.major_minor_fields_no_infix_targets_elim minor g obj j
    end
  in
  Classical.forall_intro_4 aux;
  GenInv.chunked_major_minor_fields_no_infix_targets_intro minor mh
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 1"
let chunked_no_pointer_to_blue_single_chunk_from_dense (g: heap)
  : Lemma
      (requires well_formed_heap g /\ Mark.no_pointer_to_blue g)
      (ensures
        GenInv.chunked_no_pointer_to_blue (MH.single_chunk_major_heap g))
  =
  let mh = MH.single_chunk_major_heap g in
  let aux_src (src: obj_addr)
    : Lemma
      (ensures
        forall (dst: obj_addr) (idx: nat) (field_addr: hp_addr) (raw: U64.t).
          Seq.mem src (MH.major_objects mh) /\
          ~(GenInv.chunked_is_blue mh src) /\
          idx < CG.chunked_wosize_nat_of_object mh src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw /\
          Seq.mem dst (MH.major_objects mh) /\
          is_pointer_to raw dst ==>
          ~(GenInv.chunked_is_blue mh dst))
    =
    let aux_dst (dst: obj_addr)
      : Lemma
        (ensures
          forall (idx: nat) (field_addr: hp_addr) (raw: U64.t).
            Seq.mem src (MH.major_objects mh) /\
            ~(GenInv.chunked_is_blue mh src) /\
            idx < CG.chunked_wosize_nat_of_object mh src /\
            CG.chunked_major_field_slot src idx == Some field_addr /\
            MH.read_word_in_major mh field_addr == Some raw /\
            Seq.mem dst (MH.major_objects mh) /\
            is_pointer_to raw dst ==>
            ~(GenInv.chunked_is_blue mh dst))
      =
      let aux_idx (idx: nat)
        : Lemma
          (ensures
            forall (field_addr: hp_addr) (raw: U64.t).
              Seq.mem src (MH.major_objects mh) /\
              ~(GenInv.chunked_is_blue mh src) /\
              idx < CG.chunked_wosize_nat_of_object mh src /\
              CG.chunked_major_field_slot src idx == Some field_addr /\
              MH.read_word_in_major mh field_addr == Some raw /\
              Seq.mem dst (MH.major_objects mh) /\
              is_pointer_to raw dst ==>
              ~(GenInv.chunked_is_blue mh dst))
        =
        let aux_field (field_addr: hp_addr)
          : Lemma
            (ensures
              forall (raw: U64.t).
                Seq.mem src (MH.major_objects mh) /\
                ~(GenInv.chunked_is_blue mh src) /\
                idx < CG.chunked_wosize_nat_of_object mh src /\
                CG.chunked_major_field_slot src idx == Some field_addr /\
                MH.read_word_in_major mh field_addr == Some raw /\
                Seq.mem dst (MH.major_objects mh) /\
                is_pointer_to raw dst ==>
                ~(GenInv.chunked_is_blue mh dst))
          =
          let aux_raw (raw: U64.t)
            : Lemma
              (ensures
                Seq.mem src (MH.major_objects mh) /\
                ~(GenInv.chunked_is_blue mh src) /\
                idx < CG.chunked_wosize_nat_of_object mh src /\
                CG.chunked_major_field_slot src idx == Some field_addr /\
                MH.read_word_in_major mh field_addr == Some raw /\
                Seq.mem dst (MH.major_objects mh) /\
                is_pointer_to raw dst ==>
                ~(GenInv.chunked_is_blue mh dst))
            =
            if Seq.mem src (MH.major_objects mh) &&
               ~(GenInv.chunked_is_blue mh src) &&
               idx < CG.chunked_wosize_nat_of_object mh src &&
               CG.chunked_major_field_slot src idx == Some field_addr &&
               MH.read_word_in_major mh field_addr == Some raw &&
               Seq.mem dst (MH.major_objects mh) &&
               is_pointer_to raw dst
            then begin
              MH.single_chunk_major_objects_compat g;
              assert (Seq.mem src (objects zero_addr g));
              assert (Seq.mem dst (objects zero_addr g));
              chunked_is_blue_single_chunk_compat g src;
              chunked_is_blue_single_chunk_compat g dst;
              chunked_wosize_single_chunk_compat g src;
              CG.chunked_major_field_slot_elim src idx field_addr;
              assert (U64.v field_addr == U64.v src + idx * U64.v mword);
              objects_addresses_gt_start zero_addr g src;
              assert (U64.v src > U64.v zero_addr);
              assert (U64.v field_addr >= U64.v zero_addr);
              assert (U64.v field_addr + U64.v mword <= heap_size);
              MH.single_chunk_read_word_compat g field_addr;
              assert (raw == read_word g field_addr);
              assert (U64.v field_addr ==
                      U64.v (U64.uint_to_t (U64.v src + idx * U64.v mword)));
              assert (field_addr ==
                      U64.uint_to_t (U64.v src + idx * U64.v mword));
              assert (U64.v src + idx * U64.v mword + U64.v mword <= heap_size);
              assert ((U64.v src + idx * U64.v mword) % U64.v mword == 0);
              assert (is_pointer_to
                (read_word g (U64.uint_to_t (U64.v src + idx * U64.v mword)))
                dst);
              reveal_opaque (`%well_formed_heap) well_formed_heap;
              NoBlueUtil.field_pointer_no_blue_from_no_pointer_to_blue
                g src dst idx;
              assert (~(is_blue dst g));
              assert (~(GenInv.chunked_is_blue mh dst))
            end
          in
          FStar.Classical.forall_intro aux_raw
        in
        FStar.Classical.forall_intro aux_field
      in
      FStar.Classical.forall_intro aux_idx
    in
    FStar.Classical.forall_intro aux_dst
  in
  FStar.Classical.forall_intro aux_src;
  GenInv.chunked_no_pointer_to_blue_intro mh
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 0 --ifuel 0"
let chunked_collection_heap_shape_single_chunk_from_dense
  (minor: minor_state) (g: heap) (fp: U64.t)
  : Lemma
      (requires GenInv.collection_heap_shape minor g fp)
      (ensures
        GenInv.chunked_collection_heap_shape
          minor (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel = true /\
        GenInv.chunked_chain_objects_blue
          (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel)
  =
  let mh = MH.single_chunk_major_heap g in
  GenInv.collection_heap_shape_elim minor g fp;
  GenInv.major_heap_shape_elim g fp;
  chunked_major_alloc_shape_single_chunk_from_dense g fp;
  chunked_no_black_objects_single_chunk_from_dense g;
  chunked_no_scan_invariant_single_chunk_from_dense g;
  chunked_no_pointer_to_blue_single_chunk_from_dense g;
  chunked_minor_major_fields_no_blue_single_chunk_from_dense minor g;
  chunked_major_minor_fields_no_infix_targets_single_chunk_from_dense minor g;
  GenInv.chunked_collection_heap_shape_intro
    minor mh fp Alloc.alloc_search_fuel
#pop-options
