module GC.SPOT.HeapExpansion

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module CG = GC.Gen.CombinedGraph

let spot_expand_on_oom_pre
  (mh: MH.major_heap) (fp: U64.t) (requested_wz fuel: nat)
  (fresh: MH.heap_chunk) (old_addr: hp_addr) (old_value: U64.t) : Tot prop =
  MH.well_formed_major_heap mh /\
  MH.chunk_disjoint_from_all fresh mh /\
  (SpecMajorAlloc.major_alloc_spec_with_fuel
    mh fp requested_wz fuel).major_obj_out == 0UL /\
  U64.v fresh.base >= U64.v zero_addr /\
  requested_wz > 0 /\
  SpecMajorAlloc.fresh_chunk_wosize fresh >= requested_wz /\
  SpecAlloc.normalized_wosize requested_wz <=
    SpecMajorAlloc.fresh_chunk_wosize fresh /\
  ~(MH.chunk_contains_addr fresh old_addr) /\
  MH.read_word_in_major mh old_addr == Some old_value

let spot_expand_on_oom_allocates_fresh_and_preserves_old_read
  (mh: MH.major_heap) (fp: U64.t) (requested_wz fuel: nat)
  (fresh: MH.heap_chunk) (old_addr: hp_addr) (old_value: U64.t)
  : Lemma
      (requires spot_expand_on_oom_pre
        mh fp requested_wz fuel fresh old_addr old_value)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_expand_on_oom
             mh fp requested_wz fuel fresh in
         r.major_obj_out == SpecMajorAlloc.fresh_chunk_object fresh /\
         r.major_obj_out <> 0UL /\
         MH.read_word_in_major r.major_alloc_out old_addr == Some old_value /\
         ~(Seq.mem
            (SpecMajorAlloc.fresh_chunk_object fresh)
            (MH.major_objects mh))))
  =
  SpecMajorAlloc.major_alloc_expand_on_oom_returns_fresh
    mh fp requested_wz fuel fresh;
  SpecMajorAlloc.major_alloc_expand_on_oom_preserves_old_read
    mh fp requested_wz fuel fresh old_addr;
  SpecMajorAlloc.expand_major_heap_fresh_not_old mh fresh fp;
  SpecMajorAlloc.fresh_chunk_object_in_chunk fresh;
  assert (U64.v (SpecMajorAlloc.fresh_chunk_object fresh) >= U64.v fresh.base + U64.v mword);
  assert (U64.v (SpecMajorAlloc.fresh_chunk_object fresh) >= U64.v mword);
  assert (SpecMajorAlloc.fresh_chunk_object fresh <> 0UL)

let spot_ensure_capacity_pre
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk) (old_addr: hp_addr) (old_value: U64.t) : Tot prop =
  MH.well_formed_major_heap mh /\
  SpecMajorAlloc.major_fl_valid mh fp fuel /\
  SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
  SpecMajorAlloc.major_fl_capacity mh fp fuel < needed /\
  MH.chunk_disjoint_from_all fresh mh /\
  SpecMajorAlloc.fresh_chunk_wosize fresh +
    SpecMajorAlloc.major_fl_capacity mh fp fuel >= needed /\
  fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
  U64.v fresh.base >= U64.v zero_addr /\
  ~(MH.chunk_contains_addr fresh old_addr) /\
  MH.read_word_in_major mh old_addr == Some old_value

let spot_ensure_capacity_expands_and_preserves_old_read
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk) (old_addr: hp_addr) (old_value: U64.t)
  : Lemma
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
  =
  SpecMajorAlloc.ensure_major_capacity_has_capacity mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_capacity_fl_valid mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_capacity_fl_above_zero mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_capacity_wf mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_capacity_preserves_old_read mh fp fuel needed fresh old_addr

let spot_chunked_classify_minor_field (ms: minor_state) (mh: MH.major_heap) (v: U64.t)
  : GTot (option CG.combined_vertex)
  = CG.chunked_classify_minor_field ms mh v

let spot_chunked_classify_major_field (ms: minor_state) (mh: MH.major_heap) (v: U64.t)
  : GTot (option CG.combined_vertex)
  = CG.chunked_classify_major_field ms mh v

let spot_major_member_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (v: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.pointer_in_chunk fresh v))
      (ensures
        Seq.mem v
          (MH.major_objects
            (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out) ==
        Seq.mem v (MH.major_objects mh))
  = CG.chunked_major_member_preserved_by_expansion mh fresh fp v

let spot_chunked_classify_minor_field_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (v: U64.t)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.pointer_in_chunk fresh v))
      (ensures
        spot_chunked_classify_minor_field ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out v ==
        spot_chunked_classify_minor_field ms mh v)
  = CG.chunked_classify_minor_field_preserved_by_expansion ms mh fresh fp v

let spot_chunked_classify_major_field_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (v: U64.t)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.pointer_in_chunk fresh v))
      (ensures
        spot_chunked_classify_major_field ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out v ==
        spot_chunked_classify_major_field ms mh v)
  = CG.chunked_classify_major_field_preserved_by_expansion ms mh fresh fp v

let spot_chunked_major_field_edges
  (ms: minor_state) (mh: MH.major_heap) (src: obj_addr) (wz: nat) (i: nat)
  : GTot (Seq.seq CG.combined_edge)
  = CG.chunked_major_field_edges ms mh src wz i

let spot_chunked_major_field_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (src: obj_addr) (wz: nat) (i: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_major_field_expansion_safe mh fresh src wz i)
      (ensures
        spot_chunked_major_field_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out src wz i ==
        spot_chunked_major_field_edges ms mh src wz i)
  = CG.chunked_major_field_edges_preserved_by_expansion ms mh fresh fp src wz i
