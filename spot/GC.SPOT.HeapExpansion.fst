module GC.SPOT.HeapExpansion

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module CG = GC.Gen.CombinedGraph
module GenInv = GC.Gen.HeapInvariant

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

let spot_expand_major_heap_head_wosize
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires U64.v fresh.base >= U64.v zero_addr)
      (ensures
        (let r = SpecMajorAlloc.expand_major_heap mh fresh fp in
         SpecMajorAlloc.major_fl_head_wosize r.major_out r.fp_out ==
         SpecMajorAlloc.fresh_chunk_wosize fresh))
  = SpecMajorAlloc.expand_major_heap_head_wosize mh fresh fp

let spot_head_preflight_alloc_no_oom
  (mh: MH.major_heap) (fp: U64.t) (requested_wz fuel: nat)
  : Lemma
      (requires fuel > 0 /\
                fp <> 0UL /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit mh fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  SpecAlloc.normalized_wosize requested_wz)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             mh fp requested_wz fuel in
         r.major_obj_out == fp /\ r.major_obj_out <> 0UL))
  = SpecMajorAlloc.major_alloc_spec_with_fuel_head_no_oom
      mh fp requested_wz fuel

let spot_ensure_head_capacity_preserves_shape_and_old_read
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk) (old_addr: hp_addr) (old_value: U64.t)
  : Lemma
      (requires MH.well_formed_major_heap mh /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit mh fp fuel /\
                MH.read_word_in_major mh old_addr == Some old_value /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
                 ~(MH.chunk_contains_addr fresh old_addr)))
      (ensures
        (let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             mh fp fuel needed fresh in
         SpecMajorAlloc.major_fl_head_wosize
           r.capacity_major_out r.capacity_fp_out >= needed /\
         SpecMajorAlloc.major_fl_valid
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_above_zero
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_blocks_fit
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
         MH.well_formed_major_heap r.capacity_major_out /\
         MH.read_word_in_major r.capacity_major_out old_addr == Some old_value))
  =
  SpecMajorAlloc.ensure_major_head_capacity_has_head_wosize
    mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_head_capacity_fl_valid
    mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_head_capacity_fl_above_zero
    mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_head_capacity_fl_blocks_fit
    mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_head_capacity_wf
    mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_head_capacity_preserves_old_read
    mh fp fuel needed fresh old_addr

let spot_ensure_head_capacity_alloc_no_oom
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (requested_wz: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires fuel > 0 /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   SpecMajorAlloc.major_alloc_demand_wosize requested_wz ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   SpecMajorAlloc.major_alloc_demand_wosize requested_wz))
      (ensures
        (let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             mh fp fuel
             (SpecMajorAlloc.major_alloc_demand_wosize requested_wz) fresh in
         let a =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             r.capacity_major_out r.capacity_fp_out requested_wz
             r.capacity_fuel_out in
         a.major_obj_out == r.capacity_fp_out /\ a.major_obj_out <> 0UL))
  = SpecMajorAlloc.ensure_major_head_capacity_alloc_no_oom
      mh fp fuel requested_wz fresh

let spot_major_alloc_after_expand_split_preserves_head_wosize
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (requested_wz fuel remaining: nat)
  : Lemma
      (requires U64.v fresh.base >= U64.v zero_addr /\
                requested_wz > 0 /\
                remaining > 0 /\
                SpecMajorAlloc.fresh_chunk_wosize fresh >=
                  requested_wz + 1 + remaining)
      (ensures
        (let er = SpecMajorAlloc.expand_major_heap mh fresh fp in
         let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             er.major_out er.fp_out requested_wz (fuel + 1) in
         r.major_obj_out == er.fp_out /\
         r.major_fp_out <> 0UL /\
         SpecMajorAlloc.major_fl_head_wosize
           r.major_alloc_out r.major_fp_out >= remaining))
  = SpecMajorAlloc.major_alloc_after_expand_split_preserves_head_wosize
      mh fresh fp requested_wz fuel remaining

let spot_major_alloc_head_split_preserves_head_wosize
  (mh: MH.major_heap) (fp: U64.t)
  (requested_wz fuel remaining: nat)
  : Lemma
      (requires fuel > 0 /\
                fp <> 0UL /\
                requested_wz > 0 /\
                remaining > 0 /\
                MH.well_formed_major_heap mh /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit mh fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  requested_wz + 1 + remaining)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             mh fp requested_wz fuel in
         r.major_obj_out == fp /\
         r.major_fp_out <> 0UL /\
         MH.well_formed_major_heap r.major_alloc_out /\
         SpecMajorAlloc.major_alloc_result_fp_in_objects r /\
         SpecMajorAlloc.major_fl_head_wosize
           r.major_alloc_out r.major_fp_out >= remaining))
  = SpecMajorAlloc.major_alloc_head_split_preserves_head_wosize
      mh fp requested_wz fuel remaining

let spot_major_alloc_head_split_link_not_self
  (mh: MH.major_heap) (fp: U64.t)
  (requested_wz fuel: nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                requested_wz > 0 /\
                MH.well_formed_major_heap mh /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit mh fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >= requested_wz + 2)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             mh fp requested_wz fuel in
         r.major_obj_out == fp /\
         r.major_fp_out <> 0UL /\
         SpecMajorAlloc.major_alloc_result_fp_link_not_self r))
  = SpecMajorAlloc.major_alloc_head_split_link_not_self
      mh fp requested_wz fuel

let spot_chunked_major_alloc_shape_active_head_split
  (mh: MH.major_heap) (fp: U64.t)
  (requested_wz fuel: nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                requested_wz > 0 /\
                GenInv.chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  requested_wz + 2)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             mh fp requested_wz fuel in
         r.major_obj_out == fp /\
         r.major_fp_out <> 0UL /\
         SpecMajorAlloc.major_alloc_result_fp_in_objects r /\
         GenInv.chunked_major_alloc_shape
           r.major_alloc_out r.major_fp_out fuel))
  = GenInv.chunked_major_alloc_shape_active_head_split
      mh fp requested_wz fuel

let spot_chunked_is_blue_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                Seq.mem obj (MH.major_objects mh))
      (ensures
        GenInv.chunked_is_blue
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        GenInv.chunked_is_blue mh obj)
  = GenInv.chunked_is_blue_preserved_by_expansion mh fresh fp obj

let spot_chunked_minor_major_fields_no_blue_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires GenInv.chunked_minor_major_fields_no_blue ms mh /\
                MH.chunk_disjoint_from_all fresh mh)
      (ensures
        GenInv.chunked_minor_major_fields_no_blue ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  = GenInv.chunked_minor_major_fields_no_blue_preserved_by_expansion
      ms mh fresh fp

let spot_chunked_minor_major_fields_no_blue_ensure_capacity
  (ms: minor_state) (mh: MH.major_heap)
  (fp: obj_addr) (fuel needed: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_minor_major_fields_no_blue ms mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh))
      (ensures
        GenInv.chunked_minor_major_fields_no_blue ms
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  = GenInv.chunked_minor_major_fields_no_blue_ensure_capacity
      ms mh fp fuel needed fresh

let spot_chunked_is_black_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                Seq.mem obj (MH.major_objects mh))
      (ensures
        GenInv.chunked_is_black
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        GenInv.chunked_is_black mh obj)
  = GenInv.chunked_is_black_preserved_by_expansion mh fresh fp obj

let spot_chunked_no_black_objects_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires GenInv.chunked_no_black_objects mh /\
                MH.chunk_disjoint_from_all fresh mh)
      (ensures
        GenInv.chunked_no_black_objects
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  = GenInv.chunked_no_black_objects_preserved_by_expansion mh fresh fp

let spot_chunked_no_black_objects_ensure_capacity
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_no_black_objects mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh))
      (ensures
        GenInv.chunked_no_black_objects
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  = GenInv.chunked_no_black_objects_ensure_capacity mh fp fuel needed fresh

let spot_chunked_no_scan_invariant_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires GenInv.chunked_no_scan_invariant mh /\
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures
        GenInv.chunked_no_scan_invariant
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  = GenInv.chunked_no_scan_invariant_preserved_by_expansion mh fresh fp

let spot_chunked_no_scan_invariant_ensure_capacity
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_no_scan_invariant mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        GenInv.chunked_no_scan_invariant
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  = GenInv.chunked_no_scan_invariant_ensure_capacity mh fp fuel needed fresh

let spot_chunked_no_pointer_to_blue_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires GenInv.chunked_no_pointer_to_blue mh /\
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures
        GenInv.chunked_no_pointer_to_blue
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  = GenInv.chunked_no_pointer_to_blue_preserved_by_expansion mh fresh fp

let spot_chunked_no_pointer_to_blue_ensure_capacity
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_no_pointer_to_blue mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        GenInv.chunked_no_pointer_to_blue
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  = GenInv.chunked_no_pointer_to_blue_ensure_capacity mh fp fuel needed fresh

let spot_chunked_major_minor_fields_no_infix_targets_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires GenInv.chunked_major_minor_fields_no_infix_targets ms mh /\
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures
        GenInv.chunked_major_minor_fields_no_infix_targets ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  = GenInv.chunked_major_minor_fields_no_infix_targets_preserved_by_expansion
      ms mh fresh fp

let spot_chunked_major_minor_fields_no_infix_targets_ensure_capacity
  (ms: minor_state) (mh: MH.major_heap)
  (fp: obj_addr) (fuel needed: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_major_minor_fields_no_infix_targets ms mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        GenInv.chunked_major_minor_fields_no_infix_targets ms
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  = GenInv.chunked_major_minor_fields_no_infix_targets_ensure_capacity
      ms mh fp fuel needed fresh

let spot_chunked_collection_heap_shape_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: obj_addr) (fuel: nat)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape ms mh fp fuel /\
                MH.chunk_disjoint_from_all fresh mh /\
                fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                U64.v fresh.base >= U64.v zero_addr /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures (
        let r = SpecMajorAlloc.expand_major_heap mh fresh fp in
        GenInv.chunked_collection_heap_shape ms r.major_out r.fp_out
          (fuel + 1)))
  = GenInv.chunked_collection_heap_shape_preserved_by_expansion
      ms mh fresh fp fuel

let spot_chunked_collection_heap_shape_ensure_capacity
  (ms: minor_state) (mh: MH.major_heap)
  (fp: obj_addr) (fuel needed: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape ms mh fp fuel /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh +
                   SpecMajorAlloc.major_fl_capacity mh fp fuel >= needed /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh in
        GenInv.chunked_collection_heap_shape
          ms r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_capacity
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out >= needed))
  = GenInv.chunked_collection_heap_shape_ensure_capacity
      ms mh fp fuel needed fresh

let spot_chunked_collection_heap_shape_ensure_head_capacity
  (ms: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape ms mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        GenInv.chunked_collection_heap_shape
          ms r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed))
  = GenInv.chunked_collection_heap_shape_ensure_head_capacity
      ms mh fp fuel needed fresh

let spot_chunked_collection_heap_shape_ensure_head_capacity_alloc_no_oom
  (ms: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (requested_wz: nat)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires fuel > 0 /\
                GenInv.chunked_collection_heap_shape ms mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   SpecMajorAlloc.major_alloc_demand_wosize requested_wz ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   SpecMajorAlloc.major_alloc_demand_wosize requested_wz /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let needed = SpecMajorAlloc.major_alloc_demand_wosize requested_wz in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let a =
          SpecMajorAlloc.major_alloc_spec_with_fuel
            r.capacity_major_out r.capacity_fp_out requested_wz
            r.capacity_fuel_out in
        GenInv.chunked_collection_heap_shape
          ms r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.major_obj_out == r.capacity_fp_out /\
        a.major_obj_out <> 0UL))
  = GenInv.chunked_collection_heap_shape_ensure_head_capacity_alloc_no_oom
      ms mh fp fuel requested_wz fresh

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

let spot_chunked_minor_field_edges
  (ms: minor_state) (mh: MH.major_heap) (src: U64.t) (wz: nat) (i: nat)
  : GTot (Seq.seq CG.combined_edge)
  = CG.chunked_minor_field_edges ms mh src wz i

let spot_chunked_minor_field_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (src: U64.t) (wz: nat) (i: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_minor_field_expansion_safe ms fresh src wz i)
      (ensures
        spot_chunked_minor_field_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out src wz i ==
        spot_chunked_minor_field_edges ms mh src wz i)
  = CG.chunked_minor_field_edges_preserved_by_expansion
      ms mh fresh fp src wz i

let spot_chunked_minor_object_edges
  (ms: minor_state) (mh: MH.major_heap) (obj: U64.t)
  : GTot (Seq.seq CG.combined_edge)
  = CG.chunked_minor_object_edges ms mh obj

let spot_chunked_minor_object_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (obj: U64.t)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_minor_object_expansion_safe ms fresh obj)
      (ensures
        spot_chunked_minor_object_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        spot_chunked_minor_object_edges ms mh obj)
  = CG.chunked_minor_object_edges_preserved_by_expansion ms mh fresh fp obj

let spot_chunked_all_minor_edges
  (ms: minor_state) (mh: MH.major_heap) (objs: Seq.seq U64.t) (idx: nat)
  : GTot (Seq.seq CG.combined_edge)
  = CG.chunked_all_minor_edges ms mh objs idx

let spot_chunked_all_minor_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (objs: Seq.seq U64.t) (idx: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_minor_expansion_safe ms fresh objs idx)
      (ensures
        spot_chunked_all_minor_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out objs idx ==
        spot_chunked_all_minor_edges ms mh objs idx)
  = CG.chunked_all_minor_edges_preserved_by_expansion
      ms mh fresh fp objs idx

let spot_build_chunked_combined_graph_from_major_objects
  (ms: minor_state) (mh: MH.major_heap) (major_objs: Seq.seq obj_addr)
  : GTot CG.combined_graph
  = CG.build_chunked_combined_graph_from_major_objects ms mh major_objs

let spot_build_chunked_combined_graph
  (ms: minor_state) (mh: MH.major_heap)
  : GTot CG.combined_graph
  = CG.build_chunked_combined_graph ms mh

let spot_chunked_combined_graph_old_view_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (major_objs: Seq.seq obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_minor_expansion_safe
                  ms fresh (minor_objects ms) 0 /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh major_objs 0)
      (ensures (
        let mh' = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
        let g' =
          spot_build_chunked_combined_graph_from_major_objects
            ms mh' major_objs in
        let g =
          spot_build_chunked_combined_graph_from_major_objects
            ms mh major_objs in
        g'.cg_vertices == g.cg_vertices /\ g'.cg_edges == g.cg_edges))
  = CG.chunked_combined_graph_old_view_preserved_by_expansion
      ms mh fresh fp major_objs

let spot_chunked_build_combined_graph_old_view_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_minor_expansion_safe
                  ms fresh (minor_objects ms) 0 /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures (
        let mh' = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
        let g' =
          spot_build_chunked_combined_graph_from_major_objects
            ms mh' (MH.major_objects mh) in
        let g = spot_build_chunked_combined_graph ms mh in
        g'.cg_vertices == g.cg_vertices /\ g'.cg_edges == g.cg_edges))
  = CG.chunked_build_combined_graph_old_view_preserved_by_expansion
      ms mh fresh fp

let spot_chunked_old_view_reachable_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (roots: Seq.seq CG.combined_vertex) (v: CG.combined_vertex)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_minor_expansion_safe
                  ms fresh (minor_objects ms) 0 /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0 /\
                CG.combined_reachable
                  (spot_build_chunked_combined_graph ms mh) roots v)
      (ensures (
        let mh' = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
        CG.combined_reachable
          (spot_build_chunked_combined_graph_from_major_objects
            ms mh' (MH.major_objects mh))
          roots v))
  = CG.chunked_old_view_reachable_preserved_by_expansion
      ms mh fresh fp roots v

let spot_chunked_header_of_object_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_header_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_header_of_object mh obj)
  = CG.chunked_header_of_object_preserved_by_expansion mh fresh fp obj

let spot_chunked_wosize_of_object_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_wosize_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_wosize_of_object mh obj)
  = CG.chunked_wosize_of_object_preserved_by_expansion mh fresh fp obj

let spot_chunked_wosize_nat_of_object_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_wosize_nat_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_wosize_nat_of_object mh obj)
  = CG.chunked_wosize_nat_of_object_preserved_by_expansion mh fresh fp obj

let spot_chunked_tag_of_object_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_tag_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_tag_of_object mh obj)
  = CG.chunked_tag_of_object_preserved_by_expansion mh fresh fp obj

let spot_chunked_is_no_scan_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_is_no_scan
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_is_no_scan mh obj)
  = CG.chunked_is_no_scan_preserved_by_expansion mh fresh fp obj

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

let spot_chunked_major_object_edges
  (ms: minor_state) (mh: MH.major_heap) (obj: obj_addr)
  : GTot (Seq.seq CG.combined_edge)
  = CG.chunked_major_object_edges ms mh obj

let spot_chunked_major_object_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_major_object_expansion_safe mh fresh obj)
      (ensures
        spot_chunked_major_object_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        spot_chunked_major_object_edges ms mh obj)
  = CG.chunked_major_object_edges_preserved_by_expansion ms mh fresh fp obj

let spot_chunked_all_major_object_edges
  (ms: minor_state) (mh: MH.major_heap) (objs: Seq.seq obj_addr) (idx: nat)
  : GTot (Seq.seq CG.combined_edge)
  = CG.chunked_all_major_object_edges ms mh objs idx

let spot_chunked_all_major_object_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (objs: Seq.seq obj_addr) (idx: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe mh fresh objs idx)
      (ensures
        spot_chunked_all_major_object_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out objs idx ==
        spot_chunked_all_major_object_edges ms mh objs idx)
  = CG.chunked_all_major_object_edges_preserved_by_expansion
      ms mh fresh fp objs idx

let spot_chunked_all_major_field_edges
  (ms: minor_state) (mh: MH.major_heap) (objs: Seq.seq obj_addr)
  (wz_of: obj_addr -> GTot nat) (idx: nat)
  : GTot (Seq.seq CG.combined_edge)
  = CG.chunked_all_major_field_edges ms mh objs wz_of idx

let spot_chunked_all_major_field_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (objs: Seq.seq obj_addr) (wz_of: obj_addr -> GTot nat) (idx: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_field_expansion_safe
                  mh fresh objs wz_of idx)
      (ensures
        spot_chunked_all_major_field_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out objs wz_of idx ==
        spot_chunked_all_major_field_edges ms mh objs wz_of idx)
  = CG.chunked_all_major_field_edges_preserved_by_expansion
      ms mh fresh fp objs wz_of idx
