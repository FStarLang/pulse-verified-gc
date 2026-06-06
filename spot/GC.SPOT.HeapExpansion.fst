module GC.SPOT.HeapExpansion

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Promote
open GC.Gen.Cheney

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SpecMajorAllocMultiAlloc = GC.Spec.MajorAllocator.MultiAlloc
module PromotionDemand = GC.Gen.PromotionDemand
module CheneyPreservation = GC.Gen.CheneyPreservation
module CheneyCorrectness = GC.Gen.CheneyCorrectness
module ChunkedPromote = GC.Gen.ChunkedPromote
module ChunkedCheney = GC.Gen.ChunkedCheney
module ChunkedUpdate = GC.Gen.ChunkedUpdate
module WriteBody = GC.Gen.WriteBodyLemmas
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

let spot_chunked_major_alloc_shape_alloc_list_head_split
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (requests: list nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                GenInv.chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  SpecMajorAllocMultiAlloc.allocation_list_demand requests + 1)
      (ensures
        (let r =
           SpecMajorAllocMultiAlloc.major_alloc_list_spec
             mh fp fuel requests in
         r.list_fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape r.list_major_out r.list_fp_out fuel /\
         SpecMajorAlloc.major_fl_head_wosize
           r.list_major_out r.list_fp_out >= 1 /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.list_objs_out))
  = GenInv.chunked_major_alloc_shape_alloc_list_head_split
      mh fp fuel requests

let spot_chunked_major_alloc_shape_alloc_list_with_budget
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (requests: list nat) (budget: nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                GenInv.chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  budget /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >= budget + 1)
      (ensures
        (let r =
           SpecMajorAllocMultiAlloc.major_alloc_list_spec
             mh fp fuel requests in
         r.list_fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape r.list_major_out r.list_fp_out fuel /\
         SpecMajorAlloc.major_fl_head_wosize
           r.list_major_out r.list_fp_out >= 1 /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.list_objs_out))
  = GenInv.chunked_major_alloc_shape_alloc_list_head_split_with_budget
      mh fp fuel requests budget

let spot_dense_alloc_list_single_chunk_with_budget_no_oom
  (g: heap) (fp: U64.t) (fuel: nat)
  (requests: list nat) (budget: nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                MH.well_formed_major_heap
                  (MH.single_chunk_major_heap g) /\
                SpecMajorAlloc.major_fl_valid
                  (MH.single_chunk_major_heap g) fp fuel /\
                SpecMajorAlloc.major_fl_above_zero
                  (MH.single_chunk_major_heap g) fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit
                  (MH.single_chunk_major_heap g) fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  budget /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap g) fp >= budget + 1)
      (ensures
        (let r =
           SpecMajorAllocMultiAlloc.dense_alloc_list_spec
             g fp fuel requests in
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.dense_list_objs_out))
  =
  SpecMajorAllocMultiAlloc.dense_alloc_list_head_split_nonzero_single_chunk_with_budget
    g fp fuel requests budget

let spot_chunked_major_alloc_shape_alloc_minor_objects_head_split
  (minor: minor_state) (mh: MH.major_heap) (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires fuel > 1 /\
                minor_wf minor /\
                fp <> 0UL /\
                GenInv.chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let requests = PromotionDemand.minor_promotion_requests minor in
         let r =
           SpecMajorAllocMultiAlloc.major_alloc_list_spec
             mh fp fuel requests in
         r.list_fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape r.list_major_out r.list_fp_out fuel /\
         SpecMajorAlloc.major_fl_head_wosize
           r.list_major_out r.list_fp_out >= 1 /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.list_objs_out))
  = GenInv.chunked_major_alloc_shape_alloc_minor_objects_head_split
      minor mh fp fuel

let spot_chunked_collection_shape_ensure_minor_promotion_allocs
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires fuel > 1 /\
                GenInv.chunked_collection_heap_shape minor mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   PromotionDemand.minor_promotion_demand minor + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   PromotionDemand.minor_promotion_demand minor + 1 /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let needed = PromotionDemand.minor_promotion_demand minor + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let requests = PromotionDemand.minor_promotion_requests minor in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        GenInv.chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        GenInv.chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))
  = GenInv.chunked_collection_heap_shape_ensure_minor_promotion_head_capacity_allocs
      minor mh fp fuel fresh

let spot_chunked_collection_shape_ensure_head_capacity_with_chain
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
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
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        SpecMajorAlloc.major_fl_chain_terminates
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out = true))
  = GenInv.chunked_collection_heap_shape_ensure_head_capacity_with_chain
      minor mh fp fuel needed fresh

let spot_chunked_collection_shape_ensure_head_capacity_with_chain_blue
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
                GenInv.chunked_chain_objects_blue mh fp fuel /\
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
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        SpecMajorAlloc.major_fl_chain_terminates
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out = true /\
        GenInv.chunked_chain_objects_blue
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))
  = GenInv.chunked_collection_heap_shape_ensure_head_capacity_with_chain_blue
      minor mh fp fuel needed fresh

let spot_chunked_collection_shape_ensure_head_capacity_alloc_list_budget
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (fresh: MH.heap_chunk)
  (requests: list nat) (budget: nat)
  : Lemma
      (requires fuel > 1 /\
                GenInv.chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  budget /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < budget + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= budget + 1 /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let needed = budget + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        GenInv.chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        GenInv.chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))
  = GenInv.chunked_collection_heap_shape_ensure_head_capacity_alloc_list_with_budget
      minor mh fp fuel fresh requests budget

let spot_chunked_collection_shape_ensure_minor_promotion_budget_alloc_list
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (fresh: MH.heap_chunk)
  (requests: list nat)
  : Lemma
      (requires fuel > 1 /\
                GenInv.chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  PromotionDemand.minor_promotion_demand minor /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   PromotionDemand.minor_promotion_demand minor + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   PromotionDemand.minor_promotion_demand minor + 1 /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let needed = PromotionDemand.minor_promotion_demand minor + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        GenInv.chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        GenInv.chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))
  = GenInv.chunked_collection_heap_shape_ensure_minor_promotion_budget_alloc_list
      minor mh fp fuel fresh requests

let spot_cheney_forwarded_minor_requests_budget
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma
      (requires minor_wf minor)
      (ensures
        (let requests =
           CheneyPreservation.cheney_forwarded_minor_requests
             minor major fp roots in
         SpecMajorAllocMultiAlloc.all_requests_positive requests /\
         SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
           PromotionDemand.minor_promotion_demand minor))
  =
  CheneyPreservation.cheney_forwarded_minor_requests_positive
    minor major fp roots;
  CheneyPreservation.cheney_forwarded_minor_requests_demand_bound
    minor major fp roots

let spot_cheney_unforwarded_split_demand_bound
  (minor: minor_state) (cs: cheney_state)
  : Lemma
      (ensures
        CheneyPreservation.cheney_unforwarded_split_demand minor cs <=
        PromotionDemand.minor_promotion_demand minor)
  =
  CheneyPreservation.cheney_unforwarded_split_demand_bound minor cs

let spot_cheney_forwarded_dense_alloc_list_single_chunk_no_oom
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (fuel: nat)
  : Lemma
      (requires minor_wf minor /\
                fuel > 1 /\
                fp <> 0UL /\
                MH.well_formed_major_heap
                  (MH.single_chunk_major_heap major) /\
                SpecMajorAlloc.major_fl_valid
                  (MH.single_chunk_major_heap major) fp fuel /\
                SpecMajorAlloc.major_fl_above_zero
                  (MH.single_chunk_major_heap major) fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit
                  (MH.single_chunk_major_heap major) fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                  PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let requests =
           CheneyPreservation.cheney_forwarded_minor_requests
             minor major fp roots in
         let r =
           SpecMajorAllocMultiAlloc.dense_alloc_list_spec
             major fp fuel requests in
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.dense_list_objs_out))
  =
  CheneyPreservation.cheney_forwarded_dense_alloc_list_single_chunk_no_oom
    minor major fp roots fuel

let spot_cheney_forwarded_dense_alloc_list_default_single_chunk_no_oom
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma
      (requires minor_wf minor /\
                SpecAlloc.alloc_search_fuel > 1 /\
                fp <> 0UL /\
                MH.well_formed_major_heap
                  (MH.single_chunk_major_heap major) /\
                SpecMajorAlloc.major_fl_valid
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_above_zero
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_blocks_fit
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                  PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let requests =
           CheneyPreservation.cheney_forwarded_minor_requests
             minor major fp roots in
         let r =
           SpecMajorAllocMultiAlloc.dense_alloc_list_default_spec
             major fp requests in
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.dense_list_objs_out))
  =
  CheneyPreservation.cheney_forwarded_dense_alloc_list_default_single_chunk_no_oom
    minor major fp roots

let spot_promote_object_head_no_oom_single_chunk
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 0 /\
                fp <> 0UL /\
                SpecMajorAlloc.major_fl_valid
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_above_zero
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_blocks_fit
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >= wosize)
      (ensures
        (promote_object minor major obj fp wosize).new_addr <> 0UL)
  =
  CheneyPreservation.promote_object_head_no_oom_single_chunk
    minor major obj fp wosize

let spot_promote_minor_object_head_no_oom_single_chunk
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  : Lemma
      (requires minor_wf minor /\
                Seq.mem obj (minor_objects minor) /\
                wosize == minor_wosize minor obj /\
                SpecAlloc.alloc_search_fuel > 0 /\
                fp <> 0UL /\
                SpecMajorAlloc.major_fl_valid
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_above_zero
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_blocks_fit
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                  PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (promote_object minor major obj fp wosize).new_addr <> 0UL)
  =
  CheneyPreservation.promote_minor_object_head_no_oom_single_chunk
    minor major obj fp wosize

let spot_chunked_copy_fields_frame_after
  (minor: minor_state) (mh: MH.major_heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  (target: hp_addr) (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh target == Some old /\
        U64.v dst_obj + n * U64.v mword <= U64.v target)
      (ensures
        MH.read_word_in_major
          (ChunkedPromote.chunked_copy_fields
            minor mh src_obj dst_obj i n)
          target == Some old)
  =
  ChunkedPromote.chunked_copy_fields_frame_after
    minor mh src_obj dst_obj i n target old

let spot_chunked_copy_fields_preserves_major_objects
  (minor: minor_state) (mh: MH.major_heap)
  (src_obj dst_obj: U64.t) (i n idx: nat) (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        U64.v dst_obj >= U64.v mword /\
        U64.v dst_obj < heap_size /\
        U64.v dst_obj % U64.v mword == 0 /\
        i <= n /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address (dst_obj <: obj_addr)) == Some idx /\
        Seq.mem (dst_obj <: obj_addr) (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address (dst_obj <: obj_addr)) ==
          Some hdr /\
        n <= U64.v (Obj.getWosize hdr))
      (ensures
        (let mh' =
           ChunkedPromote.chunked_copy_fields
             minor mh src_obj dst_obj i n in
         MH.well_formed_major_heap mh' /\
         MH.major_objects mh' == MH.major_objects mh /\
         MH.read_word_in_major mh' (hd_address (dst_obj <: obj_addr)) ==
           Some hdr))
  =
  ChunkedPromote.chunked_copy_fields_preserves_major_objects
    minor mh src_obj dst_obj i n idx hdr

let spot_chunked_copy_fields_field_effect
  (minor: minor_state) (mh: MH.major_heap)
  (src_obj dst_obj: U64.t) (i n j idx: nat) (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        U64.v dst_obj >= U64.v mword /\
        U64.v dst_obj < heap_size /\
        U64.v dst_obj % U64.v mword == 0 /\
        i <= j /\ j < n /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address (dst_obj <: obj_addr)) == Some idx /\
        Seq.mem (dst_obj <: obj_addr) (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address (dst_obj <: obj_addr)) ==
          Some hdr /\
        n <= U64.v (Obj.getWosize hdr))
      (ensures
        (let result =
           ChunkedPromote.chunked_copy_fields
             minor mh src_obj dst_obj i n in
         let addr_nat = U64.v dst_obj + j * U64.v mword in
         addr_nat + U64.v mword <= heap_size /\
         addr_nat % U64.v mword == 0 /\
         MH.read_word_in_major result (U64.uint_to_t addr_nat) ==
           Some (minor_read_field minor src_obj j)))
  =
  ChunkedPromote.chunked_copy_fields_field_effect
    minor mh src_obj dst_obj i n j idx hdr

let spot_chunked_promote_object_success_field_effect
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  (j: nat) (field_addr: hp_addr) (idx: nat) (hdr: U64.t)
  : Lemma
      (requires
        (let alloc_res =
           SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
         let dst = alloc_res.major_obj_out in
         alloc_res.major_obj_out <> 0UL /\
         U64.v dst >= U64.v mword /\
         U64.v dst < heap_size /\
         U64.v dst % U64.v mword == 0 /\
         j < wosize /\
         U64.v field_addr == U64.v dst + j * U64.v mword /\
         MH.well_formed_major_heap alloc_res.major_alloc_out /\
         idx < Seq.length alloc_res.major_alloc_out /\
         MH.lookup_chunk_index alloc_res.major_alloc_out
           (hd_address (dst <: obj_addr)) == Some idx /\
         Seq.mem (dst <: obj_addr)
           (MH.major_objects alloc_res.major_alloc_out) /\
         MH.read_word_in_major alloc_res.major_alloc_out
           (hd_address (dst <: obj_addr)) == Some hdr /\
         U64.v (Obj.getWosize hdr) == wosize))
      (ensures
        (let alloc_res =
           SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
         let dst = alloc_res.major_obj_out in
         let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor mh obj fp wosize fuel in
         let addr_nat = U64.v dst + j * U64.v mword in
         res.new_addr == dst /\
         addr_nat + U64.v mword <= heap_size /\
         addr_nat % U64.v mword == 0 /\
         MH.read_word_in_major res.major_out field_addr ==
           Some (minor_read_field minor obj j)))
  =
  ChunkedPromote.chunked_promote_object_success_field_effect
    minor mh obj fp wosize fuel j field_addr idx hdr

let spot_major_write_word_or_same_read_frame
  (mh: MH.major_heap) (write_addr target: hp_addr)
  (value old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh target == Some old /\
        (U64.v target + U64.v mword <= U64.v write_addr \/
         U64.v write_addr + U64.v mword <= U64.v target))
      (ensures
        MH.read_word_in_major
          (SpecMajorAlloc.major_write_word_or_same mh write_addr value)
          target == Some old)
  =
  ChunkedPromote.major_write_word_or_same_read_frame
    mh write_addr target value old

let spot_chunked_set_promoted_tag_read_frame
  (mh: MH.major_heap) (obj: U64.t) (tag: nat)
  (target: hp_addr) (old: U64.t)
  : Lemma
      (requires
        U64.v obj >= U64.v mword /\
        U64.v obj < heap_size /\
        U64.v obj % U64.v mword == 0 /\
        MH.read_word_in_major mh target == Some old /\
        (let dst : obj_addr = obj in
         U64.v target + U64.v mword <= U64.v (hd_address dst) \/
         U64.v (hd_address dst) + U64.v mword <= U64.v target))
      (ensures
        MH.read_word_in_major
          (ChunkedPromote.chunked_set_promoted_tag mh obj tag)
          target == Some old)
  =
  ChunkedPromote.chunked_set_promoted_tag_read_frame
    mh obj tag target old

let spot_chunked_set_promoted_tag_preserves_major_objects
  (mh: MH.major_heap) (obj: U64.t) (tag idx: nat) (hdr: U64.t)
  : Lemma
      (requires
        tag < 256 /\
        MH.well_formed_major_heap mh /\
        U64.v obj >= U64.v mword /\
        U64.v obj < heap_size /\
        U64.v obj % U64.v mword == 0 /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address (obj <: obj_addr)) == Some idx /\
        Seq.mem (obj <: obj_addr) (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address (obj <: obj_addr)) == Some hdr)
      (ensures
        (let mh' = ChunkedPromote.chunked_set_promoted_tag mh obj tag in
         MH.well_formed_major_heap mh' /\
         MH.major_objects mh' == MH.major_objects mh))
  =
  ChunkedPromote.chunked_set_promoted_tag_preserves_major_objects
    mh obj tag idx hdr

let spot_chunked_promote_object_default_single_chunk_compat
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma
      (requires
        (let alloc_res = SpecAlloc.alloc_spec major fp wosize in
         alloc_res.obj_out <> 0UL ==>
         U64.v alloc_res.obj_out >= U64.v zero_addr + U64.v mword /\
         U64.v alloc_res.obj_out < heap_size /\
         U64.v alloc_res.obj_out % U64.v mword == 0))
      (ensures
        (let chunked =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor (MH.single_chunk_major_heap major) obj fp wosize
             SpecAlloc.alloc_search_fuel in
         let dense = promote_object minor major obj fp wosize in
         chunked.major_out == MH.single_chunk_major_heap dense.major_out /\
         chunked.fp_out == dense.fp_out /\
         chunked.new_addr == dense.new_addr))
  =
  CheneyPreservation.chunked_promote_object_default_single_chunk_compat
    minor major obj fp wosize

let spot_chunked_cheney_forward_one_default_single_chunk_compat
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (ensures
        ChunkedCheney.chunked_cheney_forward_one
          minor (ChunkedCheney.single_chunk_cheney_state cs) addr
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_forward_one minor cs addr))
  =
  CheneyPreservation.chunked_cheney_forward_one_default_single_chunk_compat
    minor cs addr

let spot_chunked_cheney_forward_fields_default_single_chunk_compat
  (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma
      (ensures
        ChunkedCheney.chunked_cheney_forward_fields
          minor (ChunkedCheney.single_chunk_cheney_state cs) parent idx wosize
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_forward_fields minor cs parent idx wosize))
  =
  CheneyPreservation.chunked_cheney_forward_fields_default_single_chunk_compat
    minor cs parent idx wosize

let spot_chunked_cheney_forward_roots_default_single_chunk_compat
  (minor: minor_state) (cs: cheney_state) (roots: Seq.seq U64.t) (idx: nat)
  : Lemma
      (ensures
        ChunkedCheney.chunked_cheney_forward_roots
          minor (ChunkedCheney.single_chunk_cheney_state cs) roots idx
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_forward_roots minor cs roots idx))
  =
  CheneyPreservation.chunked_cheney_forward_roots_default_single_chunk_compat
    minor cs roots idx

let spot_chunked_cheney_scan_default_single_chunk_compat
  (minor: minor_state) (cs: cheney_state) (scan scan_fuel: nat)
  : Lemma
      (ensures
        ChunkedCheney.chunked_cheney_scan
          minor (ChunkedCheney.single_chunk_cheney_state cs) scan scan_fuel
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_scan minor cs scan scan_fuel))
  =
  CheneyPreservation.chunked_cheney_scan_default_single_chunk_compat
    minor cs scan scan_fuel

let spot_chunked_cheney_promote_default_single_chunk_compat
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma
      (ensures
        (let chunked =
           ChunkedCheney.chunked_cheney_promote
             minor (MH.single_chunk_major_heap major) fp roots
             SpecAlloc.alloc_search_fuel in
         let dense = cheney_promote minor major fp roots in
         chunked.major_final == MH.single_chunk_major_heap dense.major_final /\
         chunked.fp_final == dense.fp_final /\
         chunked.fwd_map == dense.fwd_map))
  =
  CheneyPreservation.chunked_cheney_promote_default_single_chunk_compat
    minor major fp roots

let spot_chunked_cheney_forward_normal_noalloc_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        ((~(Seq.mem addr (minor_objects minor)) \/
          cs.ccs_fwd addr <> 0UL) \/
         (Seq.mem addr (minor_objects minor) /\
          cs.ccs_fwd addr = 0UL /\
          minor_wosize minor addr = 0) \/
         (Seq.mem addr (minor_objects minor) /\
          cs.ccs_fwd addr = 0UL /\
          minor_wosize minor addr > 0 /\
          (ChunkedPromote.chunked_promote_object_with_fuel
            minor cs.ccs_major addr cs.ccs_fp
            (minor_wosize minor addr) fuel).new_addr = 0UL)))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal
             minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true))
  =
  CheneyPreservation.chunked_cheney_forward_normal_noalloc_preserves_chunked_alloc_shape
    minor cs addr fuel

let spot_chunked_cheney_forward_normal_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         minor_wosize minor addr > 0 ==>
         cs.ccs_fp <> 0UL /\
         SpecMajorAlloc.major_fl_head_wosize
           cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal
             minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true))
  =
  CheneyPreservation.chunked_cheney_forward_normal_head_split_preserves_chunked_alloc_shape
    minor cs addr fuel

let spot_chunked_cheney_forward_normal_head_split_preserves_chain_objects_blue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        GenInv.chunked_chain_objects_blue cs.ccs_major cs.ccs_fp fuel /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         minor_wosize minor addr > 0 ==>
         cs.ccs_fp <> 0UL /\
         SpecMajorAlloc.major_fl_head_wosize
           cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal
             minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true /\
         GenInv.chunked_chain_objects_blue cs'.ccs_major cs'.ccs_fp fuel))
  =
  CheneyPreservation.chunked_cheney_forward_normal_head_split_preserves_chain_objects_blue
    minor cs addr fuel

let spot_chunked_cheney_forward_one_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         ~(is_infix_in_minor minor addr) /\
         minor_wosize minor addr > 0 ==>
           cs.ccs_fp <> 0UL /\
           SpecMajorAlloc.major_fl_head_wosize
             cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2) /\
        (cs.ccs_fwd addr = 0UL /\
         is_infix_in_minor minor addr ==>
           (let parent = infix_parent minor addr in
            Seq.mem parent (minor_objects minor) /\
            cs.ccs_fwd parent = 0UL /\
            minor_wosize minor parent > 0 ==>
              cs.ccs_fp <> 0UL /\
              SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= minor_wosize minor parent + 2)))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true))
  =
  CheneyPreservation.chunked_cheney_forward_one_head_split_preserves_chunked_alloc_shape
    minor cs addr fuel

let spot_chunked_cheney_forward_one_head_split_preserves_chain_objects_blue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        GenInv.chunked_chain_objects_blue cs.ccs_major cs.ccs_fp fuel /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         ~(is_infix_in_minor minor addr) /\
         minor_wosize minor addr > 0 ==>
           cs.ccs_fp <> 0UL /\
           SpecMajorAlloc.major_fl_head_wosize
             cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2) /\
        (cs.ccs_fwd addr = 0UL /\
         is_infix_in_minor minor addr ==>
           (let parent = infix_parent minor addr in
            Seq.mem parent (minor_objects minor) /\
            cs.ccs_fwd parent = 0UL /\
            minor_wosize minor parent > 0 ==>
              cs.ccs_fp <> 0UL /\
              SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= minor_wosize minor parent + 2)))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true /\
         GenInv.chunked_chain_objects_blue cs'.ccs_major cs'.ccs_fp fuel))
  =
  CheneyPreservation.chunked_cheney_forward_one_head_split_preserves_chain_objects_blue
    minor cs addr fuel

let spot_chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (remaining: nat)
  : Lemma
      (requires
        fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        CheneyPreservation.chunked_cheney_forward_one_budget_ready
          minor cs addr remaining)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           cs'.ccs_major cs'.ccs_fp >= remaining))
  =
  CheneyPreservation.chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
    minor cs addr fuel remaining

let spot_chunked_cheney_forward_roots_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: Seq.seq U64.t) (idx: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_forward_roots_split_ready
          minor cs roots idx alloc_fuel)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_roots
             minor cs roots idx alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true))
  =
  CheneyPreservation.chunked_cheney_forward_roots_head_split_preserves_chunked_alloc_shape
    minor cs roots idx alloc_fuel

let spot_chunked_cheney_forward_roots_head_split_preserves_chain_objects_blue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: Seq.seq U64.t) (idx: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_forward_roots_split_ready
          minor cs roots idx alloc_fuel)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_roots
             minor cs roots idx alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
           cs'.ccs_major cs'.ccs_fp alloc_fuel))
  =
  CheneyPreservation.chunked_cheney_forward_roots_head_split_preserves_chain_objects_blue
    minor cs roots idx alloc_fuel

let spot_chunked_cheney_forward_roots_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: Seq.seq U64.t) (idx: nat) (alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_forward_roots_budget_ready
          minor cs roots idx alloc_fuel remaining)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_roots
             minor cs roots idx alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           cs'.ccs_major cs'.ccs_fp >= remaining))
  =
  CheneyPreservation.chunked_cheney_forward_roots_head_split_preserves_remaining_head_wosize
    minor cs roots idx alloc_fuel remaining

let spot_chunked_cheney_forward_roots_covers_roots_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_forward_roots_budget_ready
          minor cs roots 0 alloc_fuel remaining)
      (ensures
        GC.Gen.CheneyBFS.fwd_covers_roots minor
          (ChunkedCheney.chunked_cheney_forward_roots
            minor cs roots 0 alloc_fuel).ccs_fwd
          roots)
  =
  CheneyPreservation.chunked_cheney_forward_roots_covers_roots_from_budget
    minor cs roots alloc_fuel remaining

let spot_chunked_cheney_forward_fields_covers_successors_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_forward_fields_budget_ready
          minor cs parent 0 (minor_wosize minor parent)
          alloc_fuel remaining)
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent 0 (minor_wosize minor parent) alloc_fuel in
         forall (y:U64.t).
          Seq.mem y (GC.Gen.Reachability.minor_successors minor parent) /\
          minor_wosize minor y > 0 ==>
          cs'.ccs_fwd y <> 0UL))
  =
  CheneyPreservation.chunked_cheney_forward_fields_covers_successors_from_budget
    minor cs parent alloc_fuel remaining

let spot_chunked_cheney_scan_fwd_monotone
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat) (x: U64.t)
  : Lemma
      (requires cs.ccs_fwd x <> 0UL)
      (ensures
        (ChunkedCheney.chunked_cheney_scan
          minor cs scan scan_fuel alloc_fuel).ccs_fwd x <> 0UL)
  =
  CheneyPreservation.chunked_cheney_scan_fwd_monotone
    minor cs scan scan_fuel alloc_fuel x

let spot_chunked_scanned_prefix_step_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat) (alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_scanned_prefix_closed minor cs scan /\
        scan < Seq.length cs.ccs_queue /\
        (let parent = Seq.index cs.ccs_queue scan in
         CheneyPreservation.chunked_cheney_forward_fields_budget_ready
          minor cs parent 0 (minor_wosize minor parent)
          alloc_fuel remaining))
      (ensures
        (let parent = Seq.index cs.ccs_queue scan in
         let cs' =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent 0 (minor_wosize minor parent) alloc_fuel in
         CheneyPreservation.chunked_scanned_prefix_closed
          minor cs' (scan + 1)))
  =
  CheneyPreservation.chunked_scanned_prefix_step_from_budget
    minor cs scan alloc_fuel remaining

let spot_chunked_cheney_scan_scanned_prefix_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_scanned_prefix_closed minor cs scan /\
        CheneyPreservation.chunked_cheney_scan_budget_ready
          minor cs scan scan_fuel alloc_fuel remaining)
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel in
         CheneyPreservation.chunked_scanned_prefix_closed minor cs'
          (CheneyPreservation.chunked_cheney_scan_end_index
            minor cs scan scan_fuel alloc_fuel)))
  =
  CheneyPreservation.chunked_cheney_scan_scanned_prefix_from_budget
    minor cs scan scan_fuel alloc_fuel remaining

let spot_chunked_cheney_forward_roots_preserves_fwd_in_queue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: Seq.seq U64.t) (idx alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        CheneyPreservation.chunked_fwd_in_queue minor cs)
      (ensures
        CheneyPreservation.chunked_fwd_in_queue minor
          (ChunkedCheney.chunked_cheney_forward_roots
            minor cs roots idx alloc_fuel))
  =
  CheneyPreservation.chunked_cheney_forward_roots_preserves_fwd_in_queue
    minor cs roots idx alloc_fuel

let spot_chunked_cheney_scan_preserves_fwd_in_queue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        CheneyPreservation.chunked_fwd_in_queue minor cs)
      (ensures
        CheneyPreservation.chunked_fwd_in_queue minor
          (ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel))
  =
  CheneyPreservation.chunked_cheney_scan_preserves_fwd_in_queue
    minor cs scan scan_fuel alloc_fuel

let spot_chunked_cheney_scan_fwd_closed_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_fwd_in_queue minor cs /\
        CheneyPreservation.chunked_scanned_prefix_closed minor cs scan /\
        CheneyPreservation.chunked_cheney_scan_budget_ready
          minor cs scan scan_fuel alloc_fuel remaining /\
        (let cs' =
          ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel in
         CheneyPreservation.chunked_cheney_scan_end_index
          minor cs scan scan_fuel alloc_fuel >= Seq.length cs'.ccs_queue))
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel in
         GC.Gen.CheneyBFS.fwd_closed minor cs'.ccs_fwd))
  =
  CheneyPreservation.chunked_cheney_scan_fwd_closed_from_budget
    minor cs scan scan_fuel alloc_fuel remaining

let spot_chunked_cheney_scan_end_exhausted_or_fuel
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat)
  : Lemma
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
         let end_idx =
           CheneyPreservation.chunked_cheney_scan_end_index
             minor cs scan scan_fuel alloc_fuel in
         end_idx >= Seq.length cs'.ccs_queue \/
         end_idx == scan + scan_fuel))
  =
  CheneyPreservation.chunked_cheney_scan_end_exhausted_or_fuel
    minor cs scan scan_fuel alloc_fuel

let spot_chunked_cheney_promote_scan_exhaustion
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires minor_wf minor)
      (ensures
        (let cs0 : ChunkedCheney.chunked_cheney_state =
          { ccs_major = major; ccs_fp = fp;
            ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
         let cs1 =
          ChunkedCheney.chunked_cheney_forward_roots
            minor cs0 roots 0 alloc_fuel in
         let cs2 =
          ChunkedCheney.chunked_cheney_scan
            minor cs1 0 (cheney_fuel minor) alloc_fuel in
         CheneyPreservation.chunked_cheney_scan_end_index
          minor cs1 0 (cheney_fuel minor) alloc_fuel >=
         Seq.length cs2.ccs_queue))
  =
  CheneyPreservation.chunked_cheney_promote_scan_exhaustion
    minor major fp roots alloc_fuel

let spot_chunked_cheney_promote_no_oom_from_budget_and_scan_exhaustion
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize major fp >=
          PromotionDemand.minor_promotion_demand minor + 1 /\
        (let cs0 : ChunkedCheney.chunked_cheney_state =
          { ccs_major = major; ccs_fp = fp;
            ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
         let cs1 =
          ChunkedCheney.chunked_cheney_forward_roots
            minor cs0 roots 0 alloc_fuel in
         let cs2 =
          ChunkedCheney.chunked_cheney_scan
            minor cs1 0 (cheney_fuel minor) alloc_fuel in
         CheneyPreservation.chunked_cheney_scan_end_index
          minor cs1 0 (cheney_fuel minor) alloc_fuel >=
         Seq.length cs2.ccs_queue))
      (ensures
        CheneyPreservation.chunked_cheney_no_oom
          minor major fp roots alloc_fuel)
  =
  CheneyPreservation.chunked_cheney_promote_no_oom_from_budget_and_scan_exhaustion
    minor major fp roots alloc_fuel

let spot_chunked_cheney_promote_no_oom_from_budget
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize major fp >=
          PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        CheneyPreservation.chunked_cheney_no_oom
          minor major fp roots alloc_fuel)
  =
  CheneyPreservation.chunked_cheney_promote_no_oom_from_budget
    minor major fp roots alloc_fuel

let spot_chunked_cheney_promote_forwards_reachable_from_budget
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize major fp >=
          PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         forall (x:U64.t).
          Seq.mem x (minor_reachable minor roots) /\
          minor_wosize minor x > 0 ==>
          res.fwd_map x <> 0UL))
  =
  CheneyPreservation.chunked_cheney_promote_forwards_reachable_from_budget
    minor major fp roots alloc_fuel

let spot_chunked_cheney_forward_fields_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_forward_fields_split_ready
          minor cs parent idx wosize alloc_fuel)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_fields
             minor cs parent idx wosize alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true))
  =
  CheneyPreservation.chunked_cheney_forward_fields_head_split_preserves_chunked_alloc_shape
    minor cs parent idx wosize alloc_fuel

let spot_chunked_cheney_forward_fields_head_split_preserves_chain_objects_blue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_forward_fields_split_ready
          minor cs parent idx wosize alloc_fuel)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_fields
             minor cs parent idx wosize alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
           cs'.ccs_major cs'.ccs_fp alloc_fuel))
  =
  CheneyPreservation.chunked_cheney_forward_fields_head_split_preserves_chain_objects_blue
    minor cs parent idx wosize alloc_fuel

let spot_chunked_cheney_forward_fields_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (alloc_fuel: nat)
  (remaining: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_forward_fields_budget_ready
          minor cs parent idx wosize alloc_fuel remaining)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_fields
             minor cs parent idx wosize alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           cs'.ccs_major cs'.ccs_fp >= remaining))
  =
  CheneyPreservation.chunked_cheney_forward_fields_head_split_preserves_remaining_head_wosize
    minor cs parent idx wosize alloc_fuel remaining

let spot_chunked_cheney_scan_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat) (scan_fuel: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_scan_split_ready
          minor cs scan scan_fuel alloc_fuel)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true))
  =
  CheneyPreservation.chunked_cheney_scan_head_split_preserves_chunked_alloc_shape
    minor cs scan scan_fuel alloc_fuel

let spot_chunked_cheney_scan_head_split_preserves_chain_objects_blue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat) (scan_fuel: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_scan_split_ready
          minor cs scan scan_fuel alloc_fuel)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
           cs'.ccs_major cs'.ccs_fp alloc_fuel))
  =
  CheneyPreservation.chunked_cheney_scan_head_split_preserves_chain_objects_blue
    minor cs scan scan_fuel alloc_fuel

let spot_chunked_cheney_scan_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat) (scan_fuel: nat) (alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_scan_budget_ready
          minor cs scan scan_fuel alloc_fuel remaining)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           cs'.ccs_major cs'.ccs_fp >= remaining))
  =
  CheneyPreservation.chunked_cheney_scan_head_split_preserves_remaining_head_wosize
    minor cs scan scan_fuel alloc_fuel remaining

let spot_chunked_cheney_promote_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel)
      (ensures
        (let res =
           ChunkedCheney.chunked_cheney_promote
             minor major fp roots alloc_fuel in
         GenInv.chunked_major_alloc_shape
           res.major_final res.fp_final alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_final res.fp_final alloc_fuel = true))
  =
  CheneyPreservation.chunked_cheney_promote_head_split_preserves_chunked_alloc_shape
    minor major fp roots alloc_fuel

let spot_chunked_cheney_promote_head_split_preserves_old_major_objects
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel)
      (ensures
        (let res =
           ChunkedCheney.chunked_cheney_promote
             minor major fp roots alloc_fuel in
         forall (src: obj_addr).
          Seq.mem src (MH.major_objects major) ==>
          Seq.mem src (MH.major_objects res.major_final)))
  =
  CheneyPreservation.chunked_cheney_promote_head_split_preserves_old_major_objects
    minor major fp roots alloc_fuel

let spot_chunked_cheney_promote_head_split_preserves_old_non_blue_header
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (src: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (Obj.getWosize hdr) >= 1)
      (ensures
        (let res =
           ChunkedCheney.chunked_cheney_promote
             minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final (hd_address src) ==
           Some hdr))
  =
  CheneyPreservation.chunked_cheney_promote_head_split_preserves_old_non_blue_header
    minor major fp roots alloc_fuel src hdr

let spot_chunked_cheney_promote_head_split_preserves_old_non_blue_field
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (src: obj_addr) (hdr: U64.t)
  (j: nat) (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        j < U64.v (Obj.getWosize hdr) /\
        U64.v field_addr == U64.v src + j * U64.v mword /\
        MH.read_word_in_major major field_addr == Some old)
      (ensures
        (let res =
           ChunkedCheney.chunked_cheney_promote
             minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final field_addr == Some old))
  =
  CheneyPreservation.chunked_cheney_promote_head_split_preserves_old_non_blue_field
    minor major fp roots alloc_fuel src hdr j field_addr old

let spot_chunked_cheney_promote_head_split_preserves_chain_objects_blue
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel)
      (ensures
        (let res =
           ChunkedCheney.chunked_cheney_promote
             minor major fp roots alloc_fuel in
         GenInv.chunked_major_alloc_shape
           res.major_final res.fp_final alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_final res.fp_final alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
           res.major_final res.fp_final alloc_fuel))
  =
  CheneyPreservation.chunked_cheney_promote_head_split_preserves_chain_objects_blue
    minor major fp roots alloc_fuel

let spot_chunked_cheney_promote_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        (let res =
           ChunkedCheney.chunked_cheney_promote
             minor major fp roots alloc_fuel in
         GenInv.chunked_major_alloc_shape
           res.major_final res.fp_final alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_final res.fp_final alloc_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           res.major_final res.fp_final >= remaining))
  =
  CheneyPreservation.chunked_cheney_promote_head_split_preserves_remaining_head_wosize
    minor major fp roots alloc_fuel remaining

let spot_chunked_cheney_promote_budget_ready_from_minor_demand
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize major fp >=
          PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        CheneyPreservation.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel 1)
  =
  CheneyPreservation.chunked_cheney_promote_budget_ready_from_minor_demand
    minor major fp roots alloc_fuel

let spot_chunked_cheney_promote_after_minor_promotion_head_preflight
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        (SpecMajorAlloc.major_fl_head_wosize major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          MH.chunk_disjoint_from_all fresh major /\
          fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
          U64.v fresh.base >= U64.v zero_addr /\
          SpecMajorAlloc.fresh_chunk_wosize fresh >=
            PromotionDemand.minor_promotion_demand minor + 1 /\
          CG.chunked_all_major_object_expansion_safe
            major fresh (MH.major_objects major) 0))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let res =
           ChunkedCheney.chunked_cheney_promote
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         GenInv.chunked_collection_heap_shape
           minor r.capacity_major_out r.capacity_fp_out
           r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_head_wosize
           r.capacity_major_out r.capacity_fp_out >= needed /\
         SpecMajorAlloc.major_fl_chain_terminates
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out = true /\
         GenInv.chunked_chain_objects_blue
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
         CheneyPreservation.chunked_fwd_targets_above_minor res.fwd_map /\
         CheneyPreservation.chunked_fwd_targets_valid_addr res.fwd_map /\
         (forall (x:U64.t).
           Seq.mem x (minor_reachable minor roots) /\
           minor_wosize minor x > 0 ==>
           res.fwd_map x <> 0UL) /\
         (forall (src: obj_addr).
           Seq.mem src (MH.major_objects major) ==>
           Seq.mem src (MH.major_objects res.major_final)) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
           Seq.mem src (MH.major_objects major) /\
           MH.read_word_in_major major (hd_address src) == Some hdr /\
           Obj.getColor hdr <> GC.Lib.Header.Blue /\
           U64.v (Obj.getWosize hdr) >= 1 ==>
           MH.read_word_in_major res.major_final (hd_address src) ==
             Some hdr) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          forall (j:nat). forall (field_addr: hp_addr).
          forall (old: U64.t).
           Seq.mem src (MH.major_objects major) /\
           MH.read_word_in_major major (hd_address src) == Some hdr /\
           Obj.getColor hdr <> GC.Lib.Header.Blue /\
           j < U64.v (Obj.getWosize hdr) /\
           U64.v field_addr == U64.v src + j * U64.v mword /\
           MH.read_word_in_major major field_addr == Some old ==>
           MH.read_word_in_major res.major_final field_addr == Some old) /\
         GenInv.chunked_major_alloc_shape
           res.major_final res.fp_final r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_final res.fp_final r.capacity_fuel_out = true /\
         GenInv.chunked_chain_objects_blue
           res.major_final res.fp_final r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_head_wosize
           res.major_final res.fp_final >= 1))
  =
  CheneyPreservation.chunked_cheney_promote_after_minor_promotion_head_preflight
    minor major fp roots alloc_fuel fresh

let spot_chunked_alloc_head_split_alloc_header_wosize
  (mh: MH.major_heap) (fp: U64.t)
  (wosize: nat{wosize > 0 /\
                wosize < pow2 54 /\
                FStar.UInt.size wosize 64})
  (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
         let dst : obj_addr = fp in
         r.major_obj_out == fp /\
         r.major_fp_out <> 0UL /\
         MH.read_word_in_major r.major_alloc_out (hd_address dst) ==
           Some (SpecAlloc.make_header (U64.uint_to_t wosize)
                   SpecAlloc.white_bits 0UL) /\
         U64.v (Obj.getWosize
           (SpecAlloc.make_header (U64.uint_to_t wosize)
             SpecAlloc.white_bits 0UL)) == wosize))
  =
  CheneyPreservation.chunked_alloc_head_split_alloc_header_wosize
    mh fp wosize fuel

let spot_chunked_promote_head_split_padding_noop
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2)
      (ensures
        (let alloc_res =
           SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
         let copied =
           ChunkedPromote.chunked_copy_fields
             minor alloc_res.major_alloc_out obj fp 0 wosize in
         ChunkedPromote.chunked_zero_promote_padding copied fp wosize ==
           copied))
  =
  CheneyPreservation.chunked_promote_head_split_padding_noop
    minor mh obj fp wosize fuel

let spot_chunked_promote_object_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2)
      (ensures
        (let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor mh obj fp wosize fuel in
         res.new_addr == fp /\
         res.fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape res.major_out res.fp_out fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_out res.fp_out fuel = true /\
         (let alloc_res =
            SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
          MH.major_objects res.major_out ==
            MH.major_objects alloc_res.major_alloc_out /\
          (forall (src:obj_addr).
            Seq.mem src (MH.major_objects mh) ==>
            Seq.mem src (MH.major_objects res.major_out)) /\
          (forall (src:obj_addr). forall (hdr:U64.t).
            Seq.mem src (MH.major_objects mh) /\
            src <> fp /\
            MH.read_word_in_major mh (hd_address src) == Some hdr /\
            U64.v (Obj.getWosize hdr) >= 1 ==>
            MH.read_word_in_major res.major_out (hd_address src) ==
              Some hdr) /\
          Seq.mem (fp <: obj_addr)
            (MH.major_objects alloc_res.major_alloc_out) /\
          Seq.mem (fp <: obj_addr) (MH.major_objects res.major_out))))
  =
  CheneyPreservation.chunked_promote_object_head_split_preserves_chunked_alloc_shape
    minor mh obj fp wosize fuel

let spot_chunked_promote_object_head_split_preserves_chain_objects_blue
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
        GenInv.chunked_chain_objects_blue mh fp fuel /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2)
      (ensures
        (let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor mh obj fp wosize fuel in
         res.new_addr == fp /\
         res.fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape res.major_out res.fp_out fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_out res.fp_out fuel = true /\
         GenInv.chunked_chain_objects_blue res.major_out res.fp_out fuel))
  =
  CheneyPreservation.chunked_promote_object_head_split_preserves_chain_objects_blue
    minor mh obj fp wosize fuel

let spot_chunked_promote_object_head_split_preserves_old_non_blue_header
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  (src: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
        GenInv.chunked_chain_objects_blue mh fp fuel /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2 /\
        Seq.mem src (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address src) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (Obj.getWosize hdr) >= 1)
      (ensures
        (let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor mh obj fp wosize fuel in
         MH.read_word_in_major res.major_out (hd_address src) == Some hdr))
  =
  CheneyPreservation.chunked_promote_object_head_split_preserves_old_non_blue_header
    minor mh obj fp wosize fuel src hdr

let spot_chunked_promote_object_head_split_preserves_old_non_blue_field
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  (src: obj_addr) (hdr: U64.t) (j: nat) (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
        GenInv.chunked_chain_objects_blue mh fp fuel /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2 /\
        Seq.mem src (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address src) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        j < U64.v (Obj.getWosize hdr) /\
        U64.v field_addr == U64.v src + j * U64.v mword /\
        MH.read_word_in_major mh field_addr == Some old)
      (ensures
        (let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor mh obj fp wosize fuel in
         MH.read_word_in_major res.major_out field_addr == Some old))
  =
  CheneyPreservation.chunked_promote_object_head_split_preserves_old_non_blue_field
    minor mh obj fp wosize fuel src hdr j field_addr old

let spot_chunked_promote_object_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  (remaining: nat)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        remaining > 0 /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >=
          wosize + 1 + remaining)
      (ensures
        (let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor mh obj fp wosize fuel in
         res.new_addr == fp /\
         res.fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape res.major_out res.fp_out fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_out res.fp_out fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           res.major_out res.fp_out >= remaining))
  =
  CheneyPreservation.chunked_promote_object_head_split_preserves_remaining_head_wosize
    minor mh obj fp wosize fuel remaining

let spot_alloc_spec_head_split_alloc_wosize_single_chunk
  (major: heap) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 0 /\
                fp <> 0UL /\
                SpecMajorAlloc.major_fl_valid
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_above_zero
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_blocks_fit
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >= wosize + 2)
      (ensures
        (let r = SpecAlloc.alloc_spec major fp wosize in
         r.obj_out == fp /\
         r.fp_out <> 0UL /\
         U64.v (Obj.wosize_of_object (fp <: obj_addr) r.heap_out) == wosize /\
         U64.v fp + (wosize - 1) * U64.v mword + U64.v mword <= heap_size))
  =
  CheneyPreservation.alloc_spec_head_split_alloc_wosize_single_chunk
    major fp wosize

let spot_promote_object_head_split_padding_noop_single_chunk
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 0 /\
                fp <> 0UL /\
                SpecMajorAlloc.major_fl_valid
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_above_zero
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_blocks_fit
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >= wosize + 2)
      (ensures
        (let r = SpecAlloc.alloc_spec major fp wosize in
         let copied = WriteBody.copy_fields minor r.heap_out obj fp 0 wosize in
         zero_promote_padding copied (fp <: obj_addr) wosize == copied))
  =
  CheneyPreservation.promote_object_head_split_padding_noop_single_chunk
    minor major obj fp wosize

let spot_promote_object_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                fp <> 0UL /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >= wosize + 2)
      (ensures
        (let res = promote_object minor major obj fp wosize in
         res.new_addr == fp /\
         res.fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap res.major_out) res.fp_out
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap res.major_out) res.fp_out
           SpecAlloc.alloc_search_fuel = true))
  =
  CheneyPreservation.promote_object_head_split_preserves_chunked_alloc_shape_single_chunk
    minor major obj fp wosize

let spot_promote_object_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                fp <> 0UL /\
                remaining > 0 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                wosize + 1 + remaining)
      (ensures
        (let res = promote_object minor major obj fp wosize in
         res.new_addr == fp /\
         res.fp_out <> 0UL /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap res.major_out) res.fp_out >=
         remaining))
  =
  CheneyPreservation.promote_object_head_split_preserves_remaining_head_wosize_single_chunk
    minor major obj fp wosize remaining

let spot_cheney_forward_one_split_ready_from_minor_demand_single_chunk
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires minor_wf minor /\
                cs.cs_fp <> 0UL /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        CheneyPreservation.cheney_forward_one_split_ready_single_chunk
          minor cs addr)
  =
  CheneyPreservation.cheney_forward_one_split_ready_from_minor_demand_single_chunk
    minor cs addr

let spot_cheney_forward_one_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                (Seq.mem addr (minor_objects minor) /\
                 cs.cs_fwd addr = 0UL /\
                 ~(is_infix_in_minor minor addr) /\
                 minor_wosize minor addr > 0 ==>
                   cs.cs_fp <> 0UL /\
                   SpecMajorAlloc.major_fl_head_wosize
                     (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                   minor_wosize minor addr + 2) /\
                (cs.cs_fwd addr = 0UL /\
                 is_infix_in_minor minor addr ==>
                   (let parent = infix_parent minor addr in
                    Seq.mem parent (minor_objects minor) /\
                    cs.cs_fwd parent = 0UL /\
                    minor_wosize minor parent > 0 ==>
                      cs.cs_fp <> 0UL /\
                      SpecMajorAlloc.major_fl_head_wosize
                        (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                      minor_wosize minor parent + 2)))
      (ensures
        (let cs' = cheney_forward_one minor cs addr in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true))
  =
  CheneyPreservation.cheney_forward_one_head_split_preserves_chunked_alloc_shape_single_chunk
    minor cs addr

let spot_cheney_forward_one_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_forward_one_budget_ready_single_chunk
                  minor cs addr remaining)
      (ensures
        (let cs' = cheney_forward_one minor cs addr in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
         remaining))
  =
  CheneyPreservation.cheney_forward_one_head_split_preserves_remaining_head_wosize_single_chunk
    minor cs addr remaining

let spot_cheney_forward_one_budget_ready_from_split_demand_single_chunk
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (remaining: nat)
  : Lemma
      (requires remaining > 0 /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                CheneyPreservation.cheney_forward_one_split_demand
                  minor cs addr + remaining)
      (ensures
        CheneyPreservation.cheney_forward_one_budget_ready_single_chunk
          minor cs addr remaining)
  =
  CheneyPreservation.cheney_forward_one_budget_ready_from_split_demand_single_chunk
    minor cs addr remaining

let spot_cheney_forward_roots_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (cs: cheney_state) (roots: Seq.seq U64.t) (idx: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_forward_roots_split_ready_single_chunk
                  minor cs roots idx)
      (ensures
        (let cs' = cheney_forward_roots minor cs roots idx in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true))
  =
  CheneyPreservation.cheney_forward_roots_head_split_preserves_chunked_alloc_shape_single_chunk
    minor cs roots idx

let spot_cheney_forward_roots_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (cs: cheney_state) (roots: Seq.seq U64.t) (idx: nat)
  (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_forward_roots_budget_ready_single_chunk
                  minor cs roots idx remaining)
      (ensures
        (let cs' = cheney_forward_roots minor cs roots idx in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
         remaining))
  =
  CheneyPreservation.cheney_forward_roots_head_split_preserves_remaining_head_wosize_single_chunk
    minor cs roots idx remaining

let spot_cheney_forward_roots_budget_ready_from_split_demand_single_chunk
  (minor: minor_state) (cs: cheney_state) (roots: Seq.seq U64.t) (idx: nat)
  (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                remaining > 0 /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                CheneyPreservation.cheney_forward_roots_split_demand
                  minor cs roots idx + remaining)
      (ensures
        CheneyPreservation.cheney_forward_roots_budget_ready_single_chunk
          minor cs roots idx remaining)
  =
  CheneyPreservation.cheney_forward_roots_budget_ready_from_split_demand_single_chunk
    minor cs roots idx remaining

let spot_cheney_forward_fields_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_forward_fields_split_ready_single_chunk
                  minor cs parent idx wosize)
      (ensures
        (let cs' = cheney_forward_fields minor cs parent idx wosize in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true))
  =
  CheneyPreservation.cheney_forward_fields_head_split_preserves_chunked_alloc_shape_single_chunk
    minor cs parent idx wosize

let spot_cheney_forward_fields_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_forward_fields_budget_ready_single_chunk
                  minor cs parent idx wosize remaining)
      (ensures
        (let cs' = cheney_forward_fields minor cs parent idx wosize in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
         remaining))
  =
  CheneyPreservation.cheney_forward_fields_head_split_preserves_remaining_head_wosize_single_chunk
    minor cs parent idx wosize remaining

let spot_cheney_forward_fields_budget_ready_from_split_demand_single_chunk
  (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                remaining > 0 /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                CheneyPreservation.cheney_forward_fields_split_demand
                  minor cs parent idx wosize + remaining)
      (ensures
        CheneyPreservation.cheney_forward_fields_budget_ready_single_chunk
          minor cs parent idx wosize remaining)
  =
  CheneyPreservation.cheney_forward_fields_budget_ready_from_split_demand_single_chunk
    minor cs parent idx wosize remaining

let spot_cheney_scan_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (cs: cheney_state) (scan fuel: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_scan_split_ready_single_chunk
                  minor cs scan fuel)
      (ensures
        (let cs' = cheney_scan minor cs scan fuel in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true))
  =
  CheneyPreservation.cheney_scan_head_split_preserves_chunked_alloc_shape_single_chunk
    minor cs scan fuel

let spot_cheney_scan_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (cs: cheney_state) (scan fuel remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_scan_budget_ready_single_chunk
                  minor cs scan fuel remaining)
      (ensures
        (let cs' = cheney_scan minor cs scan fuel in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
         remaining))
  =
  CheneyPreservation.cheney_scan_head_split_preserves_remaining_head_wosize_single_chunk
    minor cs scan fuel remaining

let spot_cheney_scan_budget_ready_from_split_demand_single_chunk
  (minor: minor_state) (cs: cheney_state) (scan fuel remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                remaining > 0 /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                CheneyPreservation.cheney_scan_split_demand
                  minor cs scan fuel + remaining)
      (ensures
        CheneyPreservation.cheney_scan_budget_ready_single_chunk
          minor cs scan fuel remaining)
  =
  CheneyPreservation.cheney_scan_budget_ready_from_split_demand_single_chunk
    minor cs scan fuel remaining

let spot_cheney_promote_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_promote_split_ready_single_chunk
                  minor major fp roots)
      (ensures
        (let res = cheney_promote minor major fp roots in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel = true))
  =
  CheneyPreservation.cheney_promote_head_split_preserves_chunked_alloc_shape_single_chunk
    minor major fp roots

let spot_cheney_promote_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_promote_budget_ready_single_chunk
                  minor major fp roots remaining)
      (ensures
        (let res = cheney_promote minor major fp roots in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap res.major_final) res.fp_final >=
         remaining))
  =
  CheneyPreservation.cheney_promote_head_split_preserves_remaining_head_wosize_single_chunk
    minor major fp roots remaining

let spot_cheney_promote_budget_ready_from_split_demand_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                remaining > 0 /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                CheneyPreservation.cheney_promote_split_demand
                  minor major fp roots + remaining)
      (ensures
        CheneyPreservation.cheney_promote_budget_ready_single_chunk
          minor major fp roots remaining)
  =
  CheneyPreservation.cheney_promote_budget_ready_from_split_demand_single_chunk
    minor major fp roots remaining

let spot_cheney_promote_budget_ready_from_minor_demand_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma
      (requires minor_wf minor /\
                SpecAlloc.alloc_search_fuel > 1 /\
                fp <> 0UL /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        CheneyPreservation.cheney_promote_budget_ready_single_chunk
          minor major fp roots 1)
  =
  CheneyPreservation.cheney_promote_budget_ready_from_minor_demand_single_chunk
    minor major fp roots

let spot_cheney_promote_budgeted_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma
      (requires minor_wf minor /\
                SpecAlloc.alloc_search_fuel > 1 /\
                fp <> 0UL /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                  PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let res = cheney_promote minor major fp roots in
         let requests =
           CheneyPreservation.cheney_forwarded_minor_requests
             minor major fp roots in
         let alloc_trace =
           SpecMajorAllocMultiAlloc.dense_alloc_list_default_spec
             major fp requests in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           alloc_trace.dense_list_objs_out))
  =
  CheneyPreservation.cheney_promote_budgeted_head_split_preserves_chunked_alloc_shape_single_chunk
    minor major fp roots

let spot_cheney_promote_after_minor_promotion_head_preflight_no_expansion_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires minor_wf minor /\
                SpecAlloc.alloc_search_fuel > 1 /\
                fp <> 0UL /\
                GenInv.chunked_collection_heap_shape
                  minor (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                  PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             (MH.single_chunk_major_heap major) fp
             SpecAlloc.alloc_search_fuel needed fresh in
         let res = cheney_promote minor major fp roots in
         let requests =
           CheneyPreservation.cheney_forwarded_minor_requests
             minor major fp roots in
         let alloc_trace =
           SpecMajorAllocMultiAlloc.dense_alloc_list_default_spec
             major fp requests in
         r.capacity_major_out == MH.single_chunk_major_heap major /\
         r.capacity_fp_out == fp /\
         r.capacity_fuel_out == SpecAlloc.alloc_search_fuel /\
         GenInv.chunked_collection_heap_shape
           minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_chain_terminates
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out = true /\
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           alloc_trace.dense_list_objs_out))
  =
  CheneyPreservation.cheney_promote_after_minor_promotion_head_preflight_no_expansion_single_chunk
    minor major fp roots fresh

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

let spot_chunked_classify_minor_field_minor
  (ms: minor_state) (mh: MH.major_heap) (v: U64.t)
  : Lemma
      (requires
        (let vo = to_minor_offset v in
         is_minor_addr vo /\ Seq.mem vo (minor_objects ms)))
      (ensures
        CG.chunked_classify_minor_field ms mh v ==
        Some (CG.MinorV (to_minor_offset v)))
  =
  CG.chunked_classify_minor_field_minor ms mh v

let spot_chunked_minor_field_edge_intro_full
  (ms: minor_state) (mh: MH.major_heap)
  (src: U64.t) (i: nat) (dst: CG.combined_vertex)
  : Lemma
      (requires Seq.mem src (minor_objects ms) /\
                i < minor_wosize ms src /\
                CG.chunked_classify_minor_field
                  ms mh (minor_read_field ms src i) == Some dst)
      (ensures
        CG.mem_ce (CG.MinorV src, dst)
          (CG.build_chunked_combined_graph ms mh))
  =
  CG.chunked_minor_field_edge_intro_full ms mh src i dst

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

let spot_chunked_update_major_pointers_single_chunk_compat
  (major: heap) (fwd: forwarding_map)
  : Lemma
      (ensures
        ChunkedUpdate.chunked_update_major_pointers
          (MH.single_chunk_major_heap major) fwd ==
        MH.single_chunk_major_heap (update_major_pointers major fwd))
  =
  ChunkedUpdate.chunked_update_major_pointers_single_chunk_compat major fwd

let spot_chunked_update_major_pointers_preserves_wf_and_major_objects
  (major: MH.major_heap) (fwd: forwarding_map)
  : Lemma
      (requires MH.well_formed_major_heap major)
      (ensures
        MH.well_formed_major_heap
          (ChunkedUpdate.chunked_update_major_pointers major fwd) /\
        MH.major_objects
          (ChunkedUpdate.chunked_update_major_pointers major fwd) ==
          MH.major_objects major)
  =
  ChunkedUpdate.chunked_update_major_pointers_preserves_wf_and_major_objects
    major fwd

let spot_chunked_update_field_preserves_read_disjoint
  (major: MH.major_heap) (field_addr addr: hp_addr)
  (old: U64.t) (fwd: forwarding_map)
  : Lemma
      (requires MH.well_formed_major_heap major /\
                MH.read_word_in_major major addr == Some old /\
                ChunkedUpdate.chunked_words_disjoint field_addr addr)
      (ensures
        MH.well_formed_major_heap
          (ChunkedUpdate.chunked_update_field major field_addr fwd) /\
        MH.read_word_in_major
          (ChunkedUpdate.chunked_update_field major field_addr fwd)
          addr == Some old)
  =
  ChunkedUpdate.chunked_update_field_preserves_wf_and_read_disjoint
    major field_addr addr old fwd

let spot_chunked_update_field_effect
  (major: MH.major_heap) (field_addr: hp_addr) (old: U64.t)
  (fwd: forwarding_map)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        MH.read_word_in_major major field_addr == Some old)
      (ensures
        (let old_val = to_minor_offset old in
         let updated = ChunkedUpdate.chunked_update_field major field_addr fwd in
         (is_minor_pointer old_val /\ fwd old_val <> 0UL ==>
          MH.read_word_in_major updated field_addr == Some (fwd old_val)) /\
         (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==>
          MH.read_word_in_major updated field_addr == Some old)))
  =
  ChunkedUpdate.chunked_update_field_effect major field_addr old fwd

let spot_chunked_update_field_slot_in_object_chunk
  (major: MH.major_heap) (obj: obj_addr) (i: nat) (field_addr: hp_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        Seq.mem obj (MH.major_objects major) /\
        i < ChunkedUpdate.chunked_wosize_nat_of_object major obj /\
        ChunkedUpdate.chunked_update_field_slot obj i == Some field_addr)
      (ensures
        (let idx = MH.lookup_chunk_index_value major (hd_address obj) in
        MH.lookup_chunk_index major (hd_address obj) == Some idx /\
        idx < Seq.length major /\
        MH.word_in_chunk (Seq.index major idx) (hd_address obj) /\
        MH.word_in_chunk (Seq.index major idx) field_addr /\
        MH.lookup_chunk_index major field_addr == Some idx))
  =
  ChunkedUpdate.chunked_update_field_slot_in_object_chunk
    major obj i field_addr

let spot_chunked_update_object_pointers_preserves_read_disjoint
  (major: MH.major_heap) (obj: obj_addr) (wosize: nat)
  (fwd: forwarding_map) (i: nat) (addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        MH.read_word_in_major major addr == Some old /\
        (forall (k:nat) (field_addr:hp_addr).
          i <= k /\ k < wosize /\
          ChunkedUpdate.chunked_update_field_slot obj k == Some field_addr ==>
          ChunkedUpdate.chunked_words_disjoint field_addr addr))
      (ensures
        (let major' =
           ChunkedUpdate.chunked_update_object_pointers
             major obj wosize fwd i in
         MH.well_formed_major_heap major' /\
         MH.read_word_in_major major' addr == Some old))
  =
  ChunkedUpdate.chunked_update_object_pointers_preserves_read_disjoint
    major obj wosize fwd i addr old

let spot_chunked_update_object_pointers_field_effect
  (major: MH.major_heap) (obj: obj_addr) (wosize: nat)
  (fwd: forwarding_map) (i: nat) (j: nat) (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        Seq.mem obj (MH.major_objects major) /\
        wosize == ChunkedUpdate.chunked_wosize_nat_of_object major obj /\
        i <= j /\ j < wosize /\
        ChunkedUpdate.chunked_update_field_slot obj j == Some field_addr /\
        MH.read_word_in_major major field_addr == Some old)
      (ensures
        (let major' =
           ChunkedUpdate.chunked_update_object_pointers
             major obj wosize fwd i in
         let old_val = to_minor_offset old in
         MH.well_formed_major_heap major' /\
         MH.major_objects major' == MH.major_objects major /\
         ChunkedUpdate.chunked_header_of_object major' obj ==
           ChunkedUpdate.chunked_header_of_object major obj /\
         (is_minor_pointer old_val /\ fwd old_val <> 0UL ==>
          MH.read_word_in_major major' field_addr == Some (fwd old_val)) /\
         (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==>
          MH.read_word_in_major major' field_addr == Some old)))
  =
  ChunkedUpdate.chunked_update_object_pointers_field_effect
    major obj wosize fwd i j field_addr old

let spot_chunked_update_major_pointers_preserves_header
  (major: MH.major_heap) (fwd: forwarding_map) (h: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        Seq.mem h (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address h) == Some hdr)
      (ensures
        MH.read_word_in_major
          (ChunkedUpdate.chunked_update_major_pointers major fwd)
          (hd_address h) == Some hdr)
  =
  ChunkedUpdate.chunked_update_major_pointers_preserves_header
    major fwd h hdr

let spot_chunked_update_major_pointers_preserves_blue_field
  (major: MH.major_heap) (fwd: forwarding_map) (h: obj_addr) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        Seq.mem h (MH.major_objects major) /\
        ChunkedUpdate.chunked_is_blue major h /\
        j < ChunkedUpdate.chunked_wosize_nat_of_object major h /\
        ChunkedUpdate.chunked_update_field_slot h j == Some field_addr /\
        MH.read_word_in_major major field_addr == Some old)
      (ensures
        MH.read_word_in_major
          (ChunkedUpdate.chunked_update_major_pointers major fwd)
          field_addr == Some old)
  =
  ChunkedUpdate.chunked_update_major_pointers_preserves_blue_field
    major fwd h j field_addr old

let spot_chunked_update_major_pointers_preserves_no_scan_field
  (major: MH.major_heap) (fwd: forwarding_map) (h: obj_addr) (hdr: U64.t)
  (j: nat) (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        Seq.mem h (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address h) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (Obj.getTag hdr) >= U64.v Obj.no_scan_tag /\
        j < U64.v (Obj.getWosize hdr) /\
        U64.v field_addr == U64.v h + j * U64.v mword /\
        MH.read_word_in_major major field_addr == Some old)
      (ensures
        MH.read_word_in_major
          (ChunkedUpdate.chunked_update_major_pointers major fwd)
          field_addr == Some old)
  =
  ChunkedUpdate.chunked_update_major_pointers_preserves_no_scan_field
    major fwd h hdr j field_addr old

let spot_chunked_update_major_pointers_field_effect_stable
  (major: MH.major_heap) (fwd: forwarding_map) (h: obj_addr) (hdr: U64.t)
  (j: nat) (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        Seq.mem h (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address h) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
        j < U64.v (Obj.getWosize hdr) /\
        U64.v field_addr == U64.v h + j * U64.v mword /\
        MH.read_word_in_major major field_addr == Some old /\
        ChunkedUpdate.chunked_update_value_stable fwd
          (ChunkedUpdate.chunked_update_expected_value fwd old))
      (ensures
        MH.read_word_in_major
          (ChunkedUpdate.chunked_update_major_pointers major fwd)
          field_addr ==
        Some (ChunkedUpdate.chunked_update_expected_value fwd old))
  =
  ChunkedUpdate.chunked_update_major_pointers_field_effect_stable
    major fwd h hdr j field_addr old

let spot_chunked_chain_objects_blue_elim
  (major: MH.major_heap) (fp: U64.t) (fuel: nat) (obj: obj_addr)
  : Lemma
      (requires GenInv.chunked_chain_objects_blue major fp fuel /\
                Seq.mem obj (MH.major_objects major) /\
                ~(GenInv.chunked_is_blue major obj))
      (ensures
        SpecMajorAlloc.major_fl_chain_avoids major fp obj fuel = true)
  =
  GenInv.chunked_chain_objects_blue_elim major fp fuel obj

let spot_chunked_chain_objects_blue_preserved_by_expansion
  (major: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_chain_objects_blue major fp fuel /\
        MH.well_formed_major_heap major /\
        SpecMajorAlloc.major_fl_valid major fp fuel /\
        SpecMajorAlloc.major_fl_above_zero major fp fuel /\
        MH.chunk_disjoint_from_all fresh major)
      (ensures
        (let r = SpecMajorAlloc.expand_major_heap major fresh fp in
         GenInv.chunked_chain_objects_blue r.major_out r.fp_out (fuel + 1)))
  =
  GenInv.chunked_chain_objects_blue_preserved_by_expansion
    major fresh fp fuel

let spot_chunked_chain_objects_blue_ensure_head_capacity
  (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        GenInv.chunked_chain_objects_blue major fp fuel /\
        MH.well_formed_major_heap major /\
        SpecMajorAlloc.major_fl_valid major fp fuel /\
        SpecMajorAlloc.major_fl_above_zero major fp fuel /\
        (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
         MH.chunk_disjoint_from_all fresh major))
      (ensures
        (let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp fuel needed fresh in
         GenInv.chunked_chain_objects_blue
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))
  =
  GenInv.chunked_chain_objects_blue_ensure_head_capacity
    major fp fuel needed fresh

let spot_chunked_update_major_pointers_preserves_alloc_shape
  (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (fwd: forwarding_map)
  : Lemma
      (requires
        GenInv.chunked_major_alloc_shape major fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates major fp fuel = true /\
        GenInv.chunked_chain_objects_blue major fp fuel)
      (ensures
        (let updated =
           ChunkedUpdate.chunked_update_major_pointers major fwd in
         GenInv.chunked_major_alloc_shape updated fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates updated fp fuel = true /\
         GenInv.chunked_chain_objects_blue updated fp fuel))
  =
  CheneyPreservation.chunked_update_major_pointers_preserves_alloc_shape
    major fp fuel fwd

let spot_chunked_cheney_collect_default_single_chunk_compat
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma
      (ensures
        (let chunked =
           ChunkedCheney.chunked_cheney_collect_spec
             minor (MH.single_chunk_major_heap major) fp roots
             SpecAlloc.alloc_search_fuel in
         let dense = cheney_collect_spec minor major fp roots in
         chunked.cmc_major == MH.single_chunk_major_heap dense.mc_major /\
         chunked.cmc_fp == dense.mc_fp /\
         chunked.cmc_minor == dense.mc_minor /\
         chunked.cmc_roots == dense.mc_roots /\
         chunked.cmc_fwd == dense.mc_fwd))
  =
  ChunkedCheney.chunked_cheney_collect_default_single_chunk_compat
    minor major fp roots

let spot_chunked_cheney_collect_after_minor_promotion_head_preflight
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        (SpecMajorAlloc.major_fl_head_wosize major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          MH.chunk_disjoint_from_all fresh major /\
          fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
          U64.v fresh.base >= U64.v zero_addr /\
          SpecMajorAlloc.fresh_chunk_wosize fresh >=
            PromotionDemand.minor_promotion_demand minor + 1 /\
          CG.chunked_all_major_object_expansion_safe
            major fresh (MH.major_objects major) 0))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let prom =
           ChunkedCheney.chunked_cheney_promote
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         collect.cmc_fp == prom.fp_final /\
         collect.cmc_minor == minor_reset minor /\
         minor_wf collect.cmc_minor /\
         U64.v collect.cmc_minor.bump == 0 /\
         collect.cmc_roots == rewrite_roots roots prom.fwd_map /\
         collect.cmc_fwd == prom.fwd_map /\
         CheneyPreservation.chunked_fwd_targets_above_minor collect.cmc_fwd /\
         CheneyPreservation.chunked_fwd_targets_valid_addr collect.cmc_fwd /\
         GenInv.chunked_major_alloc_shape
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_chain_terminates
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out = true /\
         GenInv.chunked_chain_objects_blue
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out /\
         (forall (src: obj_addr).
          Seq.mem src (MH.major_objects major) ==>
          Seq.mem src (MH.major_objects collect.cmc_major)) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          Seq.mem src (MH.major_objects major) /\
          MH.read_word_in_major major (hd_address src) == Some hdr /\
          Obj.getColor hdr <> GC.Lib.Header.Blue /\
          U64.v (Obj.getWosize hdr) >= 1 ==>
          MH.read_word_in_major collect.cmc_major (hd_address src) ==
            Some hdr) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          forall (j:nat). forall (field_addr: hp_addr).
          forall (old: U64.t).
          Seq.mem src (MH.major_objects major) /\
          MH.read_word_in_major major (hd_address src) == Some hdr /\
          Obj.getColor hdr <> GC.Lib.Header.Blue /\
          j < U64.v (Obj.getWosize hdr) /\
          U64.v field_addr == U64.v src + j * U64.v mword /\
          MH.read_word_in_major major field_addr == Some old /\
          (U64.v (Obj.getTag hdr) >= U64.v Obj.no_scan_tag \/
           ~(is_minor_pointer (to_minor_offset old) /\
             collect.cmc_fwd (to_minor_offset old) <> 0UL)) ==>
          MH.read_word_in_major collect.cmc_major field_addr == Some old) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          forall (j:nat). forall (field_addr: hp_addr).
          forall (old: U64.t).
          Seq.mem src (MH.major_objects major) /\
          MH.read_word_in_major major (hd_address src) == Some hdr /\
          Obj.getColor hdr <> GC.Lib.Header.Blue /\
          U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
          j < U64.v (Obj.getWosize hdr) /\
          U64.v field_addr == U64.v src + j * U64.v mword /\
          MH.read_word_in_major major field_addr == Some old ==>
          MH.read_word_in_major collect.cmc_major field_addr ==
            Some (ChunkedUpdate.chunked_update_expected_value
              collect.cmc_fwd old)) /\
         (forall (x:U64.t).
          Seq.mem x (minor_reachable minor roots) /\
          minor_wosize minor x > 0 ==>
          collect.cmc_fwd x <> 0UL)))
  =
  CheneyPreservation.chunked_cheney_collect_after_minor_promotion_head_preflight
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_collect_after_preflight_forwards_reachable
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        (SpecMajorAlloc.major_fl_head_wosize major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          MH.chunk_disjoint_from_all fresh major /\
          fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
          U64.v fresh.base >= U64.v zero_addr /\
          SpecMajorAlloc.fresh_chunk_wosize fresh >=
            PromotionDemand.minor_promotion_demand minor + 1 /\
          CG.chunked_all_major_object_expansion_safe
            major fresh (MH.major_objects major) 0))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         forall (x: U64.t). Seq.mem x (minor_reachable minor roots) ==>
           collect.cmc_fwd x <> 0UL \/ minor_wosize minor x = 0))
  =
  CheneyCorrectness.chunked_cheney_collect_after_preflight_forwards_reachable
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_minor_successor_forwarded
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src dst: U64.t) (j: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        (SpecMajorAlloc.major_fl_head_wosize major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          MH.chunk_disjoint_from_all fresh major /\
          fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
          U64.v fresh.base >= U64.v zero_addr /\
          SpecMajorAlloc.fresh_chunk_wosize fresh >=
            PromotionDemand.minor_promotion_demand minor + 1 /\
          CG.chunked_all_major_object_expansion_safe
            major fresh (MH.major_objects major) 0) /\
        Seq.mem src (minor_reachable minor roots) /\
        j < minor_wosize minor src /\
        to_minor_offset (minor_read_field minor src j) == dst /\
        is_minor_addr dst /\
        Seq.mem dst (minor_objects minor) /\
        minor_wosize minor dst > 0)
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         CG.mem_ce (CG.MinorV src, CG.MinorV dst)
           (CG.build_chunked_combined_graph minor major) /\
         collect.cmc_fwd src <> 0UL /\
         collect.cmc_fwd dst <> 0UL))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_minor_successor_forwarded
    minor major fp roots alloc_fuel fresh src dst j

let spot_chunked_cheney_gc_correct_after_preflight
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        (SpecMajorAlloc.major_fl_head_wosize major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          MH.chunk_disjoint_from_all fresh major /\
          fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
          U64.v fresh.base >= U64.v zero_addr /\
          SpecMajorAlloc.fresh_chunk_wosize fresh >=
            PromotionDemand.minor_promotion_demand minor + 1 /\
          CG.chunked_all_major_object_expansion_safe
            major fresh (MH.major_objects major) 0))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let prom =
           ChunkedCheney.chunked_cheney_promote
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         collect.cmc_fp == prom.fp_final /\
         collect.cmc_minor == minor_reset minor /\
         minor_wf collect.cmc_minor /\
         U64.v collect.cmc_minor.bump == 0 /\
         collect.cmc_roots == rewrite_roots roots prom.fwd_map /\
         collect.cmc_fwd == prom.fwd_map /\
         CheneyPreservation.chunked_fwd_targets_above_minor collect.cmc_fwd /\
         CheneyPreservation.chunked_fwd_targets_valid_addr collect.cmc_fwd /\
         GenInv.chunked_major_alloc_shape
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_chain_terminates
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out = true /\
         GenInv.chunked_chain_objects_blue
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out /\
         (forall (src: obj_addr).
           Seq.mem src (MH.major_objects major) ==>
           Seq.mem src (MH.major_objects collect.cmc_major)) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
           Seq.mem src (MH.major_objects major) /\
           MH.read_word_in_major major (hd_address src) == Some hdr /\
           Obj.getColor hdr <> GC.Lib.Header.Blue /\
           U64.v (Obj.getWosize hdr) >= 1 ==>
           MH.read_word_in_major collect.cmc_major (hd_address src) ==
             Some hdr) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          forall (j:nat). forall (field_addr: hp_addr).
          forall (old: U64.t).
          Seq.mem src (MH.major_objects major) /\
          MH.read_word_in_major major (hd_address src) == Some hdr /\
          Obj.getColor hdr <> GC.Lib.Header.Blue /\
          j < U64.v (Obj.getWosize hdr) /\
          U64.v field_addr == U64.v src + j * U64.v mword /\
          MH.read_word_in_major major field_addr == Some old /\
          (U64.v (Obj.getTag hdr) >= U64.v Obj.no_scan_tag \/
           ~(is_minor_pointer (to_minor_offset old) /\
             collect.cmc_fwd (to_minor_offset old) <> 0UL)) ==>
          MH.read_word_in_major collect.cmc_major field_addr == Some old) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          forall (j:nat). forall (field_addr: hp_addr).
          forall (old: U64.t).
          Seq.mem src (MH.major_objects major) /\
          MH.read_word_in_major major (hd_address src) == Some hdr /\
          Obj.getColor hdr <> GC.Lib.Header.Blue /\
          U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
          j < U64.v (Obj.getWosize hdr) /\
          U64.v field_addr == U64.v src + j * U64.v mword /\
          MH.read_word_in_major major field_addr == Some old ==>
          MH.read_word_in_major collect.cmc_major field_addr ==
            Some (ChunkedUpdate.chunked_update_expected_value
              collect.cmc_fwd old)) /\
         (forall (x: U64.t). Seq.mem x (minor_reachable minor roots) ==>
           collect.cmc_fwd x <> 0UL \/ minor_wosize minor x = 0)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_old_major_field_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src expected: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        (SpecMajorAlloc.major_fl_head_wosize major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          MH.chunk_disjoint_from_all fresh major /\
          fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
          U64.v fresh.base >= U64.v zero_addr /\
          SpecMajorAlloc.fresh_chunk_wosize fresh >=
            PromotionDemand.minor_promotion_demand minor + 1 /\
          CG.chunked_all_major_object_expansion_safe
            major fresh (MH.major_objects major) 0) /\
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         Seq.mem src (MH.major_objects major) /\
         MH.read_word_in_major major (hd_address src) == Some hdr /\
         Obj.getColor hdr <> GC.Lib.Header.Blue /\
         U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
         j < U64.v (Obj.getWosize hdr) /\
         U64.v field_addr == U64.v src + j * U64.v mword /\
         CG.chunked_major_field_slot src j == Some field_addr /\
         MH.read_word_in_major major field_addr == Some old /\
         ChunkedUpdate.chunked_update_expected_value collect.cmc_fwd old ==
           expected /\
         Seq.mem expected (MH.major_objects collect.cmc_major)))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         CG.mem_ce (CG.MajorV src, CG.MajorV expected)
          (CG.build_chunked_combined_graph
            collect.cmc_minor collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_old_major_field_edge
    minor major fp roots alloc_fuel fresh src expected hdr j field_addr old

let spot_chunked_cheney_gc_correct_after_preflight_old_major_nonforwarded_field_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src dst: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        (SpecMajorAlloc.major_fl_head_wosize major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          MH.chunk_disjoint_from_all fresh major /\
          fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
          U64.v fresh.base >= U64.v zero_addr /\
          SpecMajorAlloc.fresh_chunk_wosize fresh >=
            PromotionDemand.minor_promotion_demand minor + 1 /\
          CG.chunked_all_major_object_expansion_safe
            major fresh (MH.major_objects major) 0) /\
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         Seq.mem src (MH.major_objects major) /\
         Seq.mem dst (MH.major_objects major) /\
         MH.read_word_in_major major (hd_address src) == Some hdr /\
         Obj.getColor hdr <> GC.Lib.Header.Blue /\
         U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
         j < U64.v (Obj.getWosize hdr) /\
         U64.v field_addr == U64.v src + j * U64.v mword /\
         CG.chunked_major_field_slot src j == Some field_addr /\
         MH.read_word_in_major major field_addr == Some old /\
         old == dst /\
         ~(is_minor_pointer (to_minor_offset old) /\
           collect.cmc_fwd (to_minor_offset old) <> 0UL)))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         CG.mem_ce (CG.MajorV src, CG.MajorV dst)
          (CG.build_chunked_combined_graph
            collect.cmc_minor collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_old_major_nonforwarded_field_edge
    minor major fp roots alloc_fuel fresh src dst hdr j field_addr old

let spot_chunked_cheney_gc_correct_after_preflight_old_major_forwarded_minor_field_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src expected: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        (SpecMajorAlloc.major_fl_head_wosize major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          MH.chunk_disjoint_from_all fresh major /\
          fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
          U64.v fresh.base >= U64.v zero_addr /\
          SpecMajorAlloc.fresh_chunk_wosize fresh >=
            PromotionDemand.minor_promotion_demand minor + 1 /\
          CG.chunked_all_major_object_expansion_safe
            major fresh (MH.major_objects major) 0) /\
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         let x = to_minor_offset old in
         Seq.mem src (MH.major_objects major) /\
         MH.read_word_in_major major (hd_address src) == Some hdr /\
         Obj.getColor hdr <> GC.Lib.Header.Blue /\
         U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
         j < U64.v (Obj.getWosize hdr) /\
         U64.v field_addr == U64.v src + j * U64.v mword /\
         CG.chunked_major_field_slot src j == Some field_addr /\
         MH.read_word_in_major major field_addr == Some old /\
         is_minor_pointer x /\
         collect.cmc_fwd x <> 0UL /\
         collect.cmc_fwd x == expected /\
         Seq.mem expected (MH.major_objects collect.cmc_major)))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         let x = to_minor_offset old in
         CG.mem_ce (CG.MajorV src, CG.MajorV expected)
          (CG.build_chunked_combined_graph
            collect.cmc_minor collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_old_major_forwarded_minor_field_edge
    minor major fp roots alloc_fuel fresh src expected hdr j field_addr old
