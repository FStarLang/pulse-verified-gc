module GC.SPOT.HeapExpansion

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object

module MH = GC.Spec.MajorHeap
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SpecMajorAllocMultiAlloc = GC.Spec.MajorAllocator.MultiAlloc
module PromotionDemand = GC.Gen.PromotionDemand
module CheneyPreservation = GC.Gen.CheneyPreservation
module Promote = GC.Gen.Promote
module CG = GC.Gen.CombinedGraph
module GenInv = GC.Gen.HeapInvariant

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

val spot_expand_major_heap_head_wosize
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    Lemma
      (requires U64.v fresh.base >= U64.v zero_addr)
      (ensures
        (let r = SpecMajorAlloc.expand_major_heap mh fresh fp in
         SpecMajorAlloc.major_fl_head_wosize r.major_out r.fp_out ==
         SpecMajorAlloc.fresh_chunk_wosize fresh))

val spot_head_preflight_alloc_no_oom
  : mh:MH.major_heap -> fp:U64.t -> requested_wz:nat -> fuel:nat ->
    Lemma
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

val spot_ensure_head_capacity_preserves_shape_and_old_read
  : mh:MH.major_heap -> fp:U64.t -> fuel:nat -> needed:nat{needed > 0} ->
    fresh:MH.heap_chunk -> old_addr:hp_addr -> old_value:U64.t ->
    Lemma
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

val spot_ensure_head_capacity_alloc_no_oom
  : mh:MH.major_heap -> fp:U64.t -> fuel:nat ->
    requested_wz:nat -> fresh:MH.heap_chunk ->
    Lemma
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

val spot_major_alloc_after_expand_split_preserves_head_wosize
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    requested_wz:nat -> fuel:nat -> remaining:nat ->
    Lemma
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

val spot_major_alloc_head_split_preserves_head_wosize
  : mh:MH.major_heap -> fp:U64.t ->
    requested_wz:nat -> fuel:nat -> remaining:nat ->
    Lemma
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

val spot_major_alloc_head_split_link_not_self
  : mh:MH.major_heap -> fp:U64.t ->
    requested_wz:nat -> fuel:nat ->
    Lemma
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

val spot_chunked_major_alloc_shape_active_head_split
  : mh:MH.major_heap -> fp:U64.t ->
    requested_wz:nat -> fuel:nat ->
    Lemma
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

val spot_chunked_major_alloc_shape_alloc_list_head_split
  : mh:MH.major_heap -> fp:U64.t -> fuel:nat ->
    requests:list nat ->
    Lemma
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

val spot_chunked_major_alloc_shape_alloc_list_with_budget
  : mh:MH.major_heap -> fp:U64.t -> fuel:nat ->
    requests:list nat -> budget:nat ->
    Lemma
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

val spot_dense_alloc_list_single_chunk_with_budget_no_oom
  : g:heap -> fp:U64.t -> fuel:nat ->
    requests:list nat -> budget:nat ->
    Lemma
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

val spot_chunked_major_alloc_shape_alloc_minor_objects_head_split
  : minor:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat ->
    Lemma
      (requires fuel > 1 /\
                GC.Gen.MinorHeap.minor_wf minor /\
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

val spot_chunked_collection_shape_ensure_minor_promotion_allocs
  : minor:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> fresh:MH.heap_chunk ->
    Lemma
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

val spot_chunked_collection_shape_ensure_head_capacity_alloc_list_budget
  : minor:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> fresh:MH.heap_chunk ->
    requests:list nat -> budget:nat ->
    Lemma
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

val spot_chunked_collection_shape_ensure_minor_promotion_budget_alloc_list
  : minor:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> fresh:MH.heap_chunk ->
    requests:list nat ->
    Lemma
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

val spot_cheney_forwarded_minor_requests_budget
  : minor:GC.Gen.MinorHeap.minor_state -> major:heap ->
    fp:U64.t -> roots:Seq.seq U64.t ->
    Lemma
      (requires GC.Gen.MinorHeap.minor_wf minor)
      (ensures
        (let requests =
           CheneyPreservation.cheney_forwarded_minor_requests
             minor major fp roots in
         SpecMajorAllocMultiAlloc.all_requests_positive requests /\
         SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
           PromotionDemand.minor_promotion_demand minor))

val spot_cheney_forwarded_dense_alloc_list_single_chunk_no_oom
  : minor:GC.Gen.MinorHeap.minor_state -> major:heap ->
    fp:U64.t -> roots:Seq.seq U64.t -> fuel:nat ->
    Lemma
      (requires GC.Gen.MinorHeap.minor_wf minor /\
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

val spot_cheney_forwarded_dense_alloc_list_default_single_chunk_no_oom
  : minor:GC.Gen.MinorHeap.minor_state -> major:heap ->
    fp:U64.t -> roots:Seq.seq U64.t ->
    Lemma
      (requires GC.Gen.MinorHeap.minor_wf minor /\
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

val spot_promote_object_head_no_oom_single_chunk
  : minor:GC.Gen.MinorHeap.minor_state -> major:heap ->
    obj:U64.t -> fp:U64.t -> wosize:nat{wosize > 0} ->
    Lemma
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
        (Promote.promote_object minor major obj fp wosize).new_addr <> 0UL)

val spot_promote_minor_object_head_no_oom_single_chunk
  : minor:GC.Gen.MinorHeap.minor_state -> major:heap ->
    obj:U64.t -> fp:U64.t -> wosize:nat{wosize > 0} ->
    Lemma
      (requires GC.Gen.MinorHeap.minor_wf minor /\
                Seq.mem obj (GC.Gen.MinorHeap.minor_objects minor) /\
                wosize == GC.Gen.MinorHeap.minor_wosize minor obj /\
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
        (Promote.promote_object minor major obj fp wosize).new_addr <> 0UL)

val spot_chunked_is_blue_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    obj:obj_addr ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
               Seq.mem obj (MH.major_objects mh))
      (ensures
        GenInv.chunked_is_blue
         (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        GenInv.chunked_is_blue mh obj)

val spot_chunked_minor_major_fields_no_blue_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    fresh:MH.heap_chunk -> fp:U64.t ->
    Lemma
      (requires GenInv.chunked_minor_major_fields_no_blue ms mh /\
               MH.chunk_disjoint_from_all fresh mh)
      (ensures
        GenInv.chunked_minor_major_fields_no_blue ms
         (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)

val spot_chunked_minor_major_fields_no_blue_ensure_capacity
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    fp:obj_addr -> fuel:nat -> needed:nat -> fresh:MH.heap_chunk ->
    Lemma
      (requires GenInv.chunked_minor_major_fields_no_blue ms mh /\
               (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                MH.chunk_disjoint_from_all fresh mh))
      (ensures
        GenInv.chunked_minor_major_fields_no_blue ms
         (SpecMajorAlloc.ensure_major_capacity_spec
           mh fp fuel needed fresh).capacity_major_out)

val spot_chunked_is_black_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    obj:obj_addr ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
               Seq.mem obj (MH.major_objects mh))
      (ensures
        GenInv.chunked_is_black
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        GenInv.chunked_is_black mh obj)

val spot_chunked_no_black_objects_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    Lemma
      (requires GenInv.chunked_no_black_objects mh /\
               MH.chunk_disjoint_from_all fresh mh)
      (ensures
        GenInv.chunked_no_black_objects
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)

val spot_chunked_no_black_objects_ensure_capacity
  : mh:MH.major_heap ->
    fp:obj_addr -> fuel:nat -> needed:nat -> fresh:MH.heap_chunk ->
    Lemma
      (requires GenInv.chunked_no_black_objects mh /\
               (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                MH.chunk_disjoint_from_all fresh mh))
      (ensures
        GenInv.chunked_no_black_objects
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)

val spot_chunked_no_scan_invariant_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    Lemma
      (requires GenInv.chunked_no_scan_invariant mh /\
               MH.chunk_disjoint_from_all fresh mh /\
               CG.chunked_all_major_object_expansion_safe
                 mh fresh (MH.major_objects mh) 0)
      (ensures
        GenInv.chunked_no_scan_invariant
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)

val spot_chunked_no_scan_invariant_ensure_capacity
  : mh:MH.major_heap ->
    fp:obj_addr -> fuel:nat -> needed:nat -> fresh:MH.heap_chunk ->
    Lemma
      (requires GenInv.chunked_no_scan_invariant mh /\
               (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0))
      (ensures
        GenInv.chunked_no_scan_invariant
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)

val spot_chunked_no_pointer_to_blue_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    Lemma
      (requires GenInv.chunked_no_pointer_to_blue mh /\
               MH.chunk_disjoint_from_all fresh mh /\
               CG.chunked_all_major_object_expansion_safe
                 mh fresh (MH.major_objects mh) 0)
      (ensures
        GenInv.chunked_no_pointer_to_blue
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)

val spot_chunked_no_pointer_to_blue_ensure_capacity
  : mh:MH.major_heap ->
    fp:obj_addr -> fuel:nat -> needed:nat -> fresh:MH.heap_chunk ->
    Lemma
      (requires GenInv.chunked_no_pointer_to_blue mh /\
               (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0))
      (ensures
        GenInv.chunked_no_pointer_to_blue
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)

val spot_chunked_major_minor_fields_no_infix_targets_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    fresh:MH.heap_chunk -> fp:U64.t ->
    Lemma
      (requires GenInv.chunked_major_minor_fields_no_infix_targets ms mh /\
               MH.chunk_disjoint_from_all fresh mh /\
               CG.chunked_all_major_object_expansion_safe
                 mh fresh (MH.major_objects mh) 0)
      (ensures
        GenInv.chunked_major_minor_fields_no_infix_targets ms
         (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)

val spot_chunked_major_minor_fields_no_infix_targets_ensure_capacity
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    fp:obj_addr -> fuel:nat -> needed:nat -> fresh:MH.heap_chunk ->
    Lemma
      (requires GenInv.chunked_major_minor_fields_no_infix_targets ms mh /\
               (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0))
      (ensures
        GenInv.chunked_major_minor_fields_no_infix_targets ms
         (SpecMajorAlloc.ensure_major_capacity_spec
           mh fp fuel needed fresh).capacity_major_out)

val spot_chunked_collection_heap_shape_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    fresh:MH.heap_chunk -> fp:obj_addr -> fuel:nat ->
    Lemma
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

val spot_chunked_collection_heap_shape_ensure_capacity
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    fp:obj_addr -> fuel:nat -> needed:nat -> fresh:MH.heap_chunk ->
    Lemma
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

val spot_chunked_collection_heap_shape_ensure_head_capacity
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> needed:nat{needed > 0} -> fresh:MH.heap_chunk ->
    Lemma
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

val spot_chunked_collection_heap_shape_ensure_head_capacity_alloc_no_oom
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    fp:U64.t -> fuel:nat -> requested_wz:nat -> fresh:MH.heap_chunk ->
    Lemma
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

val spot_chunked_minor_field_edges
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    src:U64.t -> wz:nat -> i:nat -> GTot (Seq.seq CG.combined_edge)

val spot_chunked_minor_field_edges_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state ->
    mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    src:U64.t -> wz:nat -> i:nat ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_minor_field_expansion_safe ms fresh src wz i)
      (ensures
        spot_chunked_minor_field_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out src wz i ==
        spot_chunked_minor_field_edges ms mh src wz i)

val spot_chunked_minor_object_edges
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap -> obj:U64.t ->
    GTot (Seq.seq CG.combined_edge)

val spot_chunked_minor_object_edges_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state ->
    mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t -> obj:U64.t ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_minor_object_expansion_safe ms fresh obj)
      (ensures
        spot_chunked_minor_object_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        spot_chunked_minor_object_edges ms mh obj)

val spot_chunked_all_minor_edges
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    objs:Seq.seq U64.t -> idx:nat -> GTot (Seq.seq CG.combined_edge)

val spot_chunked_all_minor_edges_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state ->
    mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    objs:Seq.seq U64.t -> idx:nat ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_minor_expansion_safe ms fresh objs idx)
      (ensures
        spot_chunked_all_minor_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out objs idx ==
        spot_chunked_all_minor_edges ms mh objs idx)

val spot_build_chunked_combined_graph_from_major_objects
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    major_objs:Seq.seq obj_addr -> GTot CG.combined_graph

val spot_build_chunked_combined_graph
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    GTot CG.combined_graph

val spot_chunked_combined_graph_old_view_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state ->
    mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    major_objs:Seq.seq obj_addr ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_minor_expansion_safe
        ms fresh (GC.Gen.MinorHeap.minor_objects ms) 0 /\
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

val spot_chunked_build_combined_graph_old_view_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state ->
    mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_minor_expansion_safe
        ms fresh (GC.Gen.MinorHeap.minor_objects ms) 0 /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures (
        let mh' = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
        let g' =
          spot_build_chunked_combined_graph_from_major_objects
            ms mh' (MH.major_objects mh) in
        let g = spot_build_chunked_combined_graph ms mh in
        g'.cg_vertices == g.cg_vertices /\ g'.cg_edges == g.cg_edges))

val spot_chunked_old_view_reachable_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state ->
    mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    roots:Seq.seq CG.combined_vertex -> v:CG.combined_vertex ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_minor_expansion_safe
                  ms fresh (GC.Gen.MinorHeap.minor_objects ms) 0 /\
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

val spot_chunked_wosize_nat_of_object_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t -> obj:obj_addr ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_wosize_nat_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_wosize_nat_of_object mh obj)

val spot_chunked_tag_of_object_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t -> obj:obj_addr ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_tag_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_tag_of_object mh obj)

val spot_chunked_is_no_scan_preserved_by_expansion
  : mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t -> obj:obj_addr ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_is_no_scan
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_is_no_scan mh obj)

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

val spot_chunked_major_object_edges
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap -> obj:obj_addr ->
    GTot (Seq.seq CG.combined_edge)

val spot_chunked_major_object_edges_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state ->
    mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t -> obj:obj_addr ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_major_object_expansion_safe mh fresh obj)
      (ensures
        spot_chunked_major_object_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        spot_chunked_major_object_edges ms mh obj)

val spot_chunked_all_major_object_edges
  : ms:GC.Gen.MinorHeap.minor_state -> mh:MH.major_heap ->
    objs:Seq.seq obj_addr -> idx:nat -> GTot (Seq.seq CG.combined_edge)

val spot_chunked_all_major_object_edges_preserved_by_expansion
  : ms:GC.Gen.MinorHeap.minor_state ->
    mh:MH.major_heap -> fresh:MH.heap_chunk -> fp:U64.t ->
    objs:Seq.seq obj_addr -> idx:nat ->
    Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe mh fresh objs idx)
      (ensures
        spot_chunked_all_major_object_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out objs idx ==
        spot_chunked_all_major_object_edges ms mh objs idx)

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
