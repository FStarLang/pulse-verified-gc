/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation — Additional Cheney BFS preservation lemmas
/// ---------------------------------------------------------------------------
///
/// Separated from GC.Gen.Cheney to avoid Z3 context pollution: adding val
/// declarations to Cheney.fsti causes GC.Gen.Impl.Cheney.fst to fail verification.
/// The Pulse implementation imports this module explicitly for post-minor
/// heap-shape preservation facts.

module GC.Gen.CheneyPreservation

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module MarkBounded = GC.Spec.MarkBounded
module GenInv = GC.Gen.HeapInvariant
module FreeListShape = GC.Gen.FreeListShape
module PromotionDemand = GC.Gen.PromotionDemand
module MH = GC.Spec.MajorHeap
module CG = GC.Gen.CombinedGraph
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SpecMajorAllocSplitShape = GC.Spec.MajorAllocator.SplitShape
module SpecMajorAllocMultiAlloc = GC.Spec.MajorAllocator.MultiAlloc
module ChunkedPromote = GC.Gen.ChunkedPromote
module ChunkedCheney = GC.Gen.ChunkedCheney
module ChunkedUpdate = GC.Gen.ChunkedUpdate
module CheneyBFS = GC.Gen.CheneyBFS

/// Size-only allocation request trace induced by Cheney's final forwarding map.
///
/// The list is ordered by `minor_objects`, not BFS discovery order.  It is meant
/// as a conservative bridge to the preflight demand bound: it includes exactly
/// those normal minor-object starts that ended up forwarded, excludes infix
/// interior entries because those are not members of `minor_objects`, and is a
/// filtered sub-demand of `minor_promotion_requests`.
val cheney_forwarded_minor_requests
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    GTot (list nat)

val cheney_forwarded_minor_requests_positive
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    Lemma
      (requires minor_wf minor)
      (ensures
        SpecMajorAllocMultiAlloc.all_requests_positive
          (cheney_forwarded_minor_requests minor major fp roots))

val cheney_forwarded_minor_requests_demand_bound
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    Lemma
      (ensures
        SpecMajorAllocMultiAlloc.allocation_list_demand
          (cheney_forwarded_minor_requests minor major fp roots) <=
        PromotionDemand.minor_promotion_demand minor)

/// Size-only allocation demand for normal minor objects that are still
/// unforwarded in an intermediate Cheney state.
val cheney_unforwarded_split_demand
  : minor:minor_state -> cs:cheney_state -> GTot nat

val cheney_unforwarded_split_demand_bound
  : minor:minor_state -> cs:cheney_state ->
    Lemma
      (ensures
        cheney_unforwarded_split_demand minor cs <=
        PromotionDemand.minor_promotion_demand minor)

val cheney_forwarded_dense_alloc_list_single_chunk_no_oom
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    fuel:nat ->
    Lemma
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
           cheney_forwarded_minor_requests minor major fp roots in
         let r =
           SpecMajorAllocMultiAlloc.dense_alloc_list_spec
             major fp fuel requests in
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.dense_list_objs_out))

val cheney_forwarded_dense_alloc_list_default_single_chunk_no_oom
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    Lemma
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
           cheney_forwarded_minor_requests minor major fp roots in
         let r =
           SpecMajorAllocMultiAlloc.dense_alloc_list_default_spec
             major fp requests in
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.dense_list_objs_out))

/// If the active single-chunk free-list head can satisfy the request, the
/// actual promotion boundary cannot observe allocator OOM.
val promote_object_head_no_oom_single_chunk
  : minor:minor_state -> major:heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} ->
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
        (promote_object minor major obj fp wosize).new_addr <> 0UL)

/// Preflight for the full conservative minor-promotion demand is enough for
/// any single normal minor-object promotion request at the initial head.
val promote_minor_object_head_no_oom_single_chunk
  : minor:minor_state -> major:heap -> obj:U64.t -> fp:U64.t ->
    wosize:nat{wosize > 0} ->
    Lemma
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

/// The chunked-major promotion primitive agrees with dense promotion in the
/// single active-chunk compatibility instance.
val chunked_promote_object_default_single_chunk_compat
  : minor:minor_state -> major:heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} ->
    Lemma
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

/// The first chunked Cheney forwarding step agrees with the dense Cheney step
/// in the single active-chunk compatibility instance.
val chunked_cheney_forward_normal_default_single_chunk_compat
  : minor:minor_state -> cs:cheney_state -> addr:U64.t ->
    Lemma
      (ensures
        ChunkedCheney.chunked_cheney_forward_normal
          minor (ChunkedCheney.single_chunk_cheney_state cs) addr
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_forward_normal minor cs addr))

val chunked_cheney_forward_one_default_single_chunk_compat
  : minor:minor_state -> cs:cheney_state -> addr:U64.t ->
    Lemma
      (ensures
        ChunkedCheney.chunked_cheney_forward_one
          minor (ChunkedCheney.single_chunk_cheney_state cs) addr
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_forward_one minor cs addr))

val chunked_cheney_forward_fields_default_single_chunk_compat
  : minor:minor_state -> cs:cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat ->
    Lemma
      (ensures
        ChunkedCheney.chunked_cheney_forward_fields
          minor (ChunkedCheney.single_chunk_cheney_state cs) parent idx wosize
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_forward_fields minor cs parent idx wosize))

val chunked_cheney_forward_roots_default_single_chunk_compat
  : minor:minor_state -> cs:cheney_state ->
    roots:seq U64.t -> idx:nat ->
    Lemma
      (ensures
        ChunkedCheney.chunked_cheney_forward_roots
          minor (ChunkedCheney.single_chunk_cheney_state cs) roots idx
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_forward_roots minor cs roots idx))

val chunked_cheney_scan_default_single_chunk_compat
  : minor:minor_state -> cs:cheney_state -> scan:nat -> scan_fuel:nat ->
    Lemma
      (ensures
        ChunkedCheney.chunked_cheney_scan
          minor (ChunkedCheney.single_chunk_cheney_state cs) scan scan_fuel
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_scan minor cs scan scan_fuel))

val chunked_cheney_promote_default_single_chunk_compat
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    Lemma
      (ensures
        (let chunked =
           ChunkedCheney.chunked_cheney_promote
             minor (MH.single_chunk_major_heap major) fp roots
             SpecAlloc.alloc_search_fuel in
         let dense = cheney_promote minor major fp roots in
         chunked.major_final == MH.single_chunk_major_heap dense.major_final /\
         chunked.fp_final == dense.fp_final /\
         chunked.fwd_map == dense.fwd_map))

/// Direct chunked preservation for the no-allocation branches of normal Cheney
/// forwarding.  This is the reusable case split for future full chunked
/// allocator-shape preservation: when forwarding returns the input state
/// (already forwarded, not a minor object, zero-sized object, or promotion OOM),
/// allocator shape and free-list chain termination carry over unchanged.
val chunked_cheney_forward_normal_noalloc_preserves_chunked_alloc_shape
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    addr:U64.t -> fuel:nat ->
    Lemma
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

val chunked_alloc_head_split_alloc_header_wosize
  : mh:MH.major_heap -> fp:U64.t ->
    requested_wz:nat{requested_wz > 0 /\
                     requested_wz < pow2 54 /\
                     FStar.UInt.size requested_wz 64} ->
    fuel:nat ->
    Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= requested_wz + 2)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             mh fp requested_wz fuel in
         let dst : obj_addr = fp in
         r.major_obj_out == fp /\
         r.major_fp_out <> 0UL /\
         MH.read_word_in_major r.major_alloc_out (hd_address dst) ==
           Some (SpecAlloc.make_header (U64.uint_to_t requested_wz)
                   SpecAlloc.white_bits 0UL) /\
         U64.v (getWosize
           (SpecAlloc.make_header (U64.uint_to_t requested_wz)
             SpecAlloc.white_bits 0UL)) == requested_wz))

val chunked_promote_head_split_padding_noop
  : minor:minor_state -> mh:MH.major_heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} -> fuel:nat ->
    Lemma
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

/// A head block with at least two spare words forces dense `alloc_spec` down
/// the split path, so the allocated object's wosize is exactly the request.
val alloc_spec_head_split_alloc_wosize_single_chunk
  : major:heap -> fp:U64.t -> wosize:nat{wosize > 0} ->
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
                  (MH.single_chunk_major_heap major) fp >= wosize + 2)
      (ensures
        (let r = SpecAlloc.alloc_spec major fp wosize in
         r.obj_out == fp /\
         r.fp_out <> 0UL /\
         Seq.mem (fp <: obj_addr) (objects zero_addr r.heap_out) /\
         U64.v (wosize_of_object (fp <: obj_addr) r.heap_out) == wosize /\
         U64.v fp + (wosize - 1) * U64.v mword + U64.v mword <= heap_size))

/// In the guaranteed split case, promotion's padding phase is a no-op; the
/// split remainder header at the new free-list head is therefore not clobbered.
val promote_object_head_split_padding_noop_single_chunk
  : minor:minor_state -> major:heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} ->
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
                  (MH.single_chunk_major_heap major) fp >= wosize + 2)
      (ensures
        (let r = SpecAlloc.alloc_spec major fp wosize in
         let copied = copy_fields minor r.heap_out obj fp 0 wosize in
         zero_promote_padding copied (fp <: obj_addr) wosize == copied))

/// Direct chunked-major analogue of the split-promotion preservation theorem:
/// after active-head split allocation, the chunked promotion writes preserve the
/// allocator shape rooted at the split remainder head.
val chunked_promote_object_head_split_preserves_chunked_alloc_shape
  : minor:minor_state -> mh:MH.major_heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} -> fuel:nat ->
    Lemma
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
          res.fp_out == alloc_res.major_fp_out /\
          MH.major_objects res.major_out ==
            MH.major_objects alloc_res.major_alloc_out /\
          (forall (src:obj_addr).
            Seq.mem src (MH.major_objects mh) ==>
            Seq.mem src (MH.major_objects res.major_out)) /\
          (forall (src:obj_addr). forall (hdr:U64.t).
            Seq.mem src (MH.major_objects mh) /\
            src <> fp /\
            MH.read_word_in_major mh (hd_address src) == Some hdr /\
            U64.v (getWosize hdr) >= 1 ==>
            MH.read_word_in_major res.major_out (hd_address src) ==
              Some hdr) /\
          (forall (src:obj_addr). forall (hdr:U64.t).
           forall (j:nat). forall (field_addr:hp_addr).
           forall (old:U64.t).
            Seq.mem src (MH.major_objects mh) /\
            src <> fp /\
            MH.read_word_in_major mh (hd_address src) == Some hdr /\
            j < U64.v (getWosize hdr) /\
            U64.v field_addr == U64.v src + j * U64.v mword /\
            MH.read_word_in_major mh field_addr == Some old ==>
            MH.read_word_in_major res.major_out field_addr == Some old) /\
          Seq.mem (fp <: obj_addr)
            (MH.major_objects alloc_res.major_alloc_out) /\
          Seq.mem (fp <: obj_addr) (MH.major_objects res.major_out) /\
          (forall (src:obj_addr).
            Seq.mem src (MH.major_objects alloc_res.major_alloc_out) /\
            src <> fp ==>
            MH.read_word_in_major res.major_out (hd_address src) ==
            MH.read_word_in_major alloc_res.major_alloc_out
              (hd_address src)) /\
          (forall (src:obj_addr).
            Seq.mem src (MH.major_objects alloc_res.major_alloc_out) /\
            src <> fp /\
            (match MH.read_word_in_major
               alloc_res.major_alloc_out (hd_address src)
             with
             | Some hdr -> U64.v (getWosize hdr) >= 1
             | None -> False) ==>
            MH.read_word_in_major res.major_out src ==
            MH.read_word_in_major alloc_res.major_alloc_out src))))

val chunked_promote_object_head_split_preserves_chain_objects_blue
  : minor:minor_state -> mh:MH.major_heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} -> fuel:nat ->
    Lemma
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

val chunked_promote_object_head_split_preserves_old_non_blue_header
  : minor:minor_state -> mh:MH.major_heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} -> fuel:nat ->
    src:obj_addr -> hdr:U64.t ->
    Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
        GenInv.chunked_chain_objects_blue mh fp fuel /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2 /\
        Seq.mem src (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (getWosize hdr) >= 1)
      (ensures
        (let res =
         ChunkedPromote.chunked_promote_object_with_fuel
           minor mh obj fp wosize fuel in
         MH.read_word_in_major res.major_out (hd_address src) == Some hdr))

val chunked_promote_object_head_split_preserves_old_non_blue_field
  : minor:minor_state -> mh:MH.major_heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} -> fuel:nat ->
    src:obj_addr -> hdr:U64.t -> j:nat -> field_addr:hp_addr ->
    old:U64.t ->
    Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
        GenInv.chunked_chain_objects_blue mh fp fuel /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2 /\
        Seq.mem src (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue /\
        j < U64.v (getWosize hdr) /\
        U64.v field_addr == U64.v src + j * U64.v mword /\
        MH.read_word_in_major mh field_addr == Some old)
      (ensures
        (let res =
         ChunkedPromote.chunked_promote_object_with_fuel
          minor mh obj fp wosize fuel in
         MH.read_word_in_major res.major_out field_addr == Some old))

val chunked_promote_object_head_split_preserves_remaining_head_wosize
  : minor:minor_state -> mh:MH.major_heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} -> fuel:nat ->
    remaining:nat ->
    Lemma
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

/// Direct chunked preservation for normal Cheney forwarding when any required
/// promotion is guaranteed to split the active free-list head.
val chunked_cheney_forward_normal_head_split_preserves_chunked_alloc_shape
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    addr:U64.t -> fuel:nat ->
    Lemma
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

val chunked_cheney_forward_normal_head_split_preserves_chain_objects_blue
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    addr:U64.t -> fuel:nat ->
    Lemma
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

/// One chunked Cheney forwarding step preserves allocator shape when any
/// possible normal promotion from the step splits the active free-list head.
val chunked_cheney_forward_one_head_split_preserves_chunked_alloc_shape
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    addr:U64.t -> fuel:nat ->
    Lemma
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

val chunked_cheney_forward_one_head_split_preserves_chain_objects_blue
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    addr:U64.t -> fuel:nat ->
    Lemma
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

val chunked_cheney_forward_one_budget_ready
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    addr:U64.t -> remaining:nat -> GTot prop

val chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    addr:U64.t -> fuel:nat -> remaining:nat ->
    Lemma
      (requires
        fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        chunked_cheney_forward_one_budget_ready
          minor cs addr remaining)
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
          cs'.ccs_major cs'.ccs_fp fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
          cs'.ccs_major cs'.ccs_fp >= remaining))

val chunked_cheney_forward_one_split_ready
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    addr:U64.t -> GTot prop

val chunked_cheney_forward_roots_split_ready
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    roots:seq U64.t -> idx:nat -> alloc_fuel:nat -> GTot prop

val chunked_cheney_forward_roots_head_split_preserves_chunked_alloc_shape
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    roots:seq U64.t -> idx:nat -> alloc_fuel:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        chunked_cheney_forward_roots_split_ready
          minor cs roots idx alloc_fuel)
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_roots
            minor cs roots idx alloc_fuel in
         GenInv.chunked_major_alloc_shape
          cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
          cs'.ccs_major cs'.ccs_fp alloc_fuel = true))

val chunked_cheney_forward_roots_head_split_preserves_chain_objects_blue
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    roots:seq U64.t -> idx:nat -> alloc_fuel:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        chunked_cheney_forward_roots_split_ready
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

val chunked_cheney_forward_roots_budget_ready
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    roots:seq U64.t -> idx:nat -> alloc_fuel:nat -> remaining:nat ->
    GTot prop

val chunked_cheney_forward_roots_head_split_preserves_remaining_head_wosize
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    roots:seq U64.t -> idx:nat -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        chunked_cheney_forward_roots_budget_ready
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

val chunked_cheney_forward_fields_split_ready
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> alloc_fuel:nat ->
    GTot prop

val chunked_cheney_forward_fields_head_split_preserves_chunked_alloc_shape
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> alloc_fuel:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        chunked_cheney_forward_fields_split_ready
          minor cs parent idx wosize alloc_fuel)
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent idx wosize alloc_fuel in
         GenInv.chunked_major_alloc_shape
          cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
          cs'.ccs_major cs'.ccs_fp alloc_fuel = true))

val chunked_cheney_forward_fields_head_split_preserves_chain_objects_blue
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> alloc_fuel:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        chunked_cheney_forward_fields_split_ready
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

val chunked_cheney_forward_fields_budget_ready
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> alloc_fuel:nat ->
    remaining:nat -> GTot prop

val chunked_cheney_forward_fields_head_split_preserves_remaining_head_wosize
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> alloc_fuel:nat ->
    remaining:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        chunked_cheney_forward_fields_budget_ready
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

val chunked_cheney_scan_split_ready
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    scan:nat -> scan_fuel:nat -> alloc_fuel:nat -> GTot prop

val chunked_cheney_scan_head_split_preserves_chunked_alloc_shape
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    scan:nat -> scan_fuel:nat -> alloc_fuel:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        chunked_cheney_scan_split_ready
          minor cs scan scan_fuel alloc_fuel)
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel in
         GenInv.chunked_major_alloc_shape
          cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
          cs'.ccs_major cs'.ccs_fp alloc_fuel = true))

val chunked_cheney_scan_head_split_preserves_chain_objects_blue
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    scan:nat -> scan_fuel:nat -> alloc_fuel:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        chunked_cheney_scan_split_ready
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

val chunked_cheney_scan_budget_ready
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    scan:nat -> scan_fuel:nat -> alloc_fuel:nat -> remaining:nat ->
    GTot prop

val chunked_cheney_scan_head_split_preserves_remaining_head_wosize
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    scan:nat -> scan_fuel:nat -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        chunked_cheney_scan_budget_ready
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

val chunked_cheney_promote_split_ready
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> GTot prop

val chunked_cheney_promote_head_split_preserves_chunked_alloc_shape
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel)
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         GenInv.chunked_major_alloc_shape
          res.major_final res.fp_final alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
          res.major_final res.fp_final alloc_fuel = true))

val chunked_cheney_promote_head_split_preserves_chain_objects_blue
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        chunked_cheney_promote_split_ready
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

val chunked_cheney_promote_head_split_preserves_old_major_objects
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel)
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         forall (src: obj_addr).
          Seq.mem src (MH.major_objects major) ==>
          Seq.mem src (MH.major_objects res.major_final)))

val chunked_cheney_promote_head_split_preserves_old_non_blue_header
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> src:obj_addr -> hdr:U64.t ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (getWosize hdr) >= 1)
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final (hd_address src) ==
           Some hdr))

val chunked_cheney_promote_head_split_preserves_old_non_blue_field
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> src:obj_addr -> hdr:U64.t ->
    j:nat -> field_addr:hp_addr -> old:U64.t ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue /\
        j < U64.v (getWosize hdr) /\
        U64.v field_addr == U64.v src + j * U64.v mword /\
        MH.read_word_in_major major field_addr == Some old)
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final field_addr == Some old))

val chunked_cheney_promote_budget_ready
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat -> GTot prop

val chunked_cheney_promote_head_split_preserves_remaining_head_wosize
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        chunked_cheney_promote_budget_ready
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

val chunked_cheney_forward_one_fwd_monotone
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    addr:U64.t -> x:U64.t -> alloc_fuel:nat ->
    Lemma
      (requires cs.ccs_fwd x <> 0UL)
      (ensures
        (ChunkedCheney.chunked_cheney_forward_one
         minor cs addr alloc_fuel).ccs_fwd x <> 0UL)

val chunked_cheney_forward_fields_fwd_monotone
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> alloc_fuel:nat -> x:U64.t ->
    Lemma
      (requires cs.ccs_fwd x <> 0UL)
      (ensures
        (ChunkedCheney.chunked_cheney_forward_fields
          minor cs parent idx wosize alloc_fuel).ccs_fwd x <> 0UL)

val chunked_cheney_forward_roots_fwd_monotone
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    roots:seq U64.t -> idx:nat -> alloc_fuel:nat -> x:U64.t ->
    Lemma
      (requires cs.ccs_fwd x <> 0UL)
      (ensures
        (ChunkedCheney.chunked_cheney_forward_roots
         minor cs roots idx alloc_fuel).ccs_fwd x <> 0UL)

val chunked_cheney_scan_fwd_monotone
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    scan:nat -> scan_fuel:nat -> alloc_fuel:nat -> x:U64.t ->
    Lemma
      (requires cs.ccs_fwd x <> 0UL)
      (ensures
        (ChunkedCheney.chunked_cheney_scan
          minor cs scan scan_fuel alloc_fuel).ccs_fwd x <> 0UL)

val chunked_cheney_forward_one_covers_addr_from_budget
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    addr:U64.t -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
         cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
         cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        chunked_cheney_forward_one_budget_ready
         minor cs addr remaining)
      (ensures
        Seq.mem addr (minor_objects minor) /\
        minor_wosize minor addr > 0 ==>
        (ChunkedCheney.chunked_cheney_forward_one
         minor cs addr alloc_fuel).ccs_fwd addr <> 0UL)

val chunked_cheney_forward_roots_covers_roots_from_budget
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
         cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
         cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        chunked_cheney_forward_roots_budget_ready
         minor cs roots 0 alloc_fuel remaining)
      (ensures
        CheneyBFS.fwd_covers_roots minor
         (ChunkedCheney.chunked_cheney_forward_roots
           minor cs roots 0 alloc_fuel).ccs_fwd
         roots)

val chunked_cheney_forward_fields_covers_successors_from_budget
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    parent:U64.t -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        chunked_cheney_forward_fields_budget_ready
          minor cs parent 0 (minor_wosize minor parent) alloc_fuel remaining)
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent 0 (minor_wosize minor parent) alloc_fuel in
         forall (y:U64.t).
          Seq.mem y (minor_successors minor parent) /\
          minor_wosize minor y > 0 ==>
          cs'.ccs_fwd y <> 0UL))

[@"opaque_to_smt"]
val chunked_scanned_prefix_closed
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    scan:nat -> GTot prop

val chunked_scanned_prefix_empty
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    Lemma
      (ensures chunked_scanned_prefix_closed minor cs 0)

val chunked_scanned_prefix_step_from_budget
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    scan:nat -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        chunked_scanned_prefix_closed minor cs scan /\
        scan < Seq.length cs.ccs_queue /\
        (let parent = Seq.index cs.ccs_queue scan in
         chunked_cheney_forward_fields_budget_ready
          minor cs parent 0 (minor_wosize minor parent)
          alloc_fuel remaining))
      (ensures
        (let parent = Seq.index cs.ccs_queue scan in
         let cs' =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent 0 (minor_wosize minor parent) alloc_fuel in
         chunked_scanned_prefix_closed minor cs' (scan + 1)))

val chunked_cheney_scan_end_index
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    scan:nat -> scan_fuel:nat -> alloc_fuel:nat -> GTot nat

val chunked_cheney_scan_end_exhausted_or_fuel
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    scan:nat -> scan_fuel:nat -> alloc_fuel:nat ->
    Lemma
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
         let end_idx =
           chunked_cheney_scan_end_index
             minor cs scan scan_fuel alloc_fuel in
         end_idx >= Seq.length cs'.ccs_queue \/
         end_idx == scan + scan_fuel))

val chunked_cheney_scan_scanned_prefix_from_budget
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    scan:nat -> scan_fuel:nat -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
           cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
           cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        chunked_scanned_prefix_closed minor cs scan /\
        chunked_cheney_scan_budget_ready
           minor cs scan scan_fuel alloc_fuel remaining)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
          chunked_scanned_prefix_closed minor cs'
           (chunked_cheney_scan_end_index
             minor cs scan scan_fuel alloc_fuel)))

[@"opaque_to_smt"]
val chunked_fwd_in_queue
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    GTot prop

val chunked_fwd_in_queue_elim
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    x:U64.t ->
    Lemma
      (requires
        chunked_fwd_in_queue minor cs /\
        Seq.mem x (minor_objects minor) /\
        cs.ccs_fwd x <> 0UL)
      (ensures Seq.mem x cs.ccs_queue)

val chunked_fwd_in_queue_initial
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    Lemma
      (requires cs.ccs_queue == Seq.empty /\
                 cs.ccs_fwd == empty_forwarding)
      (ensures chunked_fwd_in_queue minor cs)

val chunked_cheney_forward_one_preserves_fwd_in_queue
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    addr:U64.t -> alloc_fuel:nat ->
    Lemma
      (requires minor_wf minor /\
                 chunked_fwd_in_queue minor cs)
      (ensures
        chunked_fwd_in_queue minor
           (ChunkedCheney.chunked_cheney_forward_one
             minor cs addr alloc_fuel))

val chunked_cheney_forward_fields_preserves_fwd_in_queue
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> alloc_fuel:nat ->
    Lemma
      (requires minor_wf minor /\
                 chunked_fwd_in_queue minor cs)
      (ensures
        chunked_fwd_in_queue minor
           (ChunkedCheney.chunked_cheney_forward_fields
             minor cs parent idx wosize alloc_fuel))

val chunked_cheney_forward_roots_preserves_fwd_in_queue
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    roots:seq U64.t -> idx:nat -> alloc_fuel:nat ->
    Lemma
      (requires minor_wf minor /\
                 chunked_fwd_in_queue minor cs)
      (ensures
        chunked_fwd_in_queue minor
           (ChunkedCheney.chunked_cheney_forward_roots
             minor cs roots idx alloc_fuel))

val chunked_cheney_scan_preserves_fwd_in_queue
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    scan:nat -> scan_fuel:nat -> alloc_fuel:nat ->
    Lemma
      (requires minor_wf minor /\
                 chunked_fwd_in_queue minor cs)
      (ensures
        chunked_fwd_in_queue minor
           (ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel))

val chunked_scanned_exhausted_implies_fwd_closed
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    scan:nat ->
    Lemma
      (requires
        chunked_fwd_in_queue minor cs /\
        chunked_scanned_prefix_closed minor cs scan /\
        scan >= Seq.length cs.ccs_queue)
      (ensures CheneyBFS.fwd_closed minor cs.ccs_fwd)

val chunked_cheney_scan_fwd_closed_from_budget
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    scan:nat -> scan_fuel:nat -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        chunked_fwd_in_queue minor cs /\
        chunked_scanned_prefix_closed minor cs scan /\
        chunked_cheney_scan_budget_ready
          minor cs scan scan_fuel alloc_fuel remaining /\
        (let cs' =
          ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel in
         chunked_cheney_scan_end_index
          minor cs scan scan_fuel alloc_fuel >= Seq.length cs'.ccs_queue))
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel in
         CheneyBFS.fwd_closed minor cs'.ccs_fwd))

val chunked_cheney_promote_scan_exhaustion
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    Lemma
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
         chunked_cheney_scan_end_index
          minor cs1 0 (cheney_fuel minor) alloc_fuel >=
         Seq.length cs2.ccs_queue))

val chunked_cheney_promote_budget_ready_from_minor_demand
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    Lemma
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
        chunked_cheney_promote_budget_ready
         minor major fp roots alloc_fuel 1)

val chunked_cheney_scan_preserves_fwd_covers_roots
  : minor:minor_state -> cs:ChunkedCheney.chunked_cheney_state ->
    roots:seq U64.t -> scan:nat -> scan_fuel:nat -> alloc_fuel:nat ->
    Lemma
      (requires CheneyBFS.fwd_covers_roots minor cs.ccs_fwd roots)
      (ensures
        CheneyBFS.fwd_covers_roots minor
          (ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel).ccs_fwd
          roots)

val chunked_cheney_no_oom
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> GTot prop

val chunked_cheney_promote_no_oom_from_budget_and_scan_exhaustion
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    Lemma
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
         chunked_cheney_scan_end_index
          minor cs1 0 (cheney_fuel minor) alloc_fuel >=
         Seq.length cs2.ccs_queue))
      (ensures
        chunked_cheney_no_oom minor major fp roots alloc_fuel)

val chunked_cheney_promote_no_oom_from_budget
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    Lemma
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
        chunked_cheney_no_oom minor major fp roots alloc_fuel)

val chunked_cheney_promote_forwards_reachable_from_budget
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    Lemma
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

val chunked_cheney_promote_after_minor_promotion_head_preflight
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> fresh:MH.heap_chunk ->
    Lemma
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
          getColor hdr <> GC.Lib.Header.Blue /\
          U64.v (getWosize hdr) >= 1 ==>
          MH.read_word_in_major res.major_final (hd_address src) ==
            Some hdr) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          forall (j:nat). forall (field_addr: hp_addr).
          forall (old: U64.t).
           Seq.mem src (MH.major_objects major) /\
           MH.read_word_in_major major (hd_address src) == Some hdr /\
           getColor hdr <> GC.Lib.Header.Blue /\
           j < U64.v (getWosize hdr) /\
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

/// Chunked major-pointer update skips blue objects, so it preserves the global
/// blue free-list chain when the chain-blue side invariant is available.
val chunked_update_major_pointers_preserves_alloc_shape
  : major:MH.major_heap -> fp:U64.t -> alloc_fuel:nat ->
    fwd:forwarding_map ->
    Lemma
      (requires
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
         major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel)
      (ensures
        (let updated =
          ChunkedUpdate.chunked_update_major_pointers major fwd in
         GenInv.chunked_major_alloc_shape updated fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
          updated fp alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue updated fp alloc_fuel))

val chunked_cheney_collect_after_minor_promotion_head_preflight
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> fresh:MH.heap_chunk ->
    Lemma
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
         getColor hdr <> GC.Lib.Header.Blue /\
         U64.v (getWosize hdr) >= 1 ==>
         MH.read_word_in_major collect.cmc_major (hd_address src) ==
          Some hdr) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          forall (j:nat). forall (field_addr: hp_addr).
          forall (old: U64.t).
          Seq.mem src (MH.major_objects major) /\
          MH.read_word_in_major major (hd_address src) == Some hdr /\
          getColor hdr <> GC.Lib.Header.Blue /\
          j < U64.v (getWosize hdr) /\
          U64.v field_addr == U64.v src + j * U64.v mword /\
          MH.read_word_in_major major field_addr == Some old /\
          (U64.v (getTag hdr) >= U64.v no_scan_tag \/
           ~(is_minor_pointer (to_minor_offset old) /\
            collect.cmc_fwd (to_minor_offset old) <> 0UL)) ==>
          MH.read_word_in_major collect.cmc_major field_addr == Some old) /\
         (forall (x:U64.t).
         Seq.mem x (minor_reachable minor roots) /\
         minor_wosize minor x > 0 ==>
         collect.cmc_fwd x <> 0UL)))

/// In the active-head split case, the allocation creates a post-split
/// remainder head.  The subsequent promotion writes (field copy + tag update;
/// padding is a no-op in this case) preserve the chunked allocator shape rooted
/// at that remainder head for the single dense-heap compatibility chunk.
val promote_object_head_split_preserves_chunked_alloc_shape_single_chunk
  : minor:minor_state -> major:heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} ->
    Lemma
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

/// In the active-head split case, promotion leaves the split remainder head
/// with at least the requested positive remaining budget.
val promote_object_head_split_preserves_remaining_head_wosize_single_chunk
  : minor:minor_state -> major:heap -> obj:U64.t ->
    fp:U64.t -> wosize:nat{wosize > 0} -> remaining:nat ->
    Lemma
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

/// One Cheney forwarding step preserves the chunked allocator shape and chain
/// termination, assuming the normal object that may be promoted by that step
/// has enough active-head capacity to split.
val cheney_forward_one_split_ready_single_chunk
  : minor:minor_state -> cs:cheney_state -> addr:U64.t -> GTot prop

/// Local budget readiness for one Cheney forwarding step: the current head
/// already has the positive remaining budget, and any actual promoted normal
/// object (or infix parent) has room for its split demand plus that budget.
val cheney_forward_one_budget_ready_single_chunk
  : minor:minor_state -> cs:cheney_state -> addr:U64.t ->
    remaining:nat -> GTot prop

/// Header-inclusive split demand for the allocation that one Cheney forwarding
/// step would perform, or zero for no-op steps.
val cheney_forward_one_split_demand
  : minor:minor_state -> cs:cheney_state -> addr:U64.t -> GTot nat

val cheney_forward_one_budget_ready_from_split_demand_single_chunk
  : minor:minor_state -> cs:cheney_state -> addr:U64.t ->
    remaining:nat ->
    Lemma
      (requires remaining > 0 /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                cheney_forward_one_split_demand minor cs addr + remaining)
      (ensures
        cheney_forward_one_budget_ready_single_chunk
          minor cs addr remaining)

/// The preflight minor-promotion demand budget gives the split capacity needed
/// for any single Cheney forwarding step performed at a state whose active
/// head still carries that whole budget.
val cheney_forward_one_split_ready_from_minor_demand_single_chunk
  : minor:minor_state -> cs:cheney_state -> addr:U64.t ->
    Lemma
      (requires minor_wf minor /\
                cs.cs_fp <> 0UL /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        cheney_forward_one_split_ready_single_chunk minor cs addr)

val cheney_forward_one_head_split_preserves_chunked_alloc_shape_single_chunk
  : minor:minor_state -> cs:cheney_state -> addr:U64.t ->
    Lemma
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

val cheney_forward_one_head_split_preserves_remaining_head_wosize_single_chunk
  : minor:minor_state -> cs:cheney_state -> addr:U64.t ->
    remaining:nat ->
    Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                cheney_forward_one_budget_ready_single_chunk
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

/// Exact trace-readiness predicate for `cheney_forward_roots`: every actual
/// root step has the split-head capacity needed by the one-step theorem, after
/// applying all earlier root steps.
val cheney_forward_roots_split_ready_single_chunk
  : minor:minor_state -> cs:cheney_state -> roots:seq U64.t -> idx:nat ->
    GTot prop

val cheney_forward_roots_head_split_preserves_chunked_alloc_shape_single_chunk
  : minor:minor_state -> cs:cheney_state -> roots:seq U64.t -> idx:nat ->
    Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                cheney_forward_roots_split_ready_single_chunk
                  minor cs roots idx)
      (ensures
        (let cs' = cheney_forward_roots minor cs roots idx in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true))

/// Root-loop version of local budget readiness.
val cheney_forward_roots_budget_ready_single_chunk
  : minor:minor_state -> cs:cheney_state -> roots:seq U64.t -> idx:nat ->
    remaining:nat -> GTot prop

val cheney_forward_roots_head_split_preserves_remaining_head_wosize_single_chunk
  : minor:minor_state -> cs:cheney_state -> roots:seq U64.t -> idx:nat ->
    remaining:nat ->
    Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                cheney_forward_roots_budget_ready_single_chunk
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

/// Header-inclusive split demand for the actual root-forwarding suffix.
val cheney_forward_roots_split_demand
  : minor:minor_state -> cs:cheney_state -> roots:seq U64.t -> idx:nat ->
    GTot nat

val cheney_forward_roots_budget_ready_from_split_demand_single_chunk
  : minor:minor_state -> cs:cheney_state -> roots:seq U64.t -> idx:nat ->
    remaining:nat ->
    Lemma
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
                cheney_forward_roots_split_demand minor cs roots idx + remaining)
      (ensures
        cheney_forward_roots_budget_ready_single_chunk
          minor cs roots idx remaining)

/// Exact trace-readiness predicate for forwarding an object's fields.
val cheney_forward_fields_split_ready_single_chunk
  : minor:minor_state -> cs:cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> GTot prop

val cheney_forward_fields_head_split_preserves_chunked_alloc_shape_single_chunk
  : minor:minor_state -> cs:cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat ->
    Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                cheney_forward_fields_split_ready_single_chunk
                  minor cs parent idx wosize)
      (ensures
        (let cs' = cheney_forward_fields minor cs parent idx wosize in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true))

/// Field-loop version of local budget readiness.
val cheney_forward_fields_budget_ready_single_chunk
  : minor:minor_state -> cs:cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> remaining:nat -> GTot prop

val cheney_forward_fields_head_split_preserves_remaining_head_wosize_single_chunk
  : minor:minor_state -> cs:cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> remaining:nat ->
    Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                cheney_forward_fields_budget_ready_single_chunk
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

/// Header-inclusive split demand for the actual field-forwarding suffix.
val cheney_forward_fields_split_demand
  : minor:minor_state -> cs:cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> GTot nat

val cheney_forward_fields_budget_ready_from_split_demand_single_chunk
  : minor:minor_state -> cs:cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> remaining:nat ->
    Lemma
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
                cheney_forward_fields_split_demand
                  minor cs parent idx wosize + remaining)
      (ensures
        cheney_forward_fields_budget_ready_single_chunk
          minor cs parent idx wosize remaining)

/// Exact trace-readiness predicate for Cheney's BFS scan loop.
val cheney_scan_split_ready_single_chunk
  : minor:minor_state -> cs:cheney_state -> scan:nat -> fuel:nat ->
    GTot prop

val cheney_scan_head_split_preserves_chunked_alloc_shape_single_chunk
  : minor:minor_state -> cs:cheney_state -> scan:nat -> fuel:nat ->
    Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                cheney_scan_split_ready_single_chunk minor cs scan fuel)
      (ensures
        (let cs' = cheney_scan minor cs scan fuel in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true))

/// Scan-loop version of local budget readiness.
val cheney_scan_budget_ready_single_chunk
  : minor:minor_state -> cs:cheney_state -> scan:nat -> fuel:nat ->
    remaining:nat -> GTot prop

val cheney_scan_head_split_preserves_remaining_head_wosize_single_chunk
  : minor:minor_state -> cs:cheney_state -> scan:nat -> fuel:nat ->
    remaining:nat ->
    Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
               GenInv.chunked_major_alloc_shape
                 (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                 SpecAlloc.alloc_search_fuel /\
               SpecMajorAlloc.major_fl_chain_terminates
                 (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                 SpecAlloc.alloc_search_fuel = true /\
               cheney_scan_budget_ready_single_chunk
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

/// Header-inclusive split demand for the actual scan suffix.
val cheney_scan_split_demand
  : minor:minor_state -> cs:cheney_state -> scan:nat -> fuel:nat ->
    GTot nat

val cheney_scan_budget_ready_from_split_demand_single_chunk
  : minor:minor_state -> cs:cheney_state -> scan:nat -> fuel:nat ->
    remaining:nat ->
    Lemma
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
               cheney_scan_split_demand minor cs scan fuel + remaining)
      (ensures
        cheney_scan_budget_ready_single_chunk
          minor cs scan fuel remaining)

/// Exact trace-readiness predicate for full Cheney promotion: roots are ready
/// from the initial state, and scanning is ready after root forwarding.
val cheney_promote_split_ready_single_chunk
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    GTot prop

val cheney_promote_head_split_preserves_chunked_alloc_shape_single_chunk
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                cheney_promote_split_ready_single_chunk
                  minor major fp roots)
      (ensures
        (let res = cheney_promote minor major fp roots in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel = true))

/// Full-promotion version of local budget readiness.
val cheney_promote_budget_ready_single_chunk
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    remaining:nat -> GTot prop

val cheney_promote_head_split_preserves_remaining_head_wosize_single_chunk
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    remaining:nat ->
    Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                cheney_promote_budget_ready_single_chunk
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

/// Header-inclusive split demand for the actual full Cheney promotion trace.
val cheney_promote_split_demand
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    GTot nat

val cheney_promote_budget_ready_from_split_demand_single_chunk
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    remaining:nat ->
    Lemma
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
                cheney_promote_split_demand minor major fp roots + remaining)
      (ensures
        cheney_promote_budget_ready_single_chunk
          minor major fp roots remaining)

val cheney_promote_budget_ready_from_minor_demand_single_chunk
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    Lemma
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
        cheney_promote_budget_ready_single_chunk
          minor major fp roots 1)

/// Budgeted audit wrapper: the global minor-promotion preflight budget proves
/// both the conservative allocation trace is non-OOM and the Cheney-order
/// budget readiness needed to preserve the chunked allocator shape.
val cheney_promote_budgeted_head_split_preserves_chunked_alloc_shape_single_chunk
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    Lemma
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
          cheney_forwarded_minor_requests minor major fp roots in
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

/// Compatibility bridge from the minor-promotion head preflight to actual
/// dense Cheney promotion in the no-expansion branch.
///
/// This deliberately does not claim Cheney can run on a freshly expanded
/// multi-chunk major heap: today's Cheney spec still consumes a dense `heap`.
val cheney_promote_after_minor_promotion_head_preflight_no_expansion_single_chunk
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    fresh:MH.heap_chunk ->
    Lemma
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
          cheney_forwarded_minor_requests minor major fp roots in
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

/// Cheney promotion preserves no_black_objects.
///
/// Promoted objects get white_bits headers; pre-existing objects' colors are
/// unchanged (alloc_spec and copy_fields only modify the allocated block and
/// free-list headers, never coloring an object black).
val cheney_promote_preserves_no_black
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects major /\
                    minor_infix_wf minor)
           (ensures (let res = cheney_promote minor major fp roots in
                     Mark.no_black_objects res.major_final))

val cheney_collect_preserves_no_black
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects major /\
                    minor_infix_wf minor)
          (ensures Mark.no_black_objects
            (cheney_collect_spec minor major fp roots).mc_major)

val cheney_collect_preserves_fp_pointer_or_zero
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires GenInv.collection_heap_shape minor major fp)
          (ensures FreeListShape.fp_pointer_or_zero
            (cheney_collect_spec minor major fp roots).mc_fp)

/// All gray/black objects are present in the major gray stack.
///
/// This is the color-stack conjunct of MajorGC.gc_precondition, named so
/// Cheney promotion and the post-promotion pointer update can preserve it
/// without forcing clients to reason about Cheney's result.
let gray_black_objects_on_stack (g: heap) (st: seq obj_addr) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (objects zero_addr g) /\
    (is_gray obj g \/ is_black obj g) ==> Seq.mem obj st

val cheney_promote_preserves_gray_black_objects_on_stack
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (st: seq obj_addr)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    gray_black_objects_on_stack major st /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_promote minor major fp roots in
                    gray_black_objects_on_stack res.major_final st))

val update_major_pointers_preserves_gray_black_objects_on_stack
  (major: heap) (fwd: forwarding_map) (st: seq obj_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    gray_black_objects_on_stack major st)
          (ensures gray_black_objects_on_stack (update_major_pointers major fwd) st)

val cheney_collect_preserves_gray_black_objects_on_stack
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (st: seq obj_addr)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    gray_black_objects_on_stack major st /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_collect_spec minor major fp roots in
                    gray_black_objects_on_stack res.mc_major st))

val cheney_promote_preserves_no_scan_invariant
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    no_scan_invariant major /\
                    minor_no_scan_invariant minor /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor)
          (ensures no_scan_invariant (cheney_promote minor major fp roots).major_final)

val cheney_promote_preserves_blue_fields_closed
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor)
          (ensures blue_fields_closed (cheney_promote minor major fp roots).major_final)

val update_major_pointers_preserves_no_scan_invariant
  (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\
                    no_scan_invariant major)
          (ensures no_scan_invariant (update_major_pointers major fwd))

val cheney_collect_preserves_no_scan_invariant
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    no_scan_invariant major /\
                    minor_no_scan_invariant minor /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                     minor_infix_wf minor)
          (ensures no_scan_invariant (cheney_collect_spec minor major fp roots).mc_major)

/// ---------------------------------------------------------------------------
/// Forwarding targets classification: in objects or infix
/// ---------------------------------------------------------------------------

/// Every non-zero forwarding target produced by cheney_promote is either
/// an object in the objects list (normal forwarding) or an infix sub-object
/// in the major heap (interior pointer with tag=249).
///
/// Proof sketch (BFS induction):
///   - Normal forwarding via cheney_forward_normal: alloc_spec puts the target
///     in objects (alloc_spec_obj_in_objects_part1). Subsequent allocs preserve
///     membership (cheney_forward_one_preserves_objects).
///   - Infix forwarding: target = parent_fwd + delta. After promote_object
///     copies parent's fields, the infix header at (parent_fwd + delta - 8)
///     has tag=249. Frame: subsequent allocs write to disjoint memory
///     (promote_object_frame_old_field), preserving the infix header.
let fwd_valid_or_infix (fwd: forwarding_map) (g: heap) : prop =
  forall (x: U64.t). fwd x <> 0UL ==>
    (U64.v (fwd x) >= U64.v mword /\
     U64.v (fwd x) < heap_size /\
     U64.v (fwd x) % U64.v mword == 0 /\
     (Seq.mem ((fwd x) <: obj_addr) (objects zero_addr g) \/
      is_infix (fwd x) g))

val cheney_promote_fwd_valid_or_infix
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_valid_or_infix (cheney_promote minor major fp roots).fwd_map
                                      (cheney_promote minor major fp roots).major_final)

/// ---------------------------------------------------------------------------
/// Frame property: cheney_promote preserves fields of pre-existing non-blue objects
/// ---------------------------------------------------------------------------

/// For any non-blue object in the original major heap, its body fields are
/// unchanged after cheney_promote. This is because:
///   - Cheney BFS only writes to newly allocated regions (from the free-list)
///   - Pre-existing non-blue objects are not on the free-list
///   - promote_object_frame_old_field gives per-step field preservation
///   - BFS induction carries this through all promotion steps
val cheney_promote_frame_old_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    Seq.mem obj (objects zero_addr major) /\
                    is_blue obj major = false /\
                    j < U64.v (wosize_of_object obj major) /\
                    U64.v obj + j * 8 + 8 <= heap_size /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_promote minor major fp roots in
                    read_word res.major_final (U64.uint_to_t (U64.v obj + j * 8))
                    == read_word major (U64.uint_to_t (U64.v obj + j * 8))))

/// ---------------------------------------------------------------------------
/// Header frame: cheney_promote preserves headers of pre-existing non-blue objects
/// ---------------------------------------------------------------------------

/// For any non-blue object in the original major heap, its header is unchanged
/// after cheney_promote. This is because cheney BFS only allocates from the
/// free-list chain (blue objects), never overwriting pre-existing non-blue headers.
/// Combined with frame_old_fields, this gives complete preservation of
/// pre-existing non-blue objects through promotion.
val cheney_promote_frame_old_header
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    Seq.mem obj (objects zero_addr major) /\
                    is_blue obj major = false /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_promote minor major fp roots in
                    read_word res.major_final (hd_address obj)
                    == read_word major (hd_address obj)))

/// ---------------------------------------------------------------------------
/// Injectivity: non-infix forwarding targets are pairwise distinct
/// ---------------------------------------------------------------------------

/// The forwarding map is injective on non-infix targets: two different
/// source addresses cannot be forwarded to the same non-infix destination.
/// Proof: each successful cheney_forward_normal allocates from the free-list,
/// which advances after each allocation. From chain_objects_blue, existing
/// (non-blue) targets avoid the chain, hence differ from the next allocation
/// (which IS a chain node). By induction, all normal targets are distinct.
let fwd_normal_injective (fwd: forwarding_map) (g: heap) : prop =
  forall (x y: U64.t). fwd x <> 0UL /\ fwd y <> 0UL /\
    is_val_addr (fwd x) /\ is_val_addr (fwd y) /\
    is_infix (fwd x) g = false /\ is_infix (fwd y) g = false /\
    fwd x = fwd y ==> x = y

/// Non-infix forwarding targets produced by Cheney are normal objects, not
/// blue free-list nodes.  update_promoted_iter relies on this to agree with
/// update_major_pointers, which skips blue objects.
let fwd_targets_not_blue (fwd: forwarding_map) (g: heap) : prop =
  forall (x: U64.t). fwd x <> 0UL /\ is_val_addr (fwd x) /\
    is_infix (fwd x) g = false ==>
    Seq.mem ((fwd x) <: obj_addr) (objects zero_addr g) /\
    is_blue ((fwd x) <: obj_addr) g = false

/// Normal forwarding targets are freshly allocated from the old free-list
/// region, hence cannot equal a pre-existing non-blue major object.
let fwd_normal_targets_disjoint_from_old_nonblue
  (fwd: forwarding_map) (g_final: heap) (major0: heap) : prop =
  forall (x: U64.t) (y: obj_addr).
    fwd x <> 0UL /\
    is_val_addr (fwd x) /\
    is_infix (fwd x) g_final = false /\
    Seq.mem y (objects zero_addr major0) /\
    is_blue y major0 = false ==>
    fwd x <> y

val cheney_promote_fwd_normal_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
           (ensures fwd_normal_injective (cheney_promote minor major fp roots).fwd_map
                                         (cheney_promote minor major fp roots).major_final)

val cheney_promote_fwd_targets_not_blue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_targets_not_blue (cheney_promote minor major fp roots).fwd_map
                                        (cheney_promote minor major fp roots).major_final)

val cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_normal_targets_disjoint_from_old_nonblue
                     (cheney_promote minor major fp roots).fwd_map
                     (cheney_promote minor major fp roots).major_final
                     major)

/// ---------------------------------------------------------------------------
/// Non-blue origin: objects that become non-blue during promotion are fwd targets
/// ---------------------------------------------------------------------------

/// If an object is non-blue in major_final but was NOT a pre-existing non-blue
/// object (either wasn't in objects(major_pre) or was blue there), then it must
/// be a forwarding target — i.e., it was allocated by cheney_promote to hold
/// a promoted minor object.
///
/// Proof sketch (BFS induction): promote_object_frame_old_header_derived shows
/// only the allocated object's header changes per step. Objects whose headers
/// don't change retain their color. So: non-blue in final ∧ not-pre-nonblue → allocated → fwd target.
val cheney_promote_nonblue_origin
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: obj_addr)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor /\
                    (let res = cheney_promote minor major fp roots in
                     Seq.mem obj (objects zero_addr res.major_final) /\
                     is_blue obj res.major_final = false /\
                     ~(Seq.mem obj (objects zero_addr major) /\
                       is_blue obj major = false)))
           (ensures (let res = cheney_promote minor major fp roots in
                     exists (x: U64.t). res.fwd_map x == obj /\ is_minor_pointer x))

val cheney_collect_preserves_wfh_from_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures well_formed_heap
      (cheney_collect_spec minor major fp roots).mc_major)

val cheney_collect_preserves_no_pointer_to_blue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp /\
              well_formed_heap (cheney_collect_spec minor major fp roots).mc_major)
    (ensures Mark.no_pointer_to_blue
      (cheney_collect_spec minor major fp roots).mc_major)

val cheney_collect_preserves_collection_heap_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires GenInv.collection_heap_shape minor major fp)
          (ensures GenInv.collection_heap_shape
            (cheney_collect_spec minor major fp roots).mc_minor
            (cheney_collect_spec minor major fp roots).mc_major
            (cheney_collect_spec minor major fp roots).mc_fp)

val cheney_collect_preserves_bounded_stack_props
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (st: seq obj_addr)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    MarkBounded.bounded_stack_props major st)
          (ensures MarkBounded.bounded_stack_props
            (cheney_collect_spec minor major fp roots).mc_major st)
