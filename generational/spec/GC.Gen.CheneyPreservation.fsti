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
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SpecMajorAllocSplitShape = GC.Spec.MajorAllocator.SplitShape
module SpecMajorAllocMultiAlloc = GC.Spec.MajorAllocator.MultiAlloc

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

/// One Cheney forwarding step preserves the chunked allocator shape and chain
/// termination, assuming the normal object that may be promoted by that step
/// has enough active-head capacity to split.
val cheney_forward_one_split_ready_single_chunk
  : minor:minor_state -> cs:cheney_state -> addr:U64.t -> GTot prop

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
