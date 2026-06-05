/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation — Proofs
/// ---------------------------------------------------------------------------

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
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney
open GC.Gen.WriteBodyLemmas
open GC.Lib.Header

module Allocator = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocProps = GC.Gen.AllocProps
module Mark = GC.Spec.Mark
module MarkBounded = GC.Spec.MarkBounded
module Sweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module HeapGraph = GC.Spec.HeapGraph
module GenInv = GC.Gen.HeapInvariant
module FreeListShape = GC.Gen.FreeListShape
module Frame = GC.Gen.CheneyPreservation.Frame
module Forwarding = GC.Gen.CheneyPreservation.Forwarding
module Fields = GC.Gen.CheneyPreservation.Fields
module NonBlueOrigin = GC.Gen.CheneyPreservation.NonBlueOrigin
module NoBlue = GC.Gen.CheneyPreservation.NoBlue
module BlueProm = GC.Gen.PromoteUpdate.BlueProm
module BlueAlloc = GC.Gen.PromoteUpdate.BlueAlloc
module NoBlueUtil = GC.Gen.NoBlueUtil
module PromotionDemand = GC.Gen.PromotionDemand
module MH = GC.Spec.MajorHeap
module CG = GC.Gen.CombinedGraph
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SpecMajorAllocSplitShape = GC.Spec.MajorAllocator.SplitShape
module SpecMajorAllocMultiAlloc = GC.Spec.MajorAllocator.MultiAlloc
module ChunkedPromote = GC.Gen.ChunkedPromote
module ChunkedCheney = GC.Gen.ChunkedCheney
module AllocHeader = GC.Spec.Allocator.Lemmas.Header
module IndDesc = FStar.IndefiniteDescription
module CheneyBFS = GC.Gen.CheneyBFS
module SimOne = GC.Gen.Cheney.SimOne

private let cheney_forwarded_minor_request_filter
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: U64.t)
  : GTot bool =
  (cheney_promote minor major fp roots).fwd_map obj <> 0UL

let cheney_forwarded_minor_requests
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : GTot (list nat)
  =
  PromotionDemand.minor_promotion_filtered_requests
    minor (cheney_forwarded_minor_request_filter minor major fp roots)

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
let cheney_forwarded_minor_requests_positive
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
      (requires minor_wf minor)
      (ensures
        SpecMajorAllocMultiAlloc.all_requests_positive
          (cheney_forwarded_minor_requests minor major fp roots))
  =
  PromotionDemand.minor_promotion_filtered_requests_positive
    minor (cheney_forwarded_minor_request_filter minor major fp roots)

let cheney_forwarded_minor_requests_demand_bound
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
      (ensures
        SpecMajorAllocMultiAlloc.allocation_list_demand
          (cheney_forwarded_minor_requests minor major fp roots) <=
        PromotionDemand.minor_promotion_demand minor)
  =
  PromotionDemand.minor_promotion_filtered_requests_demand_bound
    minor (cheney_forwarded_minor_request_filter minor major fp roots)
#pop-options

private let cheney_unforwarded_minor_request_filter
  (cs: cheney_state) (obj: U64.t)
  : GTot bool =
  cs.cs_fwd obj = 0UL

let cheney_unforwarded_minor_requests
  (minor: minor_state) (cs: cheney_state)
  : GTot (list nat)
  =
  PromotionDemand.minor_promotion_filtered_requests
    minor (cheney_unforwarded_minor_request_filter cs)

let cheney_unforwarded_split_demand
  (minor: minor_state) (cs: cheney_state)
  : GTot nat
  =
  SpecMajorAllocMultiAlloc.allocation_list_demand
    (cheney_unforwarded_minor_requests minor cs)

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
let cheney_unforwarded_split_demand_bound
  (minor: minor_state) (cs: cheney_state)
  : Lemma
      (ensures
        cheney_unforwarded_split_demand minor cs <=
        PromotionDemand.minor_promotion_demand minor)
  =
  PromotionDemand.minor_promotion_filtered_requests_demand_bound
    minor (cheney_unforwarded_minor_request_filter cs)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
private let cheney_unforwarded_split_demand_object_bound
  (minor: minor_state) (cs: cheney_state) (obj: U64.t)
  : Lemma
      (requires Seq.mem obj (minor_objects minor) /\
                cs.cs_fwd obj = 0UL)
      (ensures
        SpecMajorAllocMultiAlloc.request_split_demand
          (minor_wosize minor obj) <=
        cheney_unforwarded_split_demand minor cs)
  =
  PromotionDemand.minor_promotion_filtered_request_split_demand_bound
    minor (cheney_unforwarded_minor_request_filter cs) obj

private let cheney_unforwarded_split_demand_extend_decrease
  (minor: minor_state) (cs: cheney_state)
  (addr: U64.t) (new_addr: U64.t)
  : Lemma
      (requires new_addr <> 0UL /\
                Seq.mem addr (minor_objects minor) /\
                cs.cs_fwd addr = 0UL)
      (ensures
        SpecMajorAllocMultiAlloc.request_split_demand
          (minor_wosize minor addr) +
        SpecMajorAllocMultiAlloc.allocation_list_demand
          (PromotionDemand.minor_promotion_filtered_requests
            minor
            (fun obj -> extend_forwarding cs.cs_fwd addr new_addr obj = 0UL)) <=
        cheney_unforwarded_split_demand minor cs)
  =
  let include_after (obj: U64.t) : GTot bool =
    extend_forwarding cs.cs_fwd addr new_addr obj = 0UL in
  let include_before = cheney_unforwarded_minor_request_filter cs in
  let after_to_before (x: U64.t)
    : Lemma
        (requires Seq.mem x (minor_objects minor) /\ include_after x)
        (ensures include_before x)
    =
    if x = addr then begin
      assert (extend_forwarding cs.cs_fwd addr new_addr x == new_addr);
      assert False
    end else
      assert (extend_forwarding cs.cs_fwd addr new_addr x == cs.cs_fwd x)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires after_to_before);
  PromotionDemand.minor_promotion_filtered_requests_remove_split_demand_bound
    minor include_before include_after addr

private let cheney_unforwarded_split_demand_extend_irrelevant
  (minor: minor_state) (cs: cheney_state)
  (addr: U64.t) (new_addr: U64.t)
  : Lemma
      (requires minor_wf minor /\
                is_infix_in_minor minor addr)
      (ensures
        SpecMajorAllocMultiAlloc.allocation_list_demand
          (PromotionDemand.minor_promotion_filtered_requests
            minor
            (fun obj -> extend_forwarding cs.cs_fwd addr new_addr obj = 0UL)) <=
        cheney_unforwarded_split_demand minor cs)
  =
  let include_after (obj: U64.t) : GTot bool =
    extend_forwarding cs.cs_fwd addr new_addr obj = 0UL in
  let include_before = cheney_unforwarded_minor_request_filter cs in
  let after_to_before (x: U64.t)
    : Lemma
        (requires Seq.mem x (minor_objects minor) /\ include_after x)
        (ensures include_before x)
    =
    minor_objects_not_infix minor x;
    assert (minor_tag minor x <> 249);
    assert (minor_tag minor addr = 249);
    assert (x <> addr);
    assert (extend_forwarding cs.cs_fwd addr new_addr x == cs.cs_fwd x)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires after_to_before);
  PromotionDemand.minor_promotion_filtered_requests_demand_monotone
    minor include_after include_before

private let cheney_unforwarded_split_demand_state_extend_decrease
  (minor: minor_state) (cs cs_after: cheney_state)
  (addr: U64.t) (new_addr: U64.t)
  : Lemma
      (requires new_addr <> 0UL /\
                Seq.mem addr (minor_objects minor) /\
                cs.cs_fwd addr = 0UL /\
                cs_after.cs_fwd ==
                  extend_forwarding cs.cs_fwd addr new_addr)
      (ensures
        SpecMajorAllocMultiAlloc.request_split_demand
          (minor_wosize minor addr) +
        cheney_unforwarded_split_demand minor cs_after <=
        cheney_unforwarded_split_demand minor cs)
  =
  cheney_unforwarded_split_demand_extend_decrease
    minor cs addr new_addr;
  let include_state = cheney_unforwarded_minor_request_filter cs_after in
  let include_ext (obj: U64.t) : GTot bool =
    extend_forwarding cs.cs_fwd addr new_addr obj = 0UL in
  let state_to_ext (x: U64.t)
    : Lemma
        (requires Seq.mem x (minor_objects minor) /\ include_state x)
        (ensures include_ext x)
    =
    assert (cs_after.cs_fwd x ==
            extend_forwarding cs.cs_fwd addr new_addr x)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires state_to_ext);
  PromotionDemand.minor_promotion_filtered_requests_demand_monotone
    minor include_state include_ext;
  assert (cheney_unforwarded_split_demand minor cs_after <=
          SpecMajorAllocMultiAlloc.allocation_list_demand
            (PromotionDemand.minor_promotion_filtered_requests
              minor include_ext));
  assert (SpecMajorAllocMultiAlloc.request_split_demand
            (minor_wosize minor addr) +
          cheney_unforwarded_split_demand minor cs_after <=
          cheney_unforwarded_split_demand minor cs)

private let cheney_unforwarded_split_demand_state_extend_infix_monotone
  (minor: minor_state) (cs cs_after: cheney_state)
  (addr: U64.t) (new_addr: U64.t)
  : Lemma
      (requires minor_wf minor /\
                is_infix_in_minor minor addr /\
                cs_after.cs_fwd ==
                  extend_forwarding cs.cs_fwd addr new_addr)
      (ensures
        cheney_unforwarded_split_demand minor cs_after <=
        cheney_unforwarded_split_demand minor cs)
  =
  cheney_unforwarded_split_demand_extend_irrelevant
    minor cs addr new_addr;
  let include_state = cheney_unforwarded_minor_request_filter cs_after in
  let include_ext (obj: U64.t) : GTot bool =
    extend_forwarding cs.cs_fwd addr new_addr obj = 0UL in
  let state_to_ext (x: U64.t)
    : Lemma
        (requires Seq.mem x (minor_objects minor) /\ include_state x)
        (ensures include_ext x)
    =
    assert (cs_after.cs_fwd x ==
            extend_forwarding cs.cs_fwd addr new_addr x)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires state_to_ext);
  PromotionDemand.minor_promotion_filtered_requests_demand_monotone
    minor include_state include_ext;
  assert (cheney_unforwarded_split_demand minor cs_after <=
          SpecMajorAllocMultiAlloc.allocation_list_demand
            (PromotionDemand.minor_promotion_filtered_requests
              minor include_ext));
  assert (cheney_unforwarded_split_demand minor cs_after <=
          cheney_unforwarded_split_demand minor cs)
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let cheney_forwarded_dense_alloc_list_single_chunk_no_oom
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
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
           cheney_forwarded_minor_requests minor major fp roots in
         let r =
           SpecMajorAllocMultiAlloc.dense_alloc_list_spec
             major fp fuel requests in
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.dense_list_objs_out))
  =
  cheney_forwarded_minor_requests_positive minor major fp roots;
  cheney_forwarded_minor_requests_demand_bound minor major fp roots;
  let requests = cheney_forwarded_minor_requests minor major fp roots in
  SpecMajorAllocMultiAlloc.dense_alloc_list_head_split_nonzero_single_chunk_with_budget
    major fp fuel requests (PromotionDemand.minor_promotion_demand minor)
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let cheney_forwarded_dense_alloc_list_default_single_chunk_no_oom
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
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
           cheney_forwarded_minor_requests minor major fp roots in
         let r =
           SpecMajorAllocMultiAlloc.dense_alloc_list_default_spec
             major fp requests in
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.dense_list_objs_out))
  =
  cheney_forwarded_minor_requests_positive minor major fp roots;
  cheney_forwarded_minor_requests_demand_bound minor major fp roots;
  let requests = cheney_forwarded_minor_requests minor major fp roots in
  SpecMajorAllocMultiAlloc.dense_alloc_list_default_head_split_nonzero_single_chunk_with_budget
    major fp requests (PromotionDemand.minor_promotion_demand minor)
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let promote_object_head_no_oom_single_chunk
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
  assert (SpecAlloc.normalized_wosize wosize == wosize);
  SpecMajorAlloc.major_alloc_spec_with_fuel_head_no_oom
    (MH.single_chunk_major_heap major) fp wosize SpecAlloc.alloc_search_fuel;
  SpecMajorAlloc.major_alloc_spec_with_fuel_single_chunk_compat
    major fp wosize SpecAlloc.alloc_search_fuel;
  assert ((SpecAlloc.alloc_spec_with_fuel
            major fp wosize SpecAlloc.alloc_search_fuel).obj_out <> 0UL);
  assert ((SpecAlloc.alloc_spec major fp wosize).obj_out <> 0UL);
  promote_object_success minor major obj fp wosize
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let promote_minor_object_head_no_oom_single_chunk
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
  minor_objects_body_bound minor obj;
  PromotionDemand.minor_promotion_object_wosize_demand_bound minor obj;
  assert (SpecMajorAlloc.major_fl_head_wosize
            (MH.single_chunk_major_heap major) fp >=
          wosize);
  promote_object_head_no_oom_single_chunk minor major obj fp wosize
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_promote_object_default_single_chunk_compat
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
  ChunkedPromote.chunked_promote_object_with_fuel_single_chunk_compat
    minor major obj fp wosize SpecAlloc.alloc_search_fuel
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_cheney_forward_normal_default_single_chunk_compat
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (ensures
        ChunkedCheney.chunked_cheney_forward_normal
          minor (ChunkedCheney.single_chunk_cheney_state cs) addr
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_forward_normal minor cs addr))
  =
  ChunkedCheney.chunked_cheney_forward_normal_default_single_chunk_compat
    minor cs addr

let chunked_cheney_forward_one_default_single_chunk_compat
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (ensures
        ChunkedCheney.chunked_cheney_forward_one
          minor (ChunkedCheney.single_chunk_cheney_state cs) addr
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_forward_one minor cs addr))
  =
  ChunkedCheney.chunked_cheney_forward_one_default_single_chunk_compat
    minor cs addr

let chunked_cheney_forward_fields_default_single_chunk_compat
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
  ChunkedCheney.chunked_cheney_forward_fields_default_single_chunk_compat
    minor cs parent idx wosize

let chunked_cheney_forward_roots_default_single_chunk_compat
  (minor: minor_state) (cs: cheney_state)
  (roots: seq U64.t) (idx: nat)
  : Lemma
      (ensures
        ChunkedCheney.chunked_cheney_forward_roots
          minor (ChunkedCheney.single_chunk_cheney_state cs) roots idx
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_forward_roots minor cs roots idx))
  =
  ChunkedCheney.chunked_cheney_forward_roots_default_single_chunk_compat
    minor cs roots idx

let chunked_cheney_scan_default_single_chunk_compat
  (minor: minor_state) (cs: cheney_state) (scan scan_fuel: nat)
  : Lemma
      (ensures
        ChunkedCheney.chunked_cheney_scan
          minor (ChunkedCheney.single_chunk_cheney_state cs) scan scan_fuel
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_scan minor cs scan scan_fuel))
  =
  ChunkedCheney.chunked_cheney_scan_default_single_chunk_compat
    minor cs scan scan_fuel

let chunked_cheney_promote_default_single_chunk_compat
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
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
  ChunkedCheney.chunked_cheney_promote_default_single_chunk_compat
    minor major fp roots
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_cheney_forward_normal_noalloc_preserves_chunked_alloc_shape
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
  if not (Seq.mem addr (minor_objects minor)) || cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_normal_noop minor cs addr fuel
  else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then
      ChunkedCheney.chunked_cheney_forward_normal_noop_wz0 minor cs addr fuel
    else begin
      assert (wz > 0);
      ChunkedCheney.chunked_cheney_forward_normal_noop_oom
        minor cs addr fuel
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_alloc_head_split_alloc_header_wosize
  (mh: MH.major_heap) (fp: U64.t)
  (requested_wz: nat{requested_wz > 0 /\
                     requested_wz < pow2 54 /\
                     FStar.UInt.size requested_wz 64})
  (fuel: nat)
  : Lemma
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
  =
  GenInv.chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAlloc.major_fl_above_zero_current mh fp fuel;
  assert (U64.v fp >= U64.v zero_addr + U64.v mword);
  let dst : obj_addr = fp in
  let hd = hd_address dst in
  SpecMajorAlloc.major_fl_head_wosize_current mh fp fuel;
  SpecMajorAlloc.major_fl_head_block_fits_current mh fp fuel;
  SpecMajorAlloc.major_fl_valid_link_lookup_index mh fp fuel;
  let idx = MH.lookup_chunk_index_value mh hd in
  assert (MH.lookup_chunk_index mh hd == Some idx);
  assert (idx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh idx) hd);
  match MH.read_word_in_major mh hd with
  | None -> assert False
  | Some old_hdr ->
    let block_wz = U64.v (getWosize old_hdr) in
    assert (SpecMajorAlloc.major_fl_head_wosize mh fp == block_wz);
    assert (block_wz < pow2 54);
    assert (block_wz >= requested_wz + 2);
    assert (block_wz - requested_wz >= 2);
    assert (requested_wz < pow2 54);
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    assert (requested_wz < pow2 64);
    assert (FStar.UInt.size requested_wz 64);
    match MH.read_word_in_major mh dst with
    | None -> assert False
    | Some next_fp ->
      let c = Seq.index mh idx in
      MH.read_word_in_major_at_lookup_index mh hd idx;
      assert (MH.read_word_in_chunk c hd == old_hdr);
      assert (U64.v hd + (1 + block_wz) * U64.v mword <=
              MH.chunk_end c);
      assert (U64.v mword == 8);
      let rem_hd_nat = U64.v hd + (1 + requested_wz) * 8 in
      let rem_obj_nat = rem_hd_nat + U64.v mword in
      FStar.Math.Lemmas.distributivity_add_left (1 + requested_wz) 1 8;
      assert ((1 + requested_wz) * 8 + 8 == (requested_wz + 2) * 8);
      FStar.Math.Lemmas.paren_add_right (U64.v hd) ((1 + requested_wz) * 8) 8;
      assert (rem_obj_nat == U64.v hd + (requested_wz + 2) * 8);
      assert (requested_wz + 3 <= 1 + block_wz);
      assert (rem_obj_nat + 8 == U64.v hd + (requested_wz + 3) * 8);
      assert (rem_obj_nat + 8 <= U64.v hd + (1 + block_wz) * 8);
      assert (rem_obj_nat + 8 <= MH.chunk_end c);
      assert (MH.chunk_end c <= heap_size);
      assert (rem_hd_nat < heap_size);
      assert (rem_obj_nat < heap_size);
      assert (heap_size < pow2 64);
      assert (rem_hd_nat < pow2 64);
      assert (rem_obj_nat < pow2 64);
      assert (rem_obj_nat >= U64.v mword);
      hd_address_spec dst;
      SpecMajorAlloc.aligned_plus_word_product (U64.v hd) (1 + requested_wz);
      assert (rem_hd_nat % U64.v mword == 0);
      SpecMajorAlloc.aligned_plus_word_product (U64.v hd) (requested_wz + 2);
      assert (rem_obj_nat % U64.v mword == 0);
      let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
      let rem_obj : obj_addr = U64.uint_to_t rem_obj_nat in
      assert (U64.v rem_hd == rem_hd_nat);
      assert (U64.v rem_obj == rem_obj_nat);
      assert (U64.v rem_obj == U64.v rem_hd + U64.v mword);
      SpecMajorAlloc.active_head_split_remainder_words_in_chunk
        c hd block_wz requested_wz rem_hd rem_obj;
      let rem_wz = block_wz - requested_wz - 1 in
      assert (rem_wz >= 1);
      assert (rem_wz < pow2 54);
      let rem_wz_u : w:U64.t{U64.v w == rem_wz /\ U64.v w < pow2 54} =
        U64.uint_to_t rem_wz in
      assert (U64.v rem_wz_u == block_wz - requested_wz - 1);
      SpecMajorAlloc.major_alloc_head_split
        mh dst requested_wz fuel old_hdr next_fp rem_hd rem_obj;
      let r =
        SpecMajorAlloc.major_alloc_spec_with_fuel mh fp requested_wz fuel in
      assert (r.major_obj_out == fp);
      assert (r.major_fp_out == rem_obj);
      assert (r.major_fp_out <> 0UL);
      SpecMajorAlloc.head_split_major_preserves_read_at
        mh idx dst hd old_hdr requested_wz block_wz next_fp rem_wz_u
        rem_hd rem_obj;
      let alloc_hdr =
        SpecAlloc.make_header (U64.uint_to_t requested_wz)
          SpecAlloc.white_bits 0UL in
      assert (MH.read_word_in_major r.major_alloc_out hd == Some alloc_hdr);
      AllocHeader.make_header_getWosize
        (U64.uint_to_t requested_wz) SpecAlloc.white_bits 0UL;
      assert (U64.v (getWosize alloc_hdr) == requested_wz)

let chunked_promote_head_split_padding_noop
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
  GenInv.chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAlloc.major_fl_above_zero_current mh fp fuel;
  assert (U64.v fp >= U64.v zero_addr + U64.v mword);
  SpecMajorAlloc.major_fl_head_wosize_current mh fp fuel;
  match MH.read_word_in_major mh (hd_address (fp <: obj_addr)) with
  | None -> assert False
  | Some old_hdr ->
    assert (SpecMajorAlloc.major_fl_head_wosize mh fp ==
            U64.v (getWosize old_hdr));
    assert (U64.v (getWosize old_hdr) < pow2 54);
    assert (wosize + 2 <= U64.v (getWosize old_hdr));
    assert (wosize < pow2 54);
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    assert (wosize < pow2 64);
    assert (FStar.UInt.size wosize 64);
  chunked_alloc_head_split_alloc_header_wosize mh fp wosize fuel;
  let alloc_res =
    SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
  assert (alloc_res.major_obj_out == fp);
  let dst : obj_addr = fp in
  let hd = hd_address dst in
  let hdr =
    SpecAlloc.make_header (U64.uint_to_t wosize) SpecAlloc.white_bits 0UL in
  hd_address_spec dst;
  assert (U64.v hd + U64.v mword == U64.v dst);
  assert (MH.read_word_in_major alloc_res.major_alloc_out hd == Some hdr);
  assert (U64.v (getWosize hdr) == wosize);
  let copied =
    ChunkedPromote.chunked_copy_fields
      minor alloc_res.major_alloc_out obj fp 0 wosize in
  ChunkedPromote.chunked_copy_fields_frame_before
    minor alloc_res.major_alloc_out obj fp 0 wosize hd hdr;
  assert (MH.read_word_in_major copied hd == Some hdr);
  assert (U64.v fp >= U64.v mword);
  assert (U64.v fp < heap_size);
  assert (U64.v fp % U64.v mword == 0);
  assert (U64.v (getWosize hdr) <= wosize);
  ChunkedPromote.chunked_zero_promote_padding_noop
    copied fp wosize hdr;
  assert (ChunkedPromote.chunked_zero_promote_padding copied fp wosize ==
          copied)
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let alloc_spec_head_split_alloc_wosize_single_chunk
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
         Seq.mem (fp <: obj_addr) (objects zero_addr r.heap_out) /\
         U64.v (wosize_of_object (fp <: obj_addr) r.heap_out) == wosize /\
         U64.v fp + (wosize - 1) * U64.v mword + U64.v mword <= heap_size))
  =
  let mh = MH.single_chunk_major_heap major in
  SpecMajorAlloc.major_fl_above_zero_current mh fp SpecAlloc.alloc_search_fuel;
  assert (U64.v fp >= U64.v zero_addr + U64.v mword);
  assert (U64.v fp >= U64.v mword);
  let dst_obj : obj_addr = fp in
  let hd = hd_address dst_obj in
  hd_address_spec dst_obj;
  SpecMajorAlloc.major_fl_head_wosize_current
    mh fp SpecAlloc.alloc_search_fuel;
  SpecMajorAlloc.major_fl_blocks_fit_current
    mh fp SpecAlloc.alloc_search_fuel;
  MH.single_chunk_read_word_compat major hd;
  match MH.read_word_in_major mh hd with
  | None -> assert False
  | Some hdr ->
    assert (read_word major hd == hdr);
    let block_wz = U64.v (getWosize hdr) in
    assert (SpecMajorAlloc.major_fl_head_wosize mh fp == block_wz);
    assert (block_wz >= wosize + 2);
    getWosize_bound hdr;
    assert (block_wz < pow2 54);
    assert (wosize < pow2 54);
    SpecMajorAlloc.major_fl_valid_next mh fp SpecAlloc.alloc_search_fuel;
    match MH.read_word_in_major mh dst_obj with
    | None -> assert False
    | Some next_fp ->
      MH.single_chunk_read_word_compat major dst_obj;
      assert (read_word major dst_obj == next_fp);
      let idx = MH.lookup_chunk_index_value mh hd in
      assert (MH.lookup_chunk_index mh hd == Some idx);
      assert (idx < Seq.length mh);
      assert (Seq.length mh == 1);
      assert (idx == 0);
      assert (Seq.index mh idx == MH.single_chunk_of_heap major);
      assert (MH.chunk_end (Seq.index mh idx) == heap_size);
      assert (U64.v hd + (1 + block_wz) * U64.v mword <= heap_size);
      assert (U64.v mword == 8);
      let rem_hd_nat = U64.v hd + (1 + wosize) * 8 in
      let rem_obj_nat = rem_hd_nat + 8 in
      assert (wosize + 2 <= block_wz);
      FStar.Math.Lemmas.lemma_mult_le_right 8 (wosize + 2) block_wz;
      assert ((wosize + 2) * 8 <= block_wz * 8);
      FStar.Math.Lemmas.distributivity_add_left wosize 2 8;
      assert ((wosize + 2) * 8 == wosize * 8 + 2 * 8);
      FStar.Math.Lemmas.distributivity_add_left (1 + wosize) 1 8;
      assert ((1 + wosize) * 8 + 8 == (wosize + 2) * 8);
      FStar.Math.Lemmas.paren_add_right (U64.v hd) ((1 + wosize) * 8) 8;
      assert (rem_obj_nat == U64.v hd + (wosize + 2) * 8);
      assert (rem_obj_nat <= U64.v hd + block_wz * 8);
      assert (U64.v hd + block_wz * 8 <
              U64.v hd + (1 + block_wz) * 8);
      assert (rem_obj_nat < heap_size);
      assert (rem_hd_nat < heap_size);
      assert (rem_hd_nat < pow2 64);
      assert (rem_obj_nat < pow2 64);
      assert (rem_hd_nat % U64.v mword == 0);
      assert (rem_obj_nat % U64.v mword == 0);
      assert (U64.v hd + 16 <= heap_size);
      assert (SpecAlloc.spec_next_fp major dst_obj == next_fp);
      SpecAlloc.alloc_from_block_split_normal major dst_obj wosize next_fp;
      SpecAlloc.alloc_search_found_head
        major fp 0UL fp wosize SpecAlloc.alloc_search_fuel;
      let alloc_hdr =
        SpecAlloc.make_header (U64.uint_to_t wosize) SpecAlloc.white_bits 0UL in
      let g1 = write_word major hd alloc_hdr in
      let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
      let rem_wz = block_wz - wosize - 1 in
      assert (rem_wz < pow2 54);
      let rem_hdr =
        SpecAlloc.make_header (U64.uint_to_t rem_wz) SpecAlloc.blue_bits 0UL in
      let g2 = write_word g1 rem_hd rem_hdr in
      let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
      let g3 = write_word g2 rem_obj next_fp in
      let r = SpecAlloc.alloc_spec major fp wosize in
      assert (r.heap_out == g3);
      assert (r.fp_out == rem_obj);
      assert (r.obj_out == fp);
      assert (rem_obj <> 0UL);
      assert (U64.v fp + (wosize - 1) * U64.v mword +
              U64.v mword == rem_hd_nat);
      read_write_same major hd alloc_hdr;
      assert (read_word g1 hd == alloc_hdr);
      assert (U64.v hd + U64.v mword <= U64.v rem_hd);
      read_write_different g1 rem_hd hd rem_hdr;
      assert (read_word g2 hd == alloc_hdr);
      assert (U64.v hd + U64.v mword <= U64.v rem_obj);
      read_write_different g2 rem_obj hd next_fp;
      assert (read_word g3 hd == alloc_hdr);
      // The allocated head remains an object in the post-split heap.  Prove it
      // in the chunked single-chunk model and bridge back to the dense objects
      // enumeration used by the promotion frame lemmas.
      let c = Seq.index mh idx in
      MH.single_chunk_major_heap_wf major;
      SpecMajorAlloc.major_fl_valid_gives_mem
        mh fp SpecAlloc.alloc_search_fuel;
      MH.read_word_in_major_at_lookup_index mh hd idx;
      assert (MH.read_word_in_chunk c hd == hdr);
      MH.major_objects_member_in_lookup_chunk mh idx dst_obj;
      assert (Seq.mem dst_obj (MH.objects_in_chunk c));
      assert (MH.object_wosize_in_chunk c dst_obj == block_wz);
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      assert (FStar.UInt.size wosize 64);
      let req : rreq:nat{rreq == wosize /\
                         rreq < pow2 54 /\ FStar.UInt.size rreq 64} =
        wosize in
      let rem_wz_u : rw:U64.t{U64.v rw == rem_wz /\ U64.v rw < pow2 54} =
        U64.uint_to_t rem_wz in
      assert (U64.v rem_wz_u == block_wz - wosize - 1);
      assert (wosize + 3 <= 1 + block_wz);
      FStar.Math.Lemmas.distributivity_add_left (wosize + 2) 1 8;
      assert ((wosize + 2) * 8 + 8 == (wosize + 3) * 8);
      FStar.Math.Lemmas.paren_add_right
        (U64.v hd) ((wosize + 2) * 8) 8;
      assert (rem_obj_nat + 8 == U64.v hd + (wosize + 3) * 8);
      assert (rem_obj_nat + 8 <= U64.v hd + (1 + block_wz) * 8);
      assert (rem_obj_nat + 8 <= heap_size);
      assert (MH.word_in_chunk c rem_hd);
      assert (MH.word_in_chunk c rem_obj);
      SpecMajorAlloc.major_alloc_head_split
        mh dst_obj req SpecAlloc.alloc_search_fuel hdr next_fp rem_hd rem_obj;
      let mr =
        SpecMajorAlloc.major_alloc_spec_with_fuel
          mh fp wosize SpecAlloc.alloc_search_fuel in
      assert (mr.major_alloc_out ==
              SpecMajorAllocSplitShape.head_split_heap
                mh dst_obj req next_fp rem_wz_u rem_hd rem_obj);
      SpecMajorAllocSplitShape.head_split_preserves_allocated_head_node_facts
        mh idx dst_obj hdr next_fp req block_wz next_fp rem_wz_u rem_hd rem_obj;
      assert (Seq.mem dst_obj (MH.major_objects mr.major_alloc_out));
      SpecMajorAlloc.major_alloc_spec_with_fuel_single_chunk_compat
        major fp wosize SpecAlloc.alloc_search_fuel;
      assert (SpecAlloc.alloc_spec major fp wosize ==
              SpecAlloc.alloc_spec_with_fuel
                major fp wosize SpecAlloc.alloc_search_fuel);
      assert (mr.major_alloc_out == MH.single_chunk_major_heap r.heap_out);
      assert (Seq.mem dst_obj
        (MH.major_objects (MH.single_chunk_major_heap r.heap_out)));
      MH.single_chunk_major_objects_compat r.heap_out;
      assert (Seq.mem dst_obj (objects zero_addr r.heap_out));
      AllocHeader.make_header_getWosize
        (U64.uint_to_t wosize) SpecAlloc.white_bits 0UL;
      wosize_of_object_spec dst_obj r.heap_out
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let promote_object_head_split_padding_noop_single_chunk
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
         let copied = copy_fields minor r.heap_out obj fp 0 wosize in
         zero_promote_padding copied (fp <: obj_addr) wosize == copied))
  =
  alloc_spec_head_split_alloc_wosize_single_chunk major fp wosize;
  let r = SpecAlloc.alloc_spec major fp wosize in
  let dst_obj : obj_addr = fp in
  let hd = hd_address dst_obj in
  hd_address_spec dst_obj;
  dst_fields_valid_from_bounds fp wosize;
  copy_fields_frame minor r.heap_out obj fp 0 wosize hd;
  let copied = copy_fields minor r.heap_out obj fp 0 wosize in
  wosize_of_object_spec dst_obj copied;
  wosize_of_object_spec dst_obj r.heap_out;
  assert (wosize_of_object dst_obj copied ==
          wosize_of_object dst_obj r.heap_out);
  assert (U64.v (wosize_of_object dst_obj copied) <= wosize);
  zero_promote_padding_noop copied dst_obj wosize
#pop-options

/// ---------------------------------------------------------------------------
/// Active-head split promotion frames from the post-allocation heap
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
private let copy_fields_frame_other_header
  (minor: minor_state) (g: heap) (src_obj: U64.t)
  (dst src: obj_addr) (wz: nat{wz > 0})
  : Lemma
      (requires Seq.mem dst (objects zero_addr g) /\
                Seq.mem src (objects zero_addr g) /\
                src <> dst /\
                U64.v dst % 8 == 0 /\
                U64.v (wosize_of_object dst g) >= wz /\
                dst_fields_valid dst wz)
      (ensures
        read_word (copy_fields minor g src_obj dst 0 wz) (hd_address src) ==
        read_word g (hd_address src))
  =
  hd_address_spec src;
  hd_address_spec dst;
  assert (U64.v mword == 8);
  if U64.v src < U64.v dst then begin
    assert (U64.v (hd_address src) + 8 == U64.v src);
    assert (U64.v (hd_address src) + 8 <= U64.v dst);
    copy_fields_frame minor g src_obj dst 0 wz (hd_address src)
  end else if U64.v dst < U64.v src then begin
    objects_separated zero_addr g dst src;
    assert (U64.v (wosize_of_object_as_wosize dst g) ==
            U64.v (wosize_of_object dst g));
    assert (U64.v src >
            U64.v dst + U64.v (wosize_of_object dst g) * 8);
    FStar.Math.Lemmas.lemma_mult_le_right
      8 wz (U64.v (wosize_of_object dst g));
    assert (U64.v dst + wz * 8 <=
            U64.v dst + U64.v (wosize_of_object dst g) * 8);
    assert (U64.v src > U64.v dst + wz * 8);
    SpecMajorAlloc.aligned_plus_word_product (U64.v dst) wz;
    assert ((U64.v dst + wz * 8) % U64.v mword == 0);
    MH.word_aligned_gt_at_least_mword
      (U64.v src) (U64.v dst + wz * 8);
    assert (U64.v src >= U64.v dst + wz * 8 + 8);
    assert (U64.v (hd_address src) >= U64.v dst + wz * 8);
    copy_fields_frame minor g src_obj dst 0 wz (hd_address src)
  end else begin
    assert (U64.v src == U64.v dst);
    assert (src == dst);
    assert False
  end

private let copy_fields_frame_other_field0
  (minor: minor_state) (g: heap) (src_obj: U64.t)
  (dst src: obj_addr) (wz: nat{wz > 0})
  : Lemma
      (requires Seq.mem dst (objects zero_addr g) /\
                Seq.mem src (objects zero_addr g) /\
                src <> dst /\
                U64.v dst % 8 == 0 /\
                U64.v (wosize_of_object dst g) >= wz /\
                U64.v (wosize_of_object src g) >= 1 /\
                dst_fields_valid dst wz)
      (ensures
        read_word (copy_fields minor g src_obj dst 0 wz) src ==
        read_word g src)
  =
  assert (U64.v mword == 8);
  if U64.v src < U64.v dst then begin
    objects_separated zero_addr g src dst;
    assert (U64.v (wosize_of_object_as_wosize src g) ==
            U64.v (wosize_of_object src g));
    assert (U64.v dst >
            U64.v src + U64.v (wosize_of_object src g) * 8);
    assert (U64.v src + 8 <=
            U64.v src + U64.v (wosize_of_object src g) * 8);
    assert (U64.v src + 8 <= U64.v dst);
    copy_fields_frame minor g src_obj dst 0 wz src
  end else if U64.v dst < U64.v src then begin
    objects_separated zero_addr g dst src;
    assert (U64.v (wosize_of_object_as_wosize dst g) ==
            U64.v (wosize_of_object dst g));
    assert (U64.v src >
            U64.v dst + U64.v (wosize_of_object dst g) * 8);
    FStar.Math.Lemmas.lemma_mult_le_right
      8 wz (U64.v (wosize_of_object dst g));
    assert (U64.v dst + wz * 8 <=
            U64.v dst + U64.v (wosize_of_object dst g) * 8);
    assert (U64.v src > U64.v dst + wz * 8);
    assert (U64.v src >= U64.v dst + wz * 8);
    copy_fields_frame minor g src_obj dst 0 wz src
  end else begin
    assert (U64.v src == U64.v dst);
    assert (src == dst);
    assert False
  end

private let set_promoted_tag_frame_other_header
  (g: heap) (dst src: obj_addr) (tag: nat{tag < 256})
  : Lemma
      (requires src <> dst)
      (ensures
        read_word (set_promoted_tag g dst tag) (hd_address src) ==
        read_word g (hd_address src))
  =
  hd_address_spec src;
  hd_address_spec dst;
  assert (U64.v mword == 8);
  if U64.v src < U64.v dst then begin
    MH.word_aligned_gt_at_least_mword (U64.v dst) (U64.v src);
    assert (U64.v dst >= U64.v src + 8);
    assert (U64.v (hd_address dst) >= U64.v src);
    assert (U64.v (hd_address src) + U64.v mword <=
            U64.v (hd_address dst));
    set_promoted_tag_read_frame g dst tag (hd_address src)
  end else if U64.v dst < U64.v src then begin
    MH.word_aligned_gt_at_least_mword (U64.v src) (U64.v dst);
    assert (U64.v src >= U64.v dst + 8);
    assert (U64.v (hd_address dst) + U64.v mword <=
            U64.v (hd_address src));
    set_promoted_tag_read_frame g dst tag (hd_address src)
  end else begin
    assert (U64.v src == U64.v dst);
    assert (src == dst);
    assert False
  end

private let set_promoted_tag_frame_other_field0
  (g: heap) (dst src: obj_addr) (tag: nat{tag < 256})
  : Lemma
      (requires Seq.mem dst (objects zero_addr g) /\
                Seq.mem src (objects zero_addr g) /\
                src <> dst /\
                U64.v (wosize_of_object src g) >= 1)
      (ensures
        read_word (set_promoted_tag g dst tag) src ==
        read_word g src)
  =
  hd_address_spec dst;
  assert (U64.v mword == 8);
  if U64.v src < U64.v dst then begin
    objects_separated zero_addr g src dst;
    assert (U64.v (wosize_of_object_as_wosize src g) ==
            U64.v (wosize_of_object src g));
    assert (U64.v dst >
            U64.v src + U64.v (wosize_of_object src g) * 8);
    assert (U64.v dst > U64.v src + 8);
    SpecMajorAlloc.aligned_plus_word_product (U64.v src) 1;
    assert ((U64.v src + 8) % U64.v mword == 0);
    MH.word_aligned_gt_at_least_mword (U64.v dst) (U64.v src + 8);
    assert (U64.v dst >= U64.v src + 16);
    assert (U64.v src + U64.v mword <= U64.v (hd_address dst));
    set_promoted_tag_read_frame g dst tag src
  end else if U64.v dst < U64.v src then begin
    assert (U64.v (hd_address dst) + U64.v mword <= U64.v src);
    set_promoted_tag_read_frame g dst tag src
  end else begin
    assert (U64.v src == U64.v dst);
    assert (src == dst);
    assert False
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
private let promote_object_head_split_preserves_objects_from_alloc_single_chunk
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
        (let alloc_res = SpecAlloc.alloc_spec major fp wosize in
         let res = promote_object minor major obj fp wosize in
         objects zero_addr res.major_out == objects zero_addr alloc_res.heap_out))
  =
  alloc_spec_head_split_alloc_wosize_single_chunk major fp wosize;
  promote_object_head_split_padding_noop_single_chunk minor major obj fp wosize;
  let alloc_res = SpecAlloc.alloc_spec major fp wosize in
  let dst : obj_addr = fp in
  promote_object_success minor major obj fp wosize;
  let copied = copy_fields minor alloc_res.heap_out obj dst 0 wosize in
  dst_fields_valid_from_bounds fp wosize;
  copy_fields_preserves_objects_aux
    minor alloc_res.heap_out obj dst 0 wosize;
  assert (objects zero_addr copied == objects zero_addr alloc_res.heap_out);
  assert (Seq.mem dst (objects zero_addr copied));
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  set_promoted_tag_preserves_objects copied dst tag

private let promote_object_head_split_frame_header_from_alloc_single_chunk
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (src: obj_addr)
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
                  (MH.single_chunk_major_heap major) fp >= wosize + 2 /\
                (let alloc_res = SpecAlloc.alloc_spec major fp wosize in
                 Seq.mem src (objects zero_addr alloc_res.heap_out) /\
                 src <> (fp <: obj_addr)))
      (ensures
        (let alloc_res = SpecAlloc.alloc_spec major fp wosize in
         let res = promote_object minor major obj fp wosize in
         read_word res.major_out (hd_address src) ==
         read_word alloc_res.heap_out (hd_address src)))
  =
  alloc_spec_head_split_alloc_wosize_single_chunk major fp wosize;
  promote_object_head_split_padding_noop_single_chunk minor major obj fp wosize;
  promote_object_success minor major obj fp wosize;
  let alloc_res = SpecAlloc.alloc_spec major fp wosize in
  let dst : obj_addr = fp in
  let copied = copy_fields minor alloc_res.heap_out obj dst 0 wosize in
  dst_fields_valid_from_bounds fp wosize;
  copy_fields_frame_other_header minor alloc_res.heap_out obj dst src wosize;
  copy_fields_preserves_objects_aux
    minor alloc_res.heap_out obj dst 0 wosize;
  assert (objects zero_addr copied == objects zero_addr alloc_res.heap_out);
  assert (Seq.mem dst (objects zero_addr copied));
  assert (Seq.mem src (objects zero_addr copied));
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  set_promoted_tag_frame_other_header copied dst src tag

private let promote_object_head_split_frame_field0_from_alloc_single_chunk
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (src: obj_addr)
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
                  (MH.single_chunk_major_heap major) fp >= wosize + 2 /\
                (let alloc_res = SpecAlloc.alloc_spec major fp wosize in
                 Seq.mem src (objects zero_addr alloc_res.heap_out) /\
                 src <> (fp <: obj_addr) /\
                 U64.v (wosize_of_object src alloc_res.heap_out) >= 1))
      (ensures
        (let alloc_res = SpecAlloc.alloc_spec major fp wosize in
         let res = promote_object minor major obj fp wosize in
         read_word res.major_out src ==
         read_word alloc_res.heap_out src))
  =
  alloc_spec_head_split_alloc_wosize_single_chunk major fp wosize;
  promote_object_head_split_padding_noop_single_chunk minor major obj fp wosize;
  promote_object_success minor major obj fp wosize;
  let alloc_res = SpecAlloc.alloc_spec major fp wosize in
  let dst : obj_addr = fp in
  let copied = copy_fields minor alloc_res.heap_out obj dst 0 wosize in
  dst_fields_valid_from_bounds fp wosize;
  copy_fields_frame_other_field0 minor alloc_res.heap_out obj dst src wosize;
  copy_fields_frame_other_header minor alloc_res.heap_out obj dst src wosize;
  copy_fields_preserves_objects_aux
    minor alloc_res.heap_out obj dst 0 wosize;
  assert (objects zero_addr copied == objects zero_addr alloc_res.heap_out);
  assert (Seq.mem dst (objects zero_addr copied));
  assert (Seq.mem src (objects zero_addr copied));
  wosize_of_object_spec src alloc_res.heap_out;
  wosize_of_object_spec src copied;
  assert (read_word copied (hd_address src) ==
          read_word alloc_res.heap_out (hd_address src));
  assert (wosize_of_object src copied ==
          wosize_of_object src alloc_res.heap_out);
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  set_promoted_tag_frame_other_field0 copied dst src tag
#pop-options

/// Transfer the three chunked free-list shape predicates across a dense
/// single-chunk frame that preserves object enumeration and every live chain
/// node's header/link word.  The old chain must avoid the allocation target.
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
private let rec single_chunk_fl_shape_transfer_avoids
  (g0 g1: heap) (dst: obj_addr) (cur: U64.t) (fuel: nat)
  : Lemma
      (requires
        SpecMajorAlloc.major_fl_valid
          (MH.single_chunk_major_heap g0) cur fuel /\
        SpecMajorAlloc.major_fl_above_zero
          (MH.single_chunk_major_heap g0) cur fuel /\
        SpecMajorAlloc.major_fl_blocks_fit
          (MH.single_chunk_major_heap g0) cur fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          (MH.single_chunk_major_heap g0) cur fuel = true /\
        SpecMajorAlloc.major_fl_chain_avoids
          (MH.single_chunk_major_heap g0) cur dst fuel = true /\
        objects zero_addr g1 == objects zero_addr g0 /\
        (forall (src: obj_addr).
          Seq.mem src (objects zero_addr g0) /\ src <> dst ==>
          read_word g1 (hd_address src) == read_word g0 (hd_address src)) /\
        (forall (src: obj_addr).
          Seq.mem src (objects zero_addr g0) /\
          src <> dst /\
          U64.v (wosize_of_object src g0) >= 1 ==>
          read_word g1 src == read_word g0 src))
      (ensures
        SpecMajorAlloc.major_fl_valid
          (MH.single_chunk_major_heap g1) cur fuel /\
        SpecMajorAlloc.major_fl_above_zero
          (MH.single_chunk_major_heap g1) cur fuel /\
        SpecMajorAlloc.major_fl_blocks_fit
          (MH.single_chunk_major_heap g1) cur fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          (MH.single_chunk_major_heap g1) cur fuel = true)
      (decreases fuel)
  =
  let mh0 = MH.single_chunk_major_heap g0 in
  let mh1 = MH.single_chunk_major_heap g1 in
  if fuel = 0 then begin
    SpecMajorAlloc.major_fl_valid_zero mh1 cur;
    SpecMajorAlloc.major_fl_above_zero_fuel_0 mh1 cur;
    if cur = 0UL ||
       U64.v cur < U64.v mword ||
       U64.v cur >= heap_size ||
       U64.v cur % U64.v mword <> 0 then
      SpecMajorAlloc.major_fl_chain_terminates_terminal mh1 cur fuel
    else begin
      SpecMajorAlloc.major_fl_chain_terminates_valid_zero mh0 cur;
      assert False
    end
  end else if cur = 0UL then begin
    SpecMajorAlloc.major_fl_valid_null mh1 fuel;
    SpecMajorAlloc.major_fl_above_zero_null mh1 fuel;
    SpecMajorAlloc.major_fl_blocks_fit_null mh1 fuel;
    SpecMajorAlloc.major_fl_chain_terminates_null mh1 fuel
  end else begin
    assert (fuel > 0);
    SpecMajorAlloc.major_fl_above_zero_current mh0 cur fuel;
    assert (U64.v cur >= U64.v zero_addr + U64.v mword);
    assert (U64.v cur >= U64.v mword);
    assert (U64.v cur < heap_size);
    assert (U64.v cur % U64.v mword == 0);
    assert (fuel - 1 >= 0);
    let fuel' : f:nat{f < fuel} = fuel - 1 in
    let x : obj_addr = cur in
    let xhd = hd_address x in
    hd_address_spec x;
    hd_address_bounds x;
    SpecMajorAlloc.major_fl_chain_avoids_head_ne mh0 cur dst fuel;
    assert (x <> dst);
    SpecMajorAlloc.major_fl_valid_gives_mem mh0 cur fuel;
    MH.single_chunk_major_objects_compat g0;
    assert (Seq.mem x (objects zero_addr g0));
    assert (Seq.mem x (objects zero_addr g1));
    MH.single_chunk_major_objects_compat g1;
    SpecMajorAlloc.major_fl_valid_gives_wosize mh0 cur fuel;
    SpecMajorAlloc.major_fl_valid_link_lookup_index mh0 cur fuel;
    SpecMajorAlloc.major_fl_blocks_fit_current mh0 cur fuel;
    match MH.read_word_in_major mh0 xhd with
    | None -> assert False
    | Some hdr0 ->
      match MH.read_word_in_major mh0 x with
      | None -> assert False
      | Some next ->
        wosize_of_object_spec x g0;
        MH.single_chunk_read_word_compat g0 xhd;
        assert (read_word g0 xhd == hdr0);
        assert (U64.v (wosize_of_object x g0) >= 1);
        MH.single_chunk_read_word_compat g0 x;
        assert (read_word g0 x == next);
        assert (read_word g1 xhd == read_word g0 xhd);
        assert (read_word g1 x == read_word g0 x);
        MH.single_chunk_read_word_compat g1 xhd;
        MH.single_chunk_read_word_compat g1 x;
        assert (MH.read_word_in_major mh1 xhd == Some hdr0);
        assert (MH.read_word_in_major mh1 x == Some next);
        SpecMajorAlloc.major_fl_valid_next mh0 cur fuel;
        SpecMajorAlloc.major_fl_above_zero_next mh0 x fuel next;
        SpecMajorAlloc.major_fl_blocks_fit_next mh0 x fuel next;
        SpecMajorAlloc.major_fl_chain_avoids_tail mh0 cur dst fuel;
        SpecMajorAlloc.major_fl_chain_terminates_tail mh0 cur fuel;
        assert (SpecMajorAlloc.major_fl_chain_avoids
                  mh0 next dst fuel' = true);
        assert (SpecMajorAlloc.major_fl_chain_terminates
                  mh0 next fuel' = true);
        single_chunk_fl_shape_transfer_avoids
          g0 g1 dst next fuel';
        assert (SpecMajorAlloc.major_fl_valid mh1 next fuel');
        assert (SpecMajorAlloc.major_fl_above_zero mh1 next fuel');
        assert (SpecMajorAlloc.major_fl_blocks_fit mh1 next fuel');
        assert (SpecMajorAlloc.major_fl_chain_terminates
                  mh1 next fuel' = true);
        MH.read_word_in_major_lookup_index mh1 xhd hdr0;
        assert (MH.lookup_chunk_index mh1 xhd ==
                Some (MH.lookup_chunk_index_value mh1 xhd));
        assert (MH.chunk_end
                  (Seq.index mh1 (MH.lookup_chunk_index_value mh1 xhd)) ==
                heap_size);
        assert (MH.chunk_end
                  (Seq.index mh0 (MH.lookup_chunk_index_value mh0 xhd)) ==
                heap_size);
        assert (U64.v xhd + (1 + U64.v (getWosize hdr0)) *
                  U64.v mword <= heap_size);
        assert (next <> cur);
        SpecMajorAlloc.major_fl_valid_step_from_mem mh1 x fuel hdr0 next;
        SpecMajorAlloc.major_fl_above_zero_step mh1 x fuel next;
        SpecMajorAlloc.major_fl_blocks_fit_step mh1 x fuel hdr0 next;
        SpecMajorAlloc.major_fl_chain_terminates_step mh1 cur fuel
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
private let rec chunked_fl_shape_transfer_avoids
  (mh0 mh1: MH.major_heap) (dst: obj_addr) (cur: U64.t) (fuel: nat)
  : Lemma
      (requires
        SpecMajorAlloc.major_fl_valid mh0 cur fuel /\
        SpecMajorAlloc.major_fl_above_zero mh0 cur fuel /\
        SpecMajorAlloc.major_fl_blocks_fit mh0 cur fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh0 cur fuel = true /\
        SpecMajorAlloc.major_fl_chain_avoids mh0 cur dst fuel = true /\
        MH.well_formed_major_heap mh1 /\
        MH.major_objects mh1 == MH.major_objects mh0 /\
        (forall (src: obj_addr).
          Seq.mem src (MH.major_objects mh0) /\ src <> dst ==>
          MH.read_word_in_major mh1 (hd_address src) ==
          MH.read_word_in_major mh0 (hd_address src)) /\
        (forall (src: obj_addr).
          Seq.mem src (MH.major_objects mh0) /\
          src <> dst /\
          (match MH.read_word_in_major mh0 (hd_address src) with
           | Some hdr -> U64.v (getWosize hdr) >= 1
           | None -> False) ==>
          MH.read_word_in_major mh1 src ==
          MH.read_word_in_major mh0 src))
      (ensures
        SpecMajorAlloc.major_fl_valid mh1 cur fuel /\
        SpecMajorAlloc.major_fl_above_zero mh1 cur fuel /\
        SpecMajorAlloc.major_fl_blocks_fit mh1 cur fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh1 cur fuel = true)
      (decreases fuel)
  =
  if fuel = 0 then begin
    SpecMajorAlloc.major_fl_valid_zero mh1 cur;
    SpecMajorAlloc.major_fl_above_zero_fuel_0 mh1 cur;
    if cur = 0UL ||
       U64.v cur < U64.v mword ||
       U64.v cur >= heap_size ||
       U64.v cur % U64.v mword <> 0 then
      SpecMajorAlloc.major_fl_chain_terminates_terminal mh1 cur fuel
    else begin
      SpecMajorAlloc.major_fl_chain_terminates_valid_zero mh0 cur;
      assert False
    end
  end else if cur = 0UL then begin
    SpecMajorAlloc.major_fl_valid_null mh1 fuel;
    SpecMajorAlloc.major_fl_above_zero_null mh1 fuel;
    SpecMajorAlloc.major_fl_blocks_fit_null mh1 fuel;
    SpecMajorAlloc.major_fl_chain_terminates_null mh1 fuel
  end else begin
    assert (fuel > 0);
    SpecMajorAlloc.major_fl_above_zero_current mh0 cur fuel;
    assert (U64.v cur >= U64.v zero_addr + U64.v mword);
    assert (U64.v cur >= U64.v mword);
    assert (U64.v cur < heap_size);
    assert (U64.v cur % U64.v mword == 0);
    assert (fuel - 1 >= 0);
    let fuel' : f:nat{f < fuel} = fuel - 1 in
    let x : obj_addr = cur in
    let xhd = hd_address x in
    SpecMajorAlloc.major_fl_chain_avoids_head_ne mh0 cur dst fuel;
    assert (x <> dst);
    SpecMajorAlloc.major_fl_valid_gives_mem mh0 cur fuel;
    assert (Seq.mem x (MH.major_objects mh0));
    assert (Seq.mem x (MH.major_objects mh1));
    SpecMajorAlloc.major_fl_valid_gives_wosize mh0 cur fuel;
    SpecMajorAlloc.major_fl_valid_next mh0 cur fuel;
    SpecMajorAlloc.major_fl_blocks_fit_current mh0 cur fuel;
    SpecMajorAlloc.major_fl_chain_avoids_tail mh0 cur dst fuel;
    SpecMajorAlloc.major_fl_chain_terminates_tail mh0 cur fuel;
    match MH.read_word_in_major mh0 xhd with
    | None -> assert False
    | Some hdr ->
      assert (U64.v (getWosize hdr) >= 1);
      assert (MH.read_word_in_major mh1 xhd == Some hdr);
      match MH.read_word_in_major mh0 x with
      | None -> assert False
      | Some next ->
        assert (MH.read_word_in_major mh1 x == Some next);
        assert (next <> cur);
        SpecMajorAlloc.major_fl_above_zero_next mh0 x fuel next;
        SpecMajorAlloc.major_fl_blocks_fit_next mh0 x fuel next;
        assert (SpecMajorAlloc.major_fl_valid mh0 next fuel');
        assert (SpecMajorAlloc.major_fl_above_zero mh0 next fuel');
        assert (SpecMajorAlloc.major_fl_blocks_fit mh0 next fuel');
        assert (SpecMajorAlloc.major_fl_chain_avoids mh0 next dst fuel' = true);
        assert (SpecMajorAlloc.major_fl_chain_terminates mh0 next fuel' = true);
        chunked_fl_shape_transfer_avoids mh0 mh1 dst next fuel';
        assert (SpecMajorAlloc.major_fl_valid mh1 next fuel');
        assert (SpecMajorAlloc.major_fl_above_zero mh1 next fuel');
        assert (SpecMajorAlloc.major_fl_blocks_fit mh1 next fuel');
        assert (SpecMajorAlloc.major_fl_chain_terminates mh1 next fuel' = true);
        SpecMajorAlloc.major_fl_valid_step_from_mem mh1 x fuel hdr next;
        SpecMajorAlloc.major_fl_above_zero_step mh1 x fuel next;
        MH.read_word_in_major_lookup_index mh1 xhd hdr;
        let idx = MH.lookup_chunk_index_value mh1 xhd in
        assert (MH.lookup_chunk_index mh1 xhd == Some idx);
        assert (idx < Seq.length mh1);
        assert (MH.word_in_chunk (Seq.index mh1 idx) xhd);
        assert (MH.read_word_in_chunk (Seq.index mh1 idx) xhd == hdr);
        MH.major_objects_member_in_lookup_chunk mh1 idx x;
        assert (Seq.mem x (MH.objects_in_chunk (Seq.index mh1 idx)));
        MH.objects_in_chunk_member_header_fits (Seq.index mh1 idx) x;
        assert (MH.object_header_size_fits_in_chunk (Seq.index mh1 idx) x);
        assert (U64.v xhd + (1 + U64.v (getWosize hdr)) *
                  U64.v mword <= MH.chunk_end (Seq.index mh1 idx));
        SpecMajorAlloc.major_fl_blocks_fit_step mh1 x fuel hdr next;
        assert
          (match MH.read_word_in_major mh1 (cur <: obj_addr) with
           | Some next' ->
             SpecMajorAlloc.major_fl_chain_terminates mh1 next' fuel' = true
           | None -> True);
        SpecMajorAlloc.major_fl_chain_terminates_step mh1 cur fuel
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --split_queries always"
private let chunked_member_header_disjoint_from_dst_writes
  (mh: MH.major_heap) (dst src: obj_addr) (dst_wz: nat) (dst_hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem dst (MH.major_objects mh) /\
        Seq.mem src (MH.major_objects mh) /\
        src <> dst /\
        MH.read_word_in_major mh (hd_address dst) == Some dst_hdr /\
        U64.v (getWosize dst_hdr) == dst_wz)
      (ensures
        (U64.v (hd_address src) + U64.v mword <= U64.v dst \/
         U64.v dst + dst_wz * U64.v mword <= U64.v (hd_address src)) /\
        (U64.v (hd_address src) + U64.v mword <= U64.v (hd_address dst) \/
         U64.v (hd_address dst) + U64.v mword <= U64.v (hd_address src)))
  =
  let dst_hd = hd_address dst in
  let src_hd = hd_address src in
  hd_address_spec dst;
  hd_address_spec src;
  assert (U64.v dst_hd + U64.v mword == U64.v dst);
  assert (U64.v src_hd + U64.v mword == U64.v src);
  if U64.v src < U64.v dst then begin
    MH.word_aligned_gt_at_least_mword (U64.v dst) (U64.v src);
    assert (U64.v dst >= U64.v src + U64.v mword);
    assert (U64.v src <= U64.v dst_hd);
    assert (U64.v src_hd + U64.v mword <= U64.v dst);
    assert (U64.v src_hd + U64.v mword <= U64.v dst_hd)
  end else begin
    assert (U64.v dst < U64.v src);
    MH.word_aligned_gt_at_least_mword (U64.v src) (U64.v dst);
    assert (U64.v src >= U64.v dst + U64.v mword);
    assert (U64.v dst <= U64.v src_hd);
    assert (U64.v dst_hd + U64.v mword <= U64.v src_hd);
    MH.read_word_in_major_lookup_index mh dst_hd dst_hdr;
    let didx = MH.lookup_chunk_index_value mh dst_hd in
    assert (MH.lookup_chunk_index mh dst_hd == Some didx);
    assert (didx < Seq.length mh);
    assert (MH.word_in_chunk (Seq.index mh didx) dst_hd);
    assert (MH.read_word_in_chunk (Seq.index mh didx) dst_hd == dst_hdr);
    MH.major_objects_member_in_lookup_chunk mh didx dst;
    assert (Seq.mem dst (MH.objects_in_chunk (Seq.index mh didx)));
    MH.objects_in_chunk_member_header_fits (Seq.index mh didx) dst;
    assert (MH.object_header_size_fits_in_chunk (Seq.index mh didx) dst);
    assert (MH.object_wosize_in_chunk (Seq.index mh didx) dst == dst_wz);
    MH.major_objects_member_header_read_some mh src;
    match MH.read_word_in_major mh src_hd with
    | None -> assert False
    | Some src_hdr ->
      MH.read_word_in_major_lookup_index mh src_hd src_hdr;
      let sidx = MH.lookup_chunk_index_value mh src_hd in
      assert (MH.lookup_chunk_index mh src_hd == Some sidx);
      assert (sidx < Seq.length mh);
      assert (MH.word_in_chunk (Seq.index mh sidx) src_hd);
      MH.major_objects_member_in_lookup_chunk mh sidx src;
      assert (Seq.mem src (MH.objects_in_chunk (Seq.index mh sidx)));
      if didx = sidx then begin
        assert (Seq.index mh didx == Seq.index mh sidx);
        MH.objects_in_chunk_separated (Seq.index mh didx) dst src;
        assert (U64.v src > U64.v dst + dst_wz * U64.v mword);
        SpecMajorAlloc.aligned_plus_word_product (U64.v dst) dst_wz;
        assert ((U64.v dst + dst_wz * U64.v mword) %
                  U64.v mword == 0);
        MH.word_aligned_gt_at_least_mword
          (U64.v src) (U64.v dst + dst_wz * U64.v mword);
        assert (U64.v src >=
                U64.v dst + dst_wz * U64.v mword + U64.v mword);
        assert (U64.v dst + dst_wz * U64.v mword <= U64.v src_hd)
      end else begin
        assert (didx <> sidx);
        let dc = Seq.index mh didx in
        let sc = Seq.index mh sidx in
        if didx < sidx then
          SpecMajorAlloc.chunks_pairwise_index_disjoint mh didx sidx
        else begin
          assert (sidx < didx);
          SpecMajorAlloc.chunks_pairwise_index_disjoint mh sidx didx;
          MH.chunks_disjoint_symmetric sc dc
        end;
        if MH.chunk_end dc <= MH.chunk_start sc then begin
          assert (U64.v dst + dst_wz * U64.v mword <= MH.chunk_end dc);
          assert (MH.chunk_start sc <= U64.v src_hd);
          assert (U64.v dst + dst_wz * U64.v mword <= U64.v src_hd)
        end else begin
          assert (MH.chunk_end sc <= MH.chunk_start dc);
          MH.objects_in_chunk_member_in_chunk sc src;
          assert (MH.obj_addr_in_chunk sc src);
          assert (U64.v src < MH.chunk_end sc);
          assert (MH.chunk_start dc <= U64.v dst_hd);
          assert (U64.v dst_hd < U64.v dst);
          assert (U64.v dst < U64.v src);
          assert False
        end
      end
  end

private let chunked_member_field0_disjoint_from_dst_writes
  (mh: MH.major_heap) (dst src: obj_addr)
  (dst_wz: nat) (dst_hdr src_hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem dst (MH.major_objects mh) /\
        Seq.mem src (MH.major_objects mh) /\
        src <> dst /\
        MH.read_word_in_major mh (hd_address dst) == Some dst_hdr /\
        U64.v (getWosize dst_hdr) == dst_wz /\
        MH.read_word_in_major mh (hd_address src) == Some src_hdr /\
        U64.v (getWosize src_hdr) >= 1)
      (ensures
        (U64.v src + U64.v mword <= U64.v dst \/
         U64.v dst + dst_wz * U64.v mword <= U64.v src) /\
        (U64.v src + U64.v mword <= U64.v (hd_address dst) \/
         U64.v (hd_address dst) + U64.v mword <= U64.v src))
  =
  let dst_hd = hd_address dst in
  let src_hd = hd_address src in
  hd_address_spec dst;
  hd_address_spec src;
  assert (U64.v dst_hd + U64.v mword == U64.v dst);
  assert (U64.v src_hd + U64.v mword == U64.v src);
  if U64.v src < U64.v dst then begin
    MH.word_aligned_gt_at_least_mword (U64.v dst) (U64.v src);
    assert (U64.v src + U64.v mword <= U64.v dst);
    let src_wz = U64.v (getWosize src_hdr) in
    chunked_member_header_disjoint_from_dst_writes
      mh src dst src_wz src_hdr;
    assert (U64.v dst_hd + U64.v mword == U64.v dst);
    assert (~(U64.v (hd_address dst) + U64.v mword <= U64.v src));
    assert (U64.v src + src_wz * U64.v mword <= U64.v dst_hd);
    FStar.Math.Lemmas.lemma_mult_le_right
      (U64.v mword) 1 src_wz;
    assert (U64.v mword <= src_wz * U64.v mword);
    assert (U64.v src + U64.v mword <= U64.v dst_hd)
  end else begin
    assert (U64.v dst < U64.v src);
    chunked_member_header_disjoint_from_dst_writes
      mh dst src dst_wz dst_hdr;
    assert (~(U64.v src_hd + U64.v mword <= U64.v dst));
    assert (U64.v dst + dst_wz * U64.v mword <= U64.v src_hd);
    assert (U64.v dst + dst_wz * U64.v mword <= U64.v src);
    assert (U64.v dst_hd + U64.v mword <= U64.v src)
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --split_queries always"
let chunked_promote_object_head_split_preserves_chunked_alloc_shape
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
          Seq.mem (fp <: obj_addr)
            (MH.major_objects alloc_res.major_alloc_out) /\
          Seq.mem (fp <: obj_addr) (MH.major_objects res.major_out))))
  =
  GenInv.chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAlloc.major_fl_above_zero_current mh fp fuel;
  assert (U64.v fp >= U64.v zero_addr + U64.v mword);
  assert (U64.v fp >= U64.v mword);
  assert (U64.v fp < heap_size);
  assert (U64.v fp % U64.v mword == 0);
  let dst : obj_addr = fp in
  let hd = hd_address dst in
  SpecMajorAlloc.major_fl_head_wosize_current mh fp fuel;
  SpecMajorAlloc.major_fl_head_block_fits_current mh fp fuel;
  SpecMajorAlloc.major_fl_valid_link_lookup_index mh fp fuel;
  let idx = MH.lookup_chunk_index_value mh hd in
  assert (MH.lookup_chunk_index mh hd == Some idx);
  assert (idx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh idx) hd);
  match MH.read_word_in_major mh hd with
  | None -> assert False
  | Some old_hdr ->
    let block_wz = U64.v (getWosize old_hdr) in
    assert (SpecMajorAlloc.major_fl_head_wosize mh fp == block_wz);
    assert (block_wz < pow2 54);
    assert (block_wz >= wosize + 2);
    assert (block_wz - wosize >= 2);
    assert (wosize < pow2 54);
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    assert (wosize < pow2 64);
    assert (FStar.UInt.size wosize 64);
    match MH.read_word_in_major mh dst with
    | None -> assert False
    | Some next_fp ->
      let c = Seq.index mh idx in
      MH.read_word_in_major_at_lookup_index mh hd idx;
      assert (MH.read_word_in_chunk c hd == old_hdr);
      SpecMajorAlloc.major_fl_valid_gives_mem mh fp fuel;
      assert (Seq.mem dst (MH.major_objects mh));
      MH.major_objects_member_in_lookup_chunk mh idx dst;
      assert (Seq.mem dst (MH.objects_in_chunk c));
      assert (MH.object_wosize_in_chunk c dst == block_wz);
      assert (U64.v hd + (1 + block_wz) * U64.v mword <= MH.chunk_end c);
      assert (U64.v mword == 8);
      let rem_hd_nat = U64.v hd + (1 + wosize) * 8 in
      let rem_obj_nat = rem_hd_nat + U64.v mword in
      FStar.Math.Lemmas.distributivity_add_left (1 + wosize) 1 8;
      assert ((1 + wosize) * 8 + 8 == (wosize + 2) * 8);
      FStar.Math.Lemmas.paren_add_right (U64.v hd) ((1 + wosize) * 8) 8;
      assert (rem_obj_nat == U64.v hd + (wosize + 2) * 8);
      assert (wosize + 3 <= 1 + block_wz);
      assert (rem_obj_nat + 8 == U64.v hd + (wosize + 3) * 8);
      assert (rem_obj_nat + 8 <= U64.v hd + (1 + block_wz) * 8);
      assert (rem_obj_nat + 8 <= MH.chunk_end c);
      assert (MH.chunk_end c <= heap_size);
      assert (rem_hd_nat < heap_size);
      assert (rem_obj_nat < heap_size);
      assert (heap_size < pow2 64);
      assert (rem_hd_nat < pow2 64);
      assert (rem_obj_nat < pow2 64);
      assert (rem_obj_nat >= U64.v mword);
      hd_address_spec dst;
      SpecMajorAlloc.aligned_plus_word_product (U64.v hd) (1 + wosize);
      assert (rem_hd_nat % U64.v mword == 0);
      SpecMajorAlloc.aligned_plus_word_product (U64.v hd) (wosize + 2);
      assert (rem_obj_nat % U64.v mword == 0);
      let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
      let rem_obj : obj_addr = U64.uint_to_t rem_obj_nat in
      assert (U64.v rem_hd == rem_hd_nat);
      assert (U64.v rem_obj == rem_obj_nat);
      assert (U64.v rem_obj == U64.v rem_hd + U64.v mword);
      SpecMajorAlloc.active_head_split_remainder_words_in_chunk
        c hd block_wz wosize rem_hd rem_obj;
      let rem_wz = block_wz - wosize - 1 in
      assert (rem_wz >= 1);
      assert (rem_wz < pow2 54);
      assert (rem_wz < pow2 64);
      assert (FStar.UInt.size rem_wz 64);
      let rem_wz_u : w:U64.t{U64.v w == rem_wz /\ U64.v w < pow2 54} =
        U64.uint_to_t rem_wz in
      assert (U64.v rem_wz_u == block_wz - wosize - 1);
      SpecMajorAlloc.major_alloc_head_split
        mh dst wosize fuel old_hdr next_fp rem_hd rem_obj;
      let alloc_res =
        SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
      assert (alloc_res.major_obj_out == fp);
      assert (alloc_res.major_fp_out == rem_obj);
      assert (alloc_res.major_fp_out <> 0UL);
      SpecMajorAllocSplitShape.major_alloc_head_split_preserves_alloc_shape
        mh fp wosize fuel;
      SpecMajorAllocSplitShape.major_alloc_head_split_remainder_avoids_allocated_head
        mh fp wosize fuel;
      SpecMajorAllocSplitShape.head_split_preserves_allocated_head_node_facts
        mh idx dst old_hdr next_fp wosize block_wz next_fp
        rem_wz_u rem_hd rem_obj;
      let alloc_hdr =
        SpecAlloc.make_header (U64.uint_to_t wosize)
          SpecAlloc.white_bits 0UL in
      assert (alloc_res.major_alloc_out ==
              SpecMajorAllocSplitShape.head_split_heap
                mh dst wosize next_fp rem_wz_u rem_hd rem_obj);
      assert (Seq.mem dst (MH.major_objects alloc_res.major_alloc_out));
      assert (MH.read_word_in_major alloc_res.major_alloc_out hd ==
              Some alloc_hdr);
      AllocHeader.make_header_getWosize
        (U64.uint_to_t wosize) SpecAlloc.white_bits 0UL;
      assert (U64.v (getWosize alloc_hdr) == wosize);
      assert (MH.lookup_chunk_index alloc_res.major_alloc_out hd == Some idx);
      assert (idx < Seq.length alloc_res.major_alloc_out);
      ChunkedPromote.chunked_copy_fields_preserves_major_objects
        minor alloc_res.major_alloc_out obj fp 0 wosize idx alloc_hdr;
      let copied =
        ChunkedPromote.chunked_copy_fields
          minor alloc_res.major_alloc_out obj fp 0 wosize in
      assert (MH.well_formed_major_heap copied);
      assert (MH.major_objects copied ==
              MH.major_objects alloc_res.major_alloc_out);
      assert (MH.read_word_in_major copied hd == Some alloc_hdr);
      MH.read_word_in_major_lookup_index copied hd alloc_hdr;
      let copied_idx = MH.lookup_chunk_index_value copied hd in
      assert (MH.lookup_chunk_index copied hd == Some copied_idx);
      assert (Seq.mem dst (MH.major_objects copied));
      let tag = minor_tag minor obj in
      minor_tag_bound minor obj;
      ChunkedPromote.chunked_set_promoted_tag_preserves_major_objects
        copied fp tag copied_idx alloc_hdr;
      let final_major = ChunkedPromote.chunked_set_promoted_tag copied fp tag in
      assert (MH.well_formed_major_heap final_major);
      assert (MH.major_objects final_major == MH.major_objects copied);
      chunked_promote_head_split_padding_noop minor mh obj fp wosize fuel;
      ChunkedPromote.chunked_promote_object_success
        minor mh obj fp wosize fuel;
      let res =
        ChunkedPromote.chunked_promote_object_with_fuel
          minor mh obj fp wosize fuel in
      assert (ChunkedPromote.chunked_zero_promote_padding copied fp wosize ==
              copied);
      assert (res.major_out == final_major);
      assert (res.new_addr == fp);
      assert (res.fp_out == alloc_res.major_fp_out);
      assert (res.fp_out <> 0UL);
      assert (SpecMajorAlloc.major_fl_valid
                alloc_res.major_alloc_out alloc_res.major_fp_out fuel);
      assert (SpecMajorAlloc.major_fl_above_zero
                alloc_res.major_alloc_out alloc_res.major_fp_out fuel);
      assert (SpecMajorAlloc.major_fl_blocks_fit
                alloc_res.major_alloc_out alloc_res.major_fp_out fuel);
      assert (SpecMajorAlloc.major_fl_chain_terminates
                alloc_res.major_alloc_out alloc_res.major_fp_out fuel = true);
      assert (SpecMajorAlloc.major_fl_chain_avoids
                alloc_res.major_alloc_out alloc_res.major_fp_out dst fuel = true);
      let header_frame (src: obj_addr)
        : Lemma
            (requires Seq.mem src (MH.major_objects alloc_res.major_alloc_out) /\
                      src <> dst)
            (ensures MH.read_word_in_major final_major (hd_address src) ==
                     MH.read_word_in_major alloc_res.major_alloc_out
                       (hd_address src))
        =
        let src_hd = hd_address src in
        MH.major_objects_member_header_read_some
          alloc_res.major_alloc_out src;
        match MH.read_word_in_major alloc_res.major_alloc_out src_hd with
        | None -> assert False
        | Some old ->
          chunked_member_header_disjoint_from_dst_writes
            alloc_res.major_alloc_out dst src wosize alloc_hdr;
          if U64.v src_hd + U64.v mword <= U64.v dst then
            ChunkedPromote.chunked_copy_fields_frame_before
              minor alloc_res.major_alloc_out obj fp 0 wosize src_hd old
          else begin
            assert (U64.v dst + wosize * U64.v mword <= U64.v src_hd);
            ChunkedPromote.chunked_copy_fields_frame_after
              minor alloc_res.major_alloc_out obj fp 0 wosize src_hd old
          end;
          assert (MH.read_word_in_major copied src_hd == Some old);
          if U64.v src_hd + U64.v mword <= U64.v hd then
            ChunkedPromote.chunked_set_promoted_tag_read_frame
              copied fp tag src_hd old
          else begin
            assert (U64.v hd + U64.v mword <= U64.v src_hd);
            ChunkedPromote.chunked_set_promoted_tag_read_frame
              copied fp tag src_hd old
          end
      in
      FStar.Classical.forall_intro
        (FStar.Classical.move_requires header_frame);
      let link_frame (src: obj_addr)
        : Lemma
            (requires Seq.mem src (MH.major_objects alloc_res.major_alloc_out) /\
                      src <> dst /\
                      (match
                        MH.read_word_in_major
                          alloc_res.major_alloc_out (hd_address src)
                       with
                       | Some hdr -> U64.v (getWosize hdr) >= 1
                       | None -> False))
            (ensures MH.read_word_in_major final_major src ==
                     MH.read_word_in_major alloc_res.major_alloc_out src)
        =
        let src_hd = hd_address src in
        MH.major_objects_member_header_read_some
          alloc_res.major_alloc_out src;
        match MH.read_word_in_major alloc_res.major_alloc_out src_hd with
        | None -> assert False
        | Some src_hdr ->
          assert (U64.v (getWosize src_hdr) >= 1);
          MH.major_objects_member_field0_read_some
            alloc_res.major_alloc_out src src_hdr;
          match MH.read_word_in_major alloc_res.major_alloc_out src with
          | None -> assert False
          | Some old ->
            chunked_member_field0_disjoint_from_dst_writes
              alloc_res.major_alloc_out dst src wosize alloc_hdr src_hdr;
            if U64.v src + U64.v mword <= U64.v dst then
              ChunkedPromote.chunked_copy_fields_frame_before
                minor alloc_res.major_alloc_out obj fp 0 wosize src old
            else begin
              assert (U64.v dst + wosize * U64.v mword <= U64.v src);
              ChunkedPromote.chunked_copy_fields_frame_after
                minor alloc_res.major_alloc_out obj fp 0 wosize src old
            end;
            assert (MH.read_word_in_major copied src == Some old);
            if U64.v src + U64.v mword <= U64.v hd then
              ChunkedPromote.chunked_set_promoted_tag_read_frame
                copied fp tag src old
            else begin
              assert (U64.v hd + U64.v mword <= U64.v src);
              ChunkedPromote.chunked_set_promoted_tag_read_frame
                copied fp tag src old
            end
      in
      FStar.Classical.forall_intro
        (FStar.Classical.move_requires link_frame);
      chunked_fl_shape_transfer_avoids
        alloc_res.major_alloc_out final_major dst alloc_res.major_fp_out fuel;
      assert (SpecMajorAlloc.major_fl_valid final_major res.fp_out fuel);
      assert (SpecMajorAlloc.major_fl_above_zero final_major res.fp_out fuel);
      assert (SpecMajorAlloc.major_fl_blocks_fit final_major res.fp_out fuel);
      assert (SpecMajorAlloc.major_fl_chain_terminates
                final_major res.fp_out fuel = true);
      assert (Seq.mem dst (MH.major_objects final_major));
      GenInv.chunked_major_alloc_shape_intro final_major res.fp_out fuel
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --split_queries always"
let chunked_promote_object_head_split_preserves_remaining_head_wosize
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
  assert (SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2);
  GenInv.chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAlloc.major_alloc_head_split_preserves_head_wosize
    mh fp wosize fuel remaining;
  SpecMajorAllocSplitShape.major_alloc_head_split_preserves_alloc_shape
    mh fp wosize fuel;
  SpecMajorAllocSplitShape.major_alloc_head_split_remainder_avoids_allocated_head
    mh fp wosize fuel;
  SpecMajorAlloc.major_fl_head_wosize_current mh fp fuel;
  match MH.read_word_in_major mh (hd_address (fp <: obj_addr)) with
  | None -> assert False
  | Some old_hdr ->
    let block_wz = U64.v (getWosize old_hdr) in
    assert (SpecMajorAlloc.major_fl_head_wosize mh fp == block_wz);
    assert (block_wz < pow2 54);
    assert (wosize < pow2 54);
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    assert (wosize < pow2 64);
    assert (FStar.UInt.size wosize 64);
  chunked_alloc_head_split_alloc_header_wosize mh fp wosize fuel;
  chunked_promote_head_split_padding_noop minor mh obj fp wosize fuel;
  chunked_promote_object_head_split_preserves_chunked_alloc_shape
    minor mh obj fp wosize fuel;
  let alloc_res =
    SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
  let res =
    ChunkedPromote.chunked_promote_object_with_fuel
      minor mh obj fp wosize fuel in
  ChunkedPromote.chunked_promote_object_success
    minor mh obj fp wosize fuel;
  assert (alloc_res.major_obj_out == fp);
  assert (res.new_addr == fp);
  assert (res.fp_out == alloc_res.major_fp_out);
  assert (res.fp_out <> 0UL);
  assert (SpecMajorAlloc.major_fl_valid
            alloc_res.major_alloc_out alloc_res.major_fp_out fuel);
  assert (SpecMajorAlloc.major_fl_above_zero
            alloc_res.major_alloc_out alloc_res.major_fp_out fuel);
  assert (SpecMajorAlloc.major_fl_blocks_fit
            alloc_res.major_alloc_out alloc_res.major_fp_out fuel);
  assert (SpecMajorAlloc.major_fl_head_wosize
            alloc_res.major_alloc_out alloc_res.major_fp_out >= remaining);
  SpecMajorAlloc.major_fl_above_zero_current
    alloc_res.major_alloc_out alloc_res.major_fp_out fuel;
  assert (U64.v alloc_res.major_fp_out >= U64.v zero_addr + U64.v mword);
  assert (U64.v alloc_res.major_fp_out >= U64.v mword);
  assert (U64.v alloc_res.major_fp_out < heap_size);
  assert (U64.v alloc_res.major_fp_out % U64.v mword == 0);
  let dst : obj_addr = fp in
  let rem : obj_addr = alloc_res.major_fp_out in
  assert (Seq.mem dst (MH.major_objects alloc_res.major_alloc_out));
  assert (SpecMajorAlloc.major_fl_chain_avoids
            alloc_res.major_alloc_out alloc_res.major_fp_out dst fuel = true);
  SpecMajorAlloc.major_fl_chain_avoids_head_ne
    alloc_res.major_alloc_out alloc_res.major_fp_out dst fuel;
  assert (rem <> dst);
  let mem_goal = Seq.mem rem (MH.major_objects alloc_res.major_alloc_out) in
  let prove_mem (new_fp: obj_addr)
    : Lemma
        (requires new_fp == alloc_res.major_fp_out /\
                  Seq.mem new_fp (MH.major_objects alloc_res.major_alloc_out))
        (ensures mem_goal)
    =
    assert (new_fp == rem)
  in
  FStar.Classical.exists_elim mem_goal #obj_addr
    #(fun new_fp ->
        new_fp == alloc_res.major_fp_out /\
        Seq.mem new_fp (MH.major_objects alloc_res.major_alloc_out))
    ()
    (fun new_fp -> FStar.Classical.move_requires prove_mem new_fp);
  let dst_hd = hd_address dst in
  let rem_hd = hd_address rem in
  let alloc_hdr =
    SpecAlloc.make_header (U64.uint_to_t wosize)
      SpecAlloc.white_bits 0UL in
  assert (MH.read_word_in_major alloc_res.major_alloc_out dst_hd ==
          Some alloc_hdr);
  AllocHeader.make_header_getWosize
    (U64.uint_to_t wosize) SpecAlloc.white_bits 0UL;
  assert (U64.v (getWosize alloc_hdr) == wosize);
  let copied =
    ChunkedPromote.chunked_copy_fields
      minor alloc_res.major_alloc_out obj fp 0 wosize in
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  let final_major =
    ChunkedPromote.chunked_set_promoted_tag copied fp tag in
  assert (ChunkedPromote.chunked_zero_promote_padding copied fp wosize ==
          copied);
  assert (res.major_out == final_major);
  let rem_header_frame ()
    : Lemma
        (ensures
          MH.read_word_in_major final_major rem_hd ==
          MH.read_word_in_major alloc_res.major_alloc_out rem_hd)
  =
    MH.major_objects_member_header_read_some alloc_res.major_alloc_out rem;
    match MH.read_word_in_major alloc_res.major_alloc_out rem_hd with
    | None -> assert False
    | Some old ->
      chunked_member_header_disjoint_from_dst_writes
        alloc_res.major_alloc_out dst rem wosize alloc_hdr;
      assert (U64.v fp == U64.v dst);
      if U64.v rem_hd + U64.v mword <= U64.v dst then begin
        assert (MH.read_word_in_major alloc_res.major_alloc_out rem_hd ==
                Some old);
        assert (U64.v rem_hd + U64.v mword <= U64.v fp);
        assert (U64.v rem_hd + U64.v mword <=
                U64.v fp + 0 * U64.v mword);
        ChunkedPromote.chunked_copy_fields_frame_before
          minor alloc_res.major_alloc_out obj fp 0 wosize rem_hd old
      end
      else begin
        assert (MH.read_word_in_major alloc_res.major_alloc_out rem_hd ==
                Some old);
        assert (U64.v dst + wosize * U64.v mword <= U64.v rem_hd);
        assert (U64.v fp + wosize * U64.v mword <= U64.v rem_hd);
        ChunkedPromote.chunked_copy_fields_frame_after
          minor alloc_res.major_alloc_out obj fp 0 wosize rem_hd old
      end;
      assert (MH.read_word_in_major copied rem_hd == Some old);
      if U64.v rem_hd + U64.v mword <= U64.v dst_hd then
        ChunkedPromote.chunked_set_promoted_tag_read_frame
          copied fp tag rem_hd old
      else begin
        assert (U64.v dst_hd + U64.v mword <= U64.v rem_hd);
        ChunkedPromote.chunked_set_promoted_tag_read_frame
          copied fp tag rem_hd old
      end
  in
  rem_header_frame ();
  assert (MH.read_word_in_major res.major_out rem_hd ==
          MH.read_word_in_major alloc_res.major_alloc_out rem_hd);
  SpecMajorAlloc.major_fl_head_wosize_current
    alloc_res.major_alloc_out alloc_res.major_fp_out fuel;
  GenInv.chunked_major_alloc_shape_elim res.major_out res.fp_out fuel;
  SpecMajorAlloc.major_fl_head_wosize_current
    res.major_out res.fp_out fuel;
  assert (SpecMajorAlloc.major_fl_head_wosize
            res.major_out res.fp_out ==
          SpecMajorAlloc.major_fl_head_wosize
            alloc_res.major_alloc_out alloc_res.major_fp_out)
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_cheney_forward_normal_head_split_preserves_chunked_alloc_shape
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
  if not (Seq.mem addr (minor_objects minor)) || cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_normal_noop minor cs addr fuel
  else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then
      ChunkedCheney.chunked_cheney_forward_normal_noop_wz0 minor cs addr fuel
    else begin
      assert (wz > 0);
      assert (cs.ccs_fp <> 0UL);
      assert (SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= wz + 2);
      chunked_promote_object_head_split_preserves_chunked_alloc_shape
        minor cs.ccs_major addr cs.ccs_fp wz fuel;
      let res =
        ChunkedPromote.chunked_promote_object_with_fuel
          minor cs.ccs_major addr cs.ccs_fp wz fuel in
      assert (res.new_addr == cs.ccs_fp);
      assert (res.new_addr <> 0UL);
      ChunkedCheney.chunked_cheney_forward_normal_success
        minor cs addr fuel
    end
  end
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_cheney_forward_one_head_split_preserves_chunked_alloc_shape
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
  if cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_one_noop minor cs addr fuel
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    chunked_cheney_forward_normal_head_split_preserves_chunked_alloc_shape
      minor cs parent fuel;
    let cs' = ChunkedCheney.chunked_cheney_forward_normal minor cs parent fuel in
    assert (GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel);
    assert (SpecMajorAlloc.major_fl_chain_terminates
              cs'.ccs_major cs'.ccs_fp fuel = true);
    if cs'.ccs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (cs'.ccs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_pass
        minor cs addr fuel
    else
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_fail
        minor cs addr fuel
  end else begin
    ChunkedCheney.chunked_cheney_forward_one_normal minor cs addr fuel;
    chunked_cheney_forward_normal_head_split_preserves_chunked_alloc_shape
      minor cs addr fuel
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_cheney_forward_one_budget_ready
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (remaining: nat)
  : GTot prop =
  remaining > 0 /\
  SpecMajorAlloc.major_fl_head_wosize
    cs.ccs_major cs.ccs_fp >= remaining /\
  (Seq.mem addr (minor_objects minor) /\
   cs.ccs_fwd addr = 0UL /\
   ~(is_infix_in_minor minor addr) /\
   minor_wosize minor addr > 0 ==>
     cs.ccs_fp <> 0UL /\
     SpecMajorAlloc.major_fl_head_wosize
       cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 1 + remaining) /\
  (cs.ccs_fwd addr = 0UL /\
   is_infix_in_minor minor addr ==>
     (let parent = infix_parent minor addr in
      Seq.mem parent (minor_objects minor) /\
      cs.ccs_fwd parent = 0UL /\
      minor_wosize minor parent > 0 ==>
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >=
        minor_wosize minor parent + 1 + remaining))

private let chunked_cheney_forward_normal_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (remaining: nat)
  : Lemma
      (requires
        fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        remaining > 0 /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= remaining /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         minor_wosize minor addr > 0 ==>
           cs.ccs_fp <> 0UL /\
           SpecMajorAlloc.major_fl_head_wosize
             cs.ccs_major cs.ccs_fp >=
           minor_wosize minor addr + 1 + remaining))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           cs'.ccs_major cs'.ccs_fp >= remaining))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_normal_noop minor cs addr fuel
  else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then
      ChunkedCheney.chunked_cheney_forward_normal_noop_wz0 minor cs addr fuel
    else begin
      assert (wz > 0);
      assert (cs.ccs_fp <> 0UL);
      assert (SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= wz + 1 + remaining);
      assert (SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= wz + 2);
      chunked_promote_object_head_split_preserves_remaining_head_wosize
        minor cs.ccs_major addr cs.ccs_fp wz fuel remaining;
      let res =
        ChunkedPromote.chunked_promote_object_with_fuel
          minor cs.ccs_major addr cs.ccs_fp wz fuel in
      assert (res.new_addr <> 0UL);
      ChunkedCheney.chunked_cheney_forward_normal_success
        minor cs addr fuel
    end
  end

let chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (remaining: nat)
  : Lemma
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
  =
  assert (remaining > 0);
  assert (SpecMajorAlloc.major_fl_head_wosize
            cs.ccs_major cs.ccs_fp >= remaining);
  if cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_one_noop minor cs addr fuel
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    chunked_cheney_forward_normal_head_split_preserves_remaining_head_wosize
      minor cs parent fuel remaining;
    let cs' =
      ChunkedCheney.chunked_cheney_forward_normal minor cs parent fuel in
    assert (GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel);
    assert (SpecMajorAlloc.major_fl_chain_terminates
              cs'.ccs_major cs'.ccs_fp fuel = true);
    assert (SpecMajorAlloc.major_fl_head_wosize
              cs'.ccs_major cs'.ccs_fp >= remaining);
    if cs'.ccs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (cs'.ccs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_pass
        minor cs addr fuel
    else
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_fail
        minor cs addr fuel
  end else begin
    ChunkedCheney.chunked_cheney_forward_one_normal minor cs addr fuel;
    chunked_cheney_forward_normal_head_split_preserves_remaining_head_wosize
      minor cs addr fuel remaining
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let chunked_cheney_forward_one_split_ready
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t)
  : GTot prop =
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
          cs.ccs_major cs.ccs_fp >= minor_wosize minor parent + 2))

let rec chunked_cheney_forward_roots_split_ready
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (idx: nat) (alloc_fuel: nat)
  : GTot prop
  (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then True
  else
    let r = Seq.index roots idx in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one minor cs r alloc_fuel in
    chunked_cheney_forward_one_split_ready minor cs r /\
    chunked_cheney_forward_roots_split_ready
      minor cs' roots (idx + 1) alloc_fuel

let rec chunked_cheney_forward_roots_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (idx: nat) (alloc_fuel: nat)
  : Lemma
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
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    ChunkedCheney.chunked_cheney_forward_roots_base
      minor cs roots idx alloc_fuel
  else begin
    ChunkedCheney.chunked_cheney_forward_roots_step
      minor cs roots idx alloc_fuel;
    let r = Seq.index roots idx in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one minor cs r alloc_fuel in
    assert (chunked_cheney_forward_one_split_ready minor cs r);
    assert (chunked_cheney_forward_roots_split_ready
              minor cs' roots (idx + 1) alloc_fuel);
    chunked_cheney_forward_one_head_split_preserves_chunked_alloc_shape
      minor cs r alloc_fuel;
    chunked_cheney_forward_roots_head_split_preserves_chunked_alloc_shape
      minor cs' roots (idx + 1) alloc_fuel
  end

let rec chunked_cheney_forward_roots_budget_ready
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (idx: nat) (alloc_fuel: nat) (remaining: nat)
  : GTot prop
  (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    remaining > 0 /\
    SpecMajorAlloc.major_fl_head_wosize
      cs.ccs_major cs.ccs_fp >= remaining
  else
    let r = Seq.index roots idx in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one minor cs r alloc_fuel in
    chunked_cheney_forward_one_budget_ready minor cs r remaining /\
    chunked_cheney_forward_roots_budget_ready
      minor cs' roots (idx + 1) alloc_fuel remaining

let rec chunked_cheney_forward_roots_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (idx: nat) (alloc_fuel: nat) (remaining: nat)
  : Lemma
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
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    ChunkedCheney.chunked_cheney_forward_roots_base
      minor cs roots idx alloc_fuel
  else begin
    ChunkedCheney.chunked_cheney_forward_roots_step
      minor cs roots idx alloc_fuel;
    let r = Seq.index roots idx in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one minor cs r alloc_fuel in
    assert (chunked_cheney_forward_one_budget_ready minor cs r remaining);
    assert (chunked_cheney_forward_roots_budget_ready
              minor cs' roots (idx + 1) alloc_fuel remaining);
    chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
      minor cs r alloc_fuel remaining;
    chunked_cheney_forward_roots_head_split_preserves_remaining_head_wosize
      minor cs' roots (idx + 1) alloc_fuel remaining
  end

let rec chunked_cheney_forward_fields_split_ready
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (alloc_fuel: nat)
  : GTot prop
  (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then True
  else
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs field_val alloc_fuel in
    chunked_cheney_forward_one_split_ready minor cs field_val /\
    chunked_cheney_forward_fields_split_ready
      minor cs' parent (idx + 1) wosize alloc_fuel

let rec chunked_cheney_forward_fields_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (alloc_fuel: nat)
  : Lemma
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
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    ChunkedCheney.chunked_cheney_forward_fields_base
      minor cs parent idx wosize alloc_fuel
  else begin
    ChunkedCheney.chunked_cheney_forward_fields_step
      minor cs parent idx wosize alloc_fuel;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs field_val alloc_fuel in
    assert (chunked_cheney_forward_one_split_ready minor cs field_val);
    assert (chunked_cheney_forward_fields_split_ready
              minor cs' parent (idx + 1) wosize alloc_fuel);
    chunked_cheney_forward_one_head_split_preserves_chunked_alloc_shape
      minor cs field_val alloc_fuel;
    chunked_cheney_forward_fields_head_split_preserves_chunked_alloc_shape
      minor cs' parent (idx + 1) wosize alloc_fuel
  end

let rec chunked_cheney_forward_fields_budget_ready
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (alloc_fuel: nat)
  (remaining: nat)
  : GTot prop
  (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    remaining > 0 /\
    SpecMajorAlloc.major_fl_head_wosize
      cs.ccs_major cs.ccs_fp >= remaining
  else
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs field_val alloc_fuel in
    chunked_cheney_forward_one_budget_ready
      minor cs field_val remaining /\
    chunked_cheney_forward_fields_budget_ready
      minor cs' parent (idx + 1) wosize alloc_fuel remaining

let rec chunked_cheney_forward_fields_head_split_preserves_remaining_head_wosize
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
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    ChunkedCheney.chunked_cheney_forward_fields_base
      minor cs parent idx wosize alloc_fuel
  else begin
    ChunkedCheney.chunked_cheney_forward_fields_step
      minor cs parent idx wosize alloc_fuel;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs field_val alloc_fuel in
    assert (chunked_cheney_forward_one_budget_ready
              minor cs field_val remaining);
    assert (chunked_cheney_forward_fields_budget_ready
              minor cs' parent (idx + 1) wosize alloc_fuel remaining);
    chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
      minor cs field_val alloc_fuel remaining;
    chunked_cheney_forward_fields_head_split_preserves_remaining_head_wosize
      minor cs' parent (idx + 1) wosize alloc_fuel remaining
  end

let rec chunked_cheney_scan_split_ready
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat) (scan_fuel: nat) (alloc_fuel: nat)
  : GTot prop
  (decreases scan_fuel)
  =
  if scan_fuel > 0 then
    if scan >= Seq.length cs.ccs_queue then True
    else
      let fuel' : f:nat{f < scan_fuel} = scan_fuel - 1 in
      let obj = Seq.index cs.ccs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs obj 0 wz alloc_fuel in
      chunked_cheney_forward_fields_split_ready
        minor cs obj 0 wz alloc_fuel /\
      chunked_cheney_scan_split_ready
        minor cs' (scan + 1) fuel' alloc_fuel
  else True

let rec chunked_cheney_scan_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat) (scan_fuel: nat) (alloc_fuel: nat)
  : Lemma
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
      (decreases scan_fuel)
  =
  if scan_fuel > 0 then
    if scan >= Seq.length cs.ccs_queue then
      ChunkedCheney.chunked_cheney_scan_base
        minor cs scan scan_fuel alloc_fuel
    else begin
      assert (scan < Seq.length cs.ccs_queue);
      let fuel' : f:nat{f < scan_fuel} = scan_fuel - 1 in
      ChunkedCheney.chunked_cheney_scan_step
        minor cs scan scan_fuel alloc_fuel;
      let obj = Seq.index cs.ccs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs obj 0 wz alloc_fuel in
      assert (chunked_cheney_forward_fields_split_ready
                minor cs obj 0 wz alloc_fuel);
      assert (chunked_cheney_scan_split_ready
                minor cs' (scan + 1) fuel' alloc_fuel);
      chunked_cheney_forward_fields_head_split_preserves_chunked_alloc_shape
        minor cs obj 0 wz alloc_fuel;
      chunked_cheney_scan_head_split_preserves_chunked_alloc_shape
        minor cs' (scan + 1) fuel' alloc_fuel
    end
  else begin
    assert (scan_fuel = 0);
    ChunkedCheney.chunked_cheney_scan_base
      minor cs scan scan_fuel alloc_fuel
  end

let rec chunked_cheney_scan_budget_ready
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat) (scan_fuel: nat) (alloc_fuel: nat) (remaining: nat)
  : GTot prop
  (decreases scan_fuel)
  =
  if scan_fuel > 0 then
    if scan >= Seq.length cs.ccs_queue then
      remaining > 0 /\
      SpecMajorAlloc.major_fl_head_wosize
        cs.ccs_major cs.ccs_fp >= remaining
    else
      let fuel' : f:nat{f < scan_fuel} = scan_fuel - 1 in
      let obj = Seq.index cs.ccs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs obj 0 wz alloc_fuel in
      chunked_cheney_forward_fields_budget_ready
        minor cs obj 0 wz alloc_fuel remaining /\
      chunked_cheney_scan_budget_ready
        minor cs' (scan + 1) fuel' alloc_fuel remaining
  else
    remaining > 0 /\
    SpecMajorAlloc.major_fl_head_wosize
      cs.ccs_major cs.ccs_fp >= remaining

let rec chunked_cheney_scan_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat) (scan_fuel: nat) (alloc_fuel: nat) (remaining: nat)
  : Lemma
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
      (decreases scan_fuel)
  =
  if scan_fuel > 0 then
    if scan >= Seq.length cs.ccs_queue then
      ChunkedCheney.chunked_cheney_scan_base
        minor cs scan scan_fuel alloc_fuel
    else begin
      assert (scan < Seq.length cs.ccs_queue);
      let fuel' : f:nat{f < scan_fuel} = scan_fuel - 1 in
      ChunkedCheney.chunked_cheney_scan_step
        minor cs scan scan_fuel alloc_fuel;
      let obj = Seq.index cs.ccs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs obj 0 wz alloc_fuel in
      assert (chunked_cheney_forward_fields_budget_ready
                minor cs obj 0 wz alloc_fuel remaining);
      assert (chunked_cheney_scan_budget_ready
                minor cs' (scan + 1) fuel' alloc_fuel remaining);
      chunked_cheney_forward_fields_head_split_preserves_remaining_head_wosize
        minor cs obj 0 wz alloc_fuel remaining;
      chunked_cheney_scan_head_split_preserves_remaining_head_wosize
        minor cs' (scan + 1) fuel' alloc_fuel remaining
    end
  else begin
    assert (scan_fuel = 0);
    ChunkedCheney.chunked_cheney_scan_base
      minor cs scan scan_fuel alloc_fuel
  end

let chunked_cheney_promote_split_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
  : GTot prop =
  let cs0 : ChunkedCheney.chunked_cheney_state =
    { ccs_major = major; ccs_fp = fp;
      ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
  let cs1 =
    ChunkedCheney.chunked_cheney_forward_roots
      minor cs0 roots 0 alloc_fuel in
  chunked_cheney_forward_roots_split_ready
    minor cs0 roots 0 alloc_fuel /\
  chunked_cheney_scan_split_ready
    minor cs1 0 (cheney_fuel minor) alloc_fuel

let chunked_cheney_promote_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
  : Lemma
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
  =
  let cs0 : ChunkedCheney.chunked_cheney_state =
    { ccs_major = major; ccs_fp = fp;
      ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
  assert (GenInv.chunked_major_alloc_shape
            cs0.ccs_major cs0.ccs_fp alloc_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            cs0.ccs_major cs0.ccs_fp alloc_fuel = true);
  assert (chunked_cheney_forward_roots_split_ready
            minor cs0 roots 0 alloc_fuel);
  chunked_cheney_forward_roots_head_split_preserves_chunked_alloc_shape
    minor cs0 roots 0 alloc_fuel;
  let cs1 =
    ChunkedCheney.chunked_cheney_forward_roots
      minor cs0 roots 0 alloc_fuel in
  assert (GenInv.chunked_major_alloc_shape
            cs1.ccs_major cs1.ccs_fp alloc_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            cs1.ccs_major cs1.ccs_fp alloc_fuel = true);
  assert (chunked_cheney_scan_split_ready
            minor cs1 0 (cheney_fuel minor) alloc_fuel);
  chunked_cheney_scan_head_split_preserves_chunked_alloc_shape
    minor cs1 0 (cheney_fuel minor) alloc_fuel;
  let cs2 =
    ChunkedCheney.chunked_cheney_scan
      minor cs1 0 (cheney_fuel minor) alloc_fuel in
  let res =
    ChunkedCheney.chunked_cheney_promote
      minor major fp roots alloc_fuel in
  ChunkedCheney.chunked_cheney_promote_equation
    minor major fp roots alloc_fuel;
  assert (res.major_final == cs2.ccs_major);
  assert (res.fp_final == cs2.ccs_fp)

let chunked_cheney_promote_budget_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (remaining: nat)
  : GTot prop =
  let cs0 : ChunkedCheney.chunked_cheney_state =
    { ccs_major = major; ccs_fp = fp;
      ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
  let cs1 =
    ChunkedCheney.chunked_cheney_forward_roots
      minor cs0 roots 0 alloc_fuel in
  chunked_cheney_forward_roots_budget_ready
    minor cs0 roots 0 alloc_fuel remaining /\
  chunked_cheney_scan_budget_ready
    minor cs1 0 (cheney_fuel minor) alloc_fuel remaining

let chunked_cheney_promote_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (remaining: nat)
  : Lemma
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
  =
  let cs0 : ChunkedCheney.chunked_cheney_state =
    { ccs_major = major; ccs_fp = fp;
      ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
  assert (GenInv.chunked_major_alloc_shape
            cs0.ccs_major cs0.ccs_fp alloc_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            cs0.ccs_major cs0.ccs_fp alloc_fuel = true);
  assert (chunked_cheney_forward_roots_budget_ready
            minor cs0 roots 0 alloc_fuel remaining);
  chunked_cheney_forward_roots_head_split_preserves_remaining_head_wosize
    minor cs0 roots 0 alloc_fuel remaining;
  let cs1 =
    ChunkedCheney.chunked_cheney_forward_roots
      minor cs0 roots 0 alloc_fuel in
  assert (GenInv.chunked_major_alloc_shape
            cs1.ccs_major cs1.ccs_fp alloc_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            cs1.ccs_major cs1.ccs_fp alloc_fuel = true);
  assert (SpecMajorAlloc.major_fl_head_wosize
            cs1.ccs_major cs1.ccs_fp >= remaining);
  assert (chunked_cheney_scan_budget_ready
            minor cs1 0 (cheney_fuel minor) alloc_fuel remaining);
  chunked_cheney_scan_head_split_preserves_remaining_head_wosize
    minor cs1 0 (cheney_fuel minor) alloc_fuel remaining;
  let cs2 =
    ChunkedCheney.chunked_cheney_scan
      minor cs1 0 (cheney_fuel minor) alloc_fuel in
  let res =
    ChunkedCheney.chunked_cheney_promote
      minor major fp roots alloc_fuel in
  ChunkedCheney.chunked_cheney_promote_equation
    minor major fp roots alloc_fuel;
  assert (res.major_final == cs2.ccs_major);
  assert (res.fp_final == cs2.ccs_fp)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
private let chunked_cheney_forward_normal_fwd_monotone
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr x: U64.t) (alloc_fuel: nat)
  : Lemma
      (requires cs.ccs_fwd x <> 0UL)
      (ensures
        (ChunkedCheney.chunked_cheney_forward_normal
          minor cs addr alloc_fuel).ccs_fwd x <> 0UL)
  =
  if x = addr then begin
    assert (cs.ccs_fwd addr <> 0UL);
    ChunkedCheney.chunked_cheney_forward_normal_noop
      minor cs addr alloc_fuel
  end else begin
    ChunkedCheney.chunked_cheney_forward_normal_other_fwd
      minor cs addr x alloc_fuel;
    assert ((ChunkedCheney.chunked_cheney_forward_normal
      minor cs addr alloc_fuel).ccs_fwd x == cs.ccs_fwd x)
  end

let chunked_cheney_forward_one_fwd_monotone
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr x: U64.t) (alloc_fuel: nat)
  : Lemma
      (requires cs.ccs_fwd x <> 0UL)
      (ensures
        (ChunkedCheney.chunked_cheney_forward_one
          minor cs addr alloc_fuel).ccs_fwd x <> 0UL)
  =
  if cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_one_noop
      minor cs addr alloc_fuel
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    chunked_cheney_forward_normal_fwd_monotone
      minor cs parent x alloc_fuel;
    let csn =
      ChunkedCheney.chunked_cheney_forward_normal
        minor cs parent alloc_fuel in
    assert (csn.ccs_fwd x <> 0UL);
    if csn.ccs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (csn.ccs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then begin
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_pass
        minor cs addr alloc_fuel;
      if x = addr then begin
        assert (False)
      end else begin
        let delta = U64.v addr - U64.v parent in
        let sum =
          U64.uint_to_t (U64.v (csn.ccs_fwd parent) + delta) in
        assert ((extend_forwarding csn.ccs_fwd addr sum) x ==
                csn.ccs_fwd x)
      end
    end else
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_fail
        minor cs addr alloc_fuel
  end else begin
    ChunkedCheney.chunked_cheney_forward_one_normal
      minor cs addr alloc_fuel;
    chunked_cheney_forward_normal_fwd_monotone
      minor cs addr x alloc_fuel
  end

let rec chunked_cheney_forward_fields_fwd_monotone
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx wosize alloc_fuel: nat) (x: U64.t)
  : Lemma
      (requires cs.ccs_fwd x <> 0UL)
      (ensures
        (ChunkedCheney.chunked_cheney_forward_fields
          minor cs parent idx wosize alloc_fuel).ccs_fwd x <> 0UL)
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    ChunkedCheney.chunked_cheney_forward_fields_base
      minor cs parent idx wosize alloc_fuel
  else begin
    ChunkedCheney.chunked_cheney_forward_fields_step
      minor cs parent idx wosize alloc_fuel;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs field_val alloc_fuel in
    chunked_cheney_forward_one_fwd_monotone
      minor cs field_val x alloc_fuel;
    chunked_cheney_forward_fields_fwd_monotone
      minor cs' parent (idx + 1) wosize alloc_fuel x
  end

let rec chunked_cheney_forward_roots_fwd_monotone
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (idx: nat) (alloc_fuel: nat) (x: U64.t)
  : Lemma
      (requires cs.ccs_fwd x <> 0UL)
      (ensures
        (ChunkedCheney.chunked_cheney_forward_roots
          minor cs roots idx alloc_fuel).ccs_fwd x <> 0UL)
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    ChunkedCheney.chunked_cheney_forward_roots_base
      minor cs roots idx alloc_fuel
  else begin
    ChunkedCheney.chunked_cheney_forward_roots_step
      minor cs roots idx alloc_fuel;
    let r = Seq.index roots idx in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs r alloc_fuel in
    chunked_cheney_forward_one_fwd_monotone
      minor cs r x alloc_fuel;
    chunked_cheney_forward_roots_fwd_monotone
      minor cs' roots (idx + 1) alloc_fuel x
  end

let rec chunked_cheney_scan_fwd_monotone
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat) (x: U64.t)
  : Lemma
      (requires cs.ccs_fwd x <> 0UL)
      (ensures
        (ChunkedCheney.chunked_cheney_scan
          minor cs scan scan_fuel alloc_fuel).ccs_fwd x <> 0UL)
      (decreases scan_fuel)
  =
  if scan_fuel = 0 || scan >= Seq.length cs.ccs_queue then
    ChunkedCheney.chunked_cheney_scan_base
      minor cs scan scan_fuel alloc_fuel
  else begin
    assert (scan_fuel > 0);
    let fuel' : f:nat{f < scan_fuel} = scan_fuel - 1 in
    ChunkedCheney.chunked_cheney_scan_step
      minor cs scan scan_fuel alloc_fuel;
    let obj = Seq.index cs.ccs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_fields
        minor cs obj 0 wz alloc_fuel in
    chunked_cheney_forward_fields_fwd_monotone
      minor cs obj 0 wz alloc_fuel x;
    chunked_cheney_scan_fwd_monotone
      minor cs' (scan + 1) fuel' alloc_fuel x
  end

let chunked_cheney_forward_one_covers_addr_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (alloc_fuel remaining: nat)
  : Lemma
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
  =
  if Seq.mem addr (minor_objects minor) && minor_wosize minor addr > 0 then begin
    if cs.ccs_fwd addr <> 0UL then
      ChunkedCheney.chunked_cheney_forward_one_noop
        minor cs addr alloc_fuel
    else begin
      minor_objects_not_infix minor addr;
      assert (~(is_infix_in_minor minor addr));
      ChunkedCheney.chunked_cheney_forward_one_normal
        minor cs addr alloc_fuel;
      let wz = minor_wosize minor addr in
      assert (remaining > 0);
      assert (cs.ccs_fp <> 0UL);
      assert (SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= wz + 1 + remaining);
      chunked_promote_object_head_split_preserves_remaining_head_wosize
        minor cs.ccs_major addr cs.ccs_fp wz alloc_fuel remaining;
      let res =
        ChunkedPromote.chunked_promote_object_with_fuel
          minor cs.ccs_major addr cs.ccs_fp wz alloc_fuel in
      assert (res.new_addr == cs.ccs_fp);
      assert (res.new_addr <> 0UL);
      ChunkedCheney.chunked_cheney_forward_normal_success
        minor cs addr alloc_fuel;
      assert ((extend_forwarding cs.ccs_fwd addr res.new_addr) addr ==
              res.new_addr)
    end
  end

private let rec chunked_cheney_forward_roots_covers_index_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (idx alloc_fuel remaining: nat)
  (j:nat{idx <= j /\ j < Seq.length roots})
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        chunked_cheney_forward_roots_budget_ready
          minor cs roots idx alloc_fuel remaining)
      (ensures
        Seq.mem (Seq.index roots j) (minor_objects minor) /\
        minor_wosize minor (Seq.index roots j) > 0 ==>
        (ChunkedCheney.chunked_cheney_forward_roots
          minor cs roots idx alloc_fuel).ccs_fwd
          (Seq.index roots j) <> 0UL)
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    assert (False)
  else begin
    ChunkedCheney.chunked_cheney_forward_roots_step
      minor cs roots idx alloc_fuel;
    let r = Seq.index roots idx in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs r alloc_fuel in
    assert (chunked_cheney_forward_one_budget_ready
              minor cs r remaining);
    assert (chunked_cheney_forward_roots_budget_ready
              minor cs' roots (idx + 1) alloc_fuel remaining);
    if j = idx then begin
      assert (Seq.index roots j == r);
      chunked_cheney_forward_one_covers_addr_from_budget
        minor cs r alloc_fuel remaining;
      if Seq.mem r (minor_objects minor) && minor_wosize minor r > 0 then begin
        assert (cs'.ccs_fwd r <> 0UL);
        chunked_cheney_forward_roots_fwd_monotone
          minor cs' roots (idx + 1) alloc_fuel r
      end
    end else begin
      assert (j <> idx);
      assert (idx < j);
      assert (idx + 1 <= j);
      chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
        minor cs r alloc_fuel remaining;
      chunked_cheney_forward_roots_covers_index_from_budget
        minor cs' roots (idx + 1) alloc_fuel remaining j
    end
  end

let chunked_cheney_forward_roots_covers_roots_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  : Lemma
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
  =
  let cs' =
    ChunkedCheney.chunked_cheney_forward_roots
      minor cs roots 0 alloc_fuel in
  let aux (r: U64.t)
    : Lemma
        (requires Seq.mem r roots /\
                  Seq.mem r (minor_objects minor) /\
                  minor_wosize minor r > 0)
        (ensures cs'.ccs_fwd r <> 0UL)
    =
    let j = Seq.index_mem r roots in
    assert (j < Seq.length roots);
    assert (Seq.index roots j == r);
    assert (0 <= j);
    chunked_cheney_forward_roots_covers_index_from_budget
      minor cs roots 0 alloc_fuel remaining j
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

private let rec chunked_cheney_forward_fields_covers_index_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx wosize alloc_fuel remaining: nat)
  (j:nat{idx <= j /\ j < wosize})
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        chunked_cheney_forward_fields_budget_ready
          minor cs parent idx wosize alloc_fuel remaining)
      (ensures
        (let child = to_minor_offset (minor_read_field minor parent j) in
         Seq.mem child (minor_objects minor) /\
         minor_wosize minor child > 0 ==>
         (ChunkedCheney.chunked_cheney_forward_fields
           minor cs parent idx wosize alloc_fuel).ccs_fwd child <> 0UL))
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    assert (False)
  else begin
    ChunkedCheney.chunked_cheney_forward_fields_step
      minor cs parent idx wosize alloc_fuel;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs field_val alloc_fuel in
    assert (chunked_cheney_forward_one_budget_ready
              minor cs field_val remaining);
    assert (chunked_cheney_forward_fields_budget_ready
              minor cs' parent (idx + 1) wosize alloc_fuel remaining);
    if j = idx then begin
      assert (to_minor_offset (minor_read_field minor parent j) == field_val);
      chunked_cheney_forward_one_covers_addr_from_budget
        minor cs field_val alloc_fuel remaining;
      if Seq.mem field_val (minor_objects minor) &&
         minor_wosize minor field_val > 0
      then begin
        assert (cs'.ccs_fwd field_val <> 0UL);
        chunked_cheney_forward_fields_fwd_monotone
          minor cs' parent (idx + 1) wosize alloc_fuel field_val
      end
    end else begin
      assert (j <> idx);
      assert (idx < j);
      assert (idx + 1 <= j);
      chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
        minor cs field_val alloc_fuel remaining;
      chunked_cheney_forward_fields_covers_index_from_budget
        minor cs' parent (idx + 1) wosize alloc_fuel remaining j
    end
  end

let chunked_cheney_forward_fields_covers_successors_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (alloc_fuel remaining: nat)
  : Lemma
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
  =
  let wosize = minor_wosize minor parent in
  let cs' =
    ChunkedCheney.chunked_cheney_forward_fields
      minor cs parent 0 wosize alloc_fuel in
  let aux (y: U64.t)
    : Lemma
        (requires Seq.mem y (minor_successors minor parent) /\
                  minor_wosize minor y > 0)
        (ensures cs'.ccs_fwd y <> 0UL)
    =
    minor_successors_char minor parent y;
    let j = IndDesc.indefinite_description_ghost nat
      (fun j -> j < wosize /\
                to_minor_offset (minor_read_field minor parent j) == y /\
                is_minor_addr y /\
                Seq.mem y (minor_objects minor)) in
    assert (j < wosize);
    assert (0 <= j);
    assert (to_minor_offset (minor_read_field minor parent j) == y);
    chunked_cheney_forward_fields_covers_index_from_budget
      minor cs parent 0 wosize alloc_fuel remaining j
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

private let chunked_cheney_forward_normal_queue_prefix
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (k alloc_fuel: nat)
  : Lemma
      (requires k < Seq.length cs.ccs_queue)
      (ensures
        k < Seq.length
          (ChunkedCheney.chunked_cheney_forward_normal
            minor cs addr alloc_fuel).ccs_queue /\
        Seq.index
          (ChunkedCheney.chunked_cheney_forward_normal
            minor cs addr alloc_fuel).ccs_queue k ==
        Seq.index cs.ccs_queue k)
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_normal_noop
      minor cs addr alloc_fuel
  else if minor_wosize minor addr = 0 then
    ChunkedCheney.chunked_cheney_forward_normal_noop_wz0
      minor cs addr alloc_fuel
  else begin
    assert (Seq.mem addr (minor_objects minor));
    assert (cs.ccs_fwd addr = 0UL);
    let wz = minor_wosize minor addr in
    assert (wz > 0);
    let res =
      ChunkedPromote.chunked_promote_object_with_fuel
        minor cs.ccs_major addr cs.ccs_fp wz alloc_fuel in
    if res.new_addr = 0UL then
      ChunkedCheney.chunked_cheney_forward_normal_noop_oom
        minor cs addr alloc_fuel
    else begin
      ChunkedCheney.chunked_cheney_forward_normal_success
        minor cs addr alloc_fuel;
      Seq.Base.lemma_index_app1 cs.ccs_queue (Seq.create 1 addr) k
    end
  end

private let chunked_cheney_forward_one_queue_prefix
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (k alloc_fuel: nat)
  : Lemma
      (requires k < Seq.length cs.ccs_queue)
      (ensures
        k < Seq.length
          (ChunkedCheney.chunked_cheney_forward_one
            minor cs addr alloc_fuel).ccs_queue /\
        Seq.index
          (ChunkedCheney.chunked_cheney_forward_one
            minor cs addr alloc_fuel).ccs_queue k ==
        Seq.index cs.ccs_queue k)
  =
  if cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_one_noop
      minor cs addr alloc_fuel
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    chunked_cheney_forward_normal_queue_prefix
      minor cs parent k alloc_fuel;
    let csn =
      ChunkedCheney.chunked_cheney_forward_normal
        minor cs parent alloc_fuel in
    if csn.ccs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (csn.ccs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_pass
        minor cs addr alloc_fuel
    else
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_fail
        minor cs addr alloc_fuel
  end else begin
    ChunkedCheney.chunked_cheney_forward_one_normal
      minor cs addr alloc_fuel;
    chunked_cheney_forward_normal_queue_prefix
      minor cs addr k alloc_fuel
  end

private let rec chunked_cheney_forward_fields_queue_prefix
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx wosize: nat) (k alloc_fuel: nat)
  : Lemma
      (requires k < Seq.length cs.ccs_queue)
      (ensures
        k < Seq.length
          (ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent idx wosize alloc_fuel).ccs_queue /\
        Seq.index
          (ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent idx wosize alloc_fuel).ccs_queue k ==
        Seq.index cs.ccs_queue k)
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    ChunkedCheney.chunked_cheney_forward_fields_base
      minor cs parent idx wosize alloc_fuel
  else begin
    ChunkedCheney.chunked_cheney_forward_fields_step
      minor cs parent idx wosize alloc_fuel;
    let child = to_minor_offset (minor_read_field minor parent idx) in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs child alloc_fuel in
    chunked_cheney_forward_one_queue_prefix
      minor cs child k alloc_fuel;
    assert (k < Seq.length cs'.ccs_queue);
    chunked_cheney_forward_fields_queue_prefix
      minor cs' parent (idx + 1) wosize k alloc_fuel
  end

[@"opaque_to_smt"]
let chunked_scanned_prefix_closed
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat) : prop =
  forall (k:nat) (y:U64.t).
    k < scan /\ k < Seq.length cs.ccs_queue /\
    Seq.mem y (minor_successors minor (Seq.index cs.ccs_queue k)) /\
    minor_wosize minor y > 0 ==> cs.ccs_fwd y <> 0UL

let chunked_scanned_prefix_empty
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  : Lemma
      (ensures chunked_scanned_prefix_closed minor cs 0)
  =
  reveal_opaque (`%chunked_scanned_prefix_closed)
    (chunked_scanned_prefix_closed minor cs 0)

let chunked_scanned_prefix_step_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan alloc_fuel remaining: nat)
  : Lemma
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
  =
  let parent = Seq.index cs.ccs_queue scan in
  let wz = minor_wosize minor parent in
  let cs' =
    ChunkedCheney.chunked_cheney_forward_fields
      minor cs parent 0 wz alloc_fuel in
  reveal_opaque (`%chunked_scanned_prefix_closed)
    (chunked_scanned_prefix_closed minor cs scan);
  reveal_opaque (`%chunked_scanned_prefix_closed)
    (chunked_scanned_prefix_closed minor cs' (scan + 1));
  let aux (k:nat) (y:U64.t)
    : Lemma
        (requires
          k < scan + 1 /\ k < Seq.length cs'.ccs_queue /\
          Seq.mem y (minor_successors minor (Seq.index cs'.ccs_queue k)) /\
          minor_wosize minor y > 0)
        (ensures cs'.ccs_fwd y <> 0UL)
    =
    if k = scan then begin
      chunked_cheney_forward_fields_queue_prefix
        minor cs parent 0 wz scan alloc_fuel;
      assert (Seq.index cs'.ccs_queue k == parent);
      chunked_cheney_forward_fields_covers_successors_from_budget
        minor cs parent alloc_fuel remaining
    end else begin
      if k < scan then () else begin
        assert (k >= scan);
        assert (k <= scan);
        assert (k == scan);
        assert (False)
      end;
      assert (k < Seq.length cs.ccs_queue);
      chunked_cheney_forward_fields_queue_prefix
        minor cs parent 0 wz k alloc_fuel;
      assert (Seq.index cs'.ccs_queue k == Seq.index cs.ccs_queue k);
      assert (cs.ccs_fwd y <> 0UL);
      chunked_cheney_forward_fields_fwd_monotone
        minor cs parent 0 wz alloc_fuel y
    end
  in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux)

let rec chunked_cheney_scan_end_index
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat)
  : GTot nat
  (decreases scan_fuel)
  =
  if scan_fuel > 0 then
    if scan >= Seq.length cs.ccs_queue then scan
    else
      let fuel' : f:nat{f < scan_fuel} = scan_fuel - 1 in
      let obj = Seq.index cs.ccs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs obj 0 wz alloc_fuel in
      chunked_cheney_scan_end_index
        minor cs' (scan + 1) fuel' alloc_fuel
  else scan

let rec chunked_cheney_scan_end_exhausted_or_fuel
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat)
  : Lemma
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
         let end_idx =
           chunked_cheney_scan_end_index
             minor cs scan scan_fuel alloc_fuel in
         end_idx >= Seq.length cs'.ccs_queue \/
         end_idx == scan + scan_fuel))
      (decreases scan_fuel)
  =
  if scan_fuel > 0 then
    if scan >= Seq.length cs.ccs_queue then begin
      ChunkedCheney.chunked_cheney_scan_base
        minor cs scan scan_fuel alloc_fuel;
      assert (chunked_cheney_scan_end_index
                minor cs scan scan_fuel alloc_fuel == scan);
      assert (scan >= Seq.length cs.ccs_queue)
    end else begin
      assert (scan < Seq.length cs.ccs_queue);
      let fuel' : f:nat{f < scan_fuel} = scan_fuel - 1 in
      ChunkedCheney.chunked_cheney_scan_step
        minor cs scan scan_fuel alloc_fuel;
      let obj = Seq.index cs.ccs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs obj 0 wz alloc_fuel in
      let final =
        ChunkedCheney.chunked_cheney_scan
          minor cs' (scan + 1) fuel' alloc_fuel in
      let end_idx =
        chunked_cheney_scan_end_index
          minor cs' (scan + 1) fuel' alloc_fuel in
      chunked_cheney_scan_end_exhausted_or_fuel
        minor cs' (scan + 1) fuel' alloc_fuel;
      assert (ChunkedCheney.chunked_cheney_scan
                minor cs scan scan_fuel alloc_fuel == final);
      assert (chunked_cheney_scan_end_index
                minor cs scan scan_fuel alloc_fuel == end_idx);
      assert (end_idx >= Seq.length final.ccs_queue \/
              end_idx == (scan + 1) + fuel');
      assert (fuel' == scan_fuel - 1);
      assert (scan_fuel == fuel' + 1);
      assert ((scan + 1) + fuel' == scan + (fuel' + 1));
      assert ((scan + 1) + fuel' == scan + scan_fuel)
    end
  else begin
    assert (scan_fuel = 0);
    ChunkedCheney.chunked_cheney_scan_base
      minor cs scan scan_fuel alloc_fuel;
    assert (chunked_cheney_scan_end_index
              minor cs scan scan_fuel alloc_fuel == scan);
    assert (scan == scan + scan_fuel)
  end

let rec chunked_cheney_scan_scanned_prefix_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel remaining: nat)
  : Lemma
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
      (decreases scan_fuel)
  =
  if scan_fuel > 0 then
    if scan >= Seq.length cs.ccs_queue then
      ChunkedCheney.chunked_cheney_scan_base
        minor cs scan scan_fuel alloc_fuel
    else begin
      assert (scan < Seq.length cs.ccs_queue);
      let fuel' : f:nat{f < scan_fuel} = scan_fuel - 1 in
      ChunkedCheney.chunked_cheney_scan_step
        minor cs scan scan_fuel alloc_fuel;
      let obj = Seq.index cs.ccs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs obj 0 wz alloc_fuel in
      assert (chunked_cheney_forward_fields_budget_ready
                minor cs obj 0 wz alloc_fuel remaining);
      assert (chunked_cheney_scan_budget_ready
                minor cs' (scan + 1) fuel' alloc_fuel remaining);
      chunked_scanned_prefix_step_from_budget
        minor cs scan alloc_fuel remaining;
      assert (chunked_scanned_prefix_closed minor cs' (scan + 1));
      chunked_cheney_forward_fields_head_split_preserves_remaining_head_wosize
        minor cs obj 0 wz alloc_fuel remaining;
      assert (GenInv.chunked_major_alloc_shape
                cs'.ccs_major cs'.ccs_fp alloc_fuel);
      assert (SpecMajorAlloc.major_fl_chain_terminates
                cs'.ccs_major cs'.ccs_fp alloc_fuel = true);
      chunked_cheney_scan_scanned_prefix_from_budget
        minor cs' (scan + 1) fuel' alloc_fuel remaining
    end
  else begin
    assert (scan_fuel = 0);
    ChunkedCheney.chunked_cheney_scan_base
      minor cs scan scan_fuel alloc_fuel
  end

[@"opaque_to_smt"]
let chunked_fwd_in_queue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  : prop =
  forall (x: U64.t).
    Seq.mem x (minor_objects minor) /\
    cs.ccs_fwd x <> 0UL ==> Seq.mem x cs.ccs_queue

let chunked_fwd_in_queue_elim
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (x: U64.t)
  : Lemma
      (requires
        chunked_fwd_in_queue minor cs /\
        Seq.mem x (minor_objects minor) /\
        cs.ccs_fwd x <> 0UL)
      (ensures Seq.mem x cs.ccs_queue)
  =
  reveal_opaque (`%chunked_fwd_in_queue)
    (chunked_fwd_in_queue minor cs)

let chunked_fwd_in_queue_initial
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  : Lemma
      (requires cs.ccs_queue == Seq.empty /\
                cs.ccs_fwd == empty_forwarding)
      (ensures chunked_fwd_in_queue minor cs)
  =
  reveal_opaque (`%chunked_fwd_in_queue)
    (chunked_fwd_in_queue minor cs);
  let aux (x: U64.t)
    : Lemma
        (requires Seq.mem x (minor_objects minor) /\
                  cs.ccs_fwd x <> 0UL)
        (ensures Seq.mem x cs.ccs_queue)
    =
    assert (cs.ccs_fwd x == 0UL);
    assert False
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

private let chunked_cheney_forward_normal_preserves_fwd_in_queue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (alloc_fuel: nat)
  : Lemma
      (requires chunked_fwd_in_queue minor cs)
      (ensures
        chunked_fwd_in_queue minor
          (ChunkedCheney.chunked_cheney_forward_normal
            minor cs addr alloc_fuel))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_normal_noop
      minor cs addr alloc_fuel
  else if minor_wosize minor addr = 0 then
    ChunkedCheney.chunked_cheney_forward_normal_noop_wz0
      minor cs addr alloc_fuel
  else begin
    assert (Seq.mem addr (minor_objects minor));
    assert (cs.ccs_fwd addr = 0UL);
    let wz = minor_wosize minor addr in
    assert (wz > 0);
    let res =
      ChunkedPromote.chunked_promote_object_with_fuel
        minor cs.ccs_major addr cs.ccs_fp wz alloc_fuel in
    if res.new_addr = 0UL then
      ChunkedCheney.chunked_cheney_forward_normal_noop_oom
        minor cs addr alloc_fuel
    else begin
      ChunkedCheney.chunked_cheney_forward_normal_success
        minor cs addr alloc_fuel;
      let cs' =
        ChunkedCheney.chunked_cheney_forward_normal
          minor cs addr alloc_fuel in
      reveal_opaque (`%chunked_fwd_in_queue)
        (chunked_fwd_in_queue minor cs');
      let aux (x: U64.t)
        : Lemma
            (requires Seq.mem x (minor_objects minor) /\
                      cs'.ccs_fwd x <> 0UL)
            (ensures Seq.mem x cs'.ccs_queue)
        =
        if x = addr then begin
          Seq.lemma_mem_append cs.ccs_queue (Seq.create 1 addr);
          Seq.mem_cons addr Seq.empty
        end else begin
          ChunkedCheney.chunked_cheney_forward_normal_other_fwd
            minor cs addr x alloc_fuel;
          assert (cs.ccs_fwd x <> 0UL);
          chunked_fwd_in_queue_elim minor cs x;
          Seq.lemma_mem_append cs.ccs_queue (Seq.create 1 addr)
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end
  end

let chunked_cheney_forward_one_preserves_fwd_in_queue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (alloc_fuel: nat)
  : Lemma
      (requires minor_wf minor /\
                chunked_fwd_in_queue minor cs)
      (ensures
        chunked_fwd_in_queue minor
          (ChunkedCheney.chunked_cheney_forward_one
            minor cs addr alloc_fuel))
  =
  if cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_one_noop
      minor cs addr alloc_fuel
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    chunked_cheney_forward_normal_preserves_fwd_in_queue
      minor cs parent alloc_fuel;
    let csn =
      ChunkedCheney.chunked_cheney_forward_normal
        minor cs parent alloc_fuel in
    let r =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs addr alloc_fuel in
    if csn.ccs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (csn.ccs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then begin
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_pass
        minor cs addr alloc_fuel;
      reveal_opaque (`%chunked_fwd_in_queue)
        (chunked_fwd_in_queue minor r);
      let aux (x: U64.t)
        : Lemma
            (requires Seq.mem x (minor_objects minor) /\
                      r.ccs_fwd x <> 0UL)
            (ensures Seq.mem x r.ccs_queue)
        =
        if x = addr then begin
          minor_objects_not_infix minor x;
          assert (minor_tag minor x <> 249);
          assert (minor_tag minor addr = 249);
          assert False
        end else begin
          assert (r.ccs_fwd x == csn.ccs_fwd x);
          assert (csn.ccs_fwd x <> 0UL);
          chunked_fwd_in_queue_elim minor csn x;
          assert (r.ccs_queue == csn.ccs_queue)
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end else
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_fail
        minor cs addr alloc_fuel
  end else begin
    ChunkedCheney.chunked_cheney_forward_one_normal
      minor cs addr alloc_fuel;
    chunked_cheney_forward_normal_preserves_fwd_in_queue
      minor cs addr alloc_fuel
  end

let rec chunked_cheney_forward_fields_preserves_fwd_in_queue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx wosize alloc_fuel: nat)
  : Lemma
      (requires minor_wf minor /\
                chunked_fwd_in_queue minor cs)
      (ensures
        chunked_fwd_in_queue minor
          (ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent idx wosize alloc_fuel))
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    ChunkedCheney.chunked_cheney_forward_fields_base
      minor cs parent idx wosize alloc_fuel
  else begin
    ChunkedCheney.chunked_cheney_forward_fields_step
      minor cs parent idx wosize alloc_fuel;
    let child = to_minor_offset (minor_read_field minor parent idx) in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs child alloc_fuel in
    chunked_cheney_forward_one_preserves_fwd_in_queue
      minor cs child alloc_fuel;
    chunked_cheney_forward_fields_preserves_fwd_in_queue
      minor cs' parent (idx + 1) wosize alloc_fuel
  end

let rec chunked_cheney_forward_roots_preserves_fwd_in_queue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (idx alloc_fuel: nat)
  : Lemma
      (requires minor_wf minor /\
                chunked_fwd_in_queue minor cs)
      (ensures
        chunked_fwd_in_queue minor
          (ChunkedCheney.chunked_cheney_forward_roots
            minor cs roots idx alloc_fuel))
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    ChunkedCheney.chunked_cheney_forward_roots_base
      minor cs roots idx alloc_fuel
  else begin
    ChunkedCheney.chunked_cheney_forward_roots_step
      minor cs roots idx alloc_fuel;
    let r = Seq.index roots idx in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs r alloc_fuel in
    chunked_cheney_forward_one_preserves_fwd_in_queue
      minor cs r alloc_fuel;
    chunked_cheney_forward_roots_preserves_fwd_in_queue
      minor cs' roots (idx + 1) alloc_fuel
  end

let rec chunked_cheney_scan_preserves_fwd_in_queue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat)
  : Lemma
      (requires minor_wf minor /\
                chunked_fwd_in_queue minor cs)
      (ensures
        chunked_fwd_in_queue minor
          (ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel))
      (decreases scan_fuel)
  =
  if scan_fuel = 0 || scan >= Seq.length cs.ccs_queue then
    ChunkedCheney.chunked_cheney_scan_base
      minor cs scan scan_fuel alloc_fuel
  else begin
    assert (scan_fuel > 0);
    let fuel' : f:nat{f < scan_fuel} = scan_fuel - 1 in
    ChunkedCheney.chunked_cheney_scan_step
      minor cs scan scan_fuel alloc_fuel;
    let obj = Seq.index cs.ccs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_fields
        minor cs obj 0 wz alloc_fuel in
    chunked_cheney_forward_fields_preserves_fwd_in_queue
      minor cs obj 0 wz alloc_fuel;
    chunked_cheney_scan_preserves_fwd_in_queue
      minor cs' (scan + 1) fuel' alloc_fuel
  end

let chunked_scanned_exhausted_implies_fwd_closed
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat)
  : Lemma
      (requires
        chunked_fwd_in_queue minor cs /\
        chunked_scanned_prefix_closed minor cs scan /\
        scan >= Seq.length cs.ccs_queue)
      (ensures CheneyBFS.fwd_closed minor cs.ccs_fwd)
  =
  reveal_opaque (`%chunked_scanned_prefix_closed)
    (chunked_scanned_prefix_closed minor cs scan);
  let aux (x y: U64.t)
    : Lemma
        (requires
          Seq.mem x (minor_objects minor) /\
          cs.ccs_fwd x <> 0UL /\
          Seq.mem y (minor_successors minor x) /\
          minor_wosize minor y > 0)
        (ensures cs.ccs_fwd y <> 0UL)
    =
    chunked_fwd_in_queue_elim minor cs x;
    let k = Seq.index_mem x cs.ccs_queue in
    assert (k < Seq.length cs.ccs_queue);
    assert (k < scan);
    assert (Seq.index cs.ccs_queue k == x);
    assert (Seq.mem y (minor_successors minor (Seq.index cs.ccs_queue k)));
    assert (cs.ccs_fwd y <> 0UL)
  in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux)

let chunked_cheney_scan_fwd_closed_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel remaining: nat)
  : Lemma
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
  =
  chunked_cheney_scan_scanned_prefix_from_budget
    minor cs scan scan_fuel alloc_fuel remaining;
  chunked_cheney_scan_preserves_fwd_in_queue
    minor cs scan scan_fuel alloc_fuel;
  let cs' =
    ChunkedCheney.chunked_cheney_scan
      minor cs scan scan_fuel alloc_fuel in
  assert (chunked_scanned_prefix_closed minor cs'
            (chunked_cheney_scan_end_index
              minor cs scan scan_fuel alloc_fuel));
  assert (chunked_fwd_in_queue minor cs');
  chunked_scanned_exhausted_implies_fwd_closed
    minor cs'
    (chunked_cheney_scan_end_index
      minor cs scan scan_fuel alloc_fuel)

#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
private let chunked_queue_potential
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  : prop =
  Seq.length cs.ccs_queue +
  SimOne.count_unforwarded (minor_objects minor) cs.ccs_fwd 0 <=
  Seq.length (minor_objects minor)

private let chunked_queue_potential_initial
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  : Lemma
      (requires cs.ccs_queue == Seq.empty /\
                cs.ccs_fwd == empty_forwarding)
      (ensures chunked_queue_potential minor cs)
  =
  SimOne.count_unforwarded_empty (minor_objects minor) 0

private let chunked_queue_potential_bound
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  : Lemma
      (requires chunked_queue_potential minor cs)
      (ensures Seq.length cs.ccs_queue <= Seq.length (minor_objects minor))
  = ()

private let chunked_cheney_forward_normal_preserves_queue_potential
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (alloc_fuel: nat)
  : Lemma
      (requires chunked_queue_potential minor cs)
      (ensures
        chunked_queue_potential minor
          (ChunkedCheney.chunked_cheney_forward_normal
            minor cs addr alloc_fuel))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_normal_noop
      minor cs addr alloc_fuel
  else if minor_wosize minor addr = 0 then
    ChunkedCheney.chunked_cheney_forward_normal_noop_wz0
      minor cs addr alloc_fuel
  else begin
    assert (Seq.mem addr (minor_objects minor));
    assert (cs.ccs_fwd addr = 0UL);
    let wz = minor_wosize minor addr in
    assert (wz > 0);
    let res =
      ChunkedPromote.chunked_promote_object_with_fuel
        minor cs.ccs_major addr cs.ccs_fp wz alloc_fuel in
    if res.new_addr = 0UL then
      ChunkedCheney.chunked_cheney_forward_normal_noop_oom
        minor cs addr alloc_fuel
    else begin
      ChunkedCheney.chunked_cheney_forward_normal_success
        minor cs addr alloc_fuel;
      let objs = minor_objects minor in
      let cs' =
        ChunkedCheney.chunked_cheney_forward_normal
          minor cs addr alloc_fuel in
      let old_count = SimOne.count_unforwarded objs cs.ccs_fwd 0 in
      let new_count = SimOne.count_unforwarded objs cs'.ccs_fwd 0 in
      FStar.Classical.exists_intro
        (fun (k:nat) ->
          k >= 0 /\ k < Seq.length objs /\
          Seq.index objs k == addr)
        (Seq.index_mem addr objs);
      SimOne.count_unforwarded_decrease
        objs cs.ccs_fwd addr res.new_addr 0;
      Seq.Base.lemma_len_append cs.ccs_queue (Seq.create 1 addr);
      assert (cs'.ccs_fwd ==
              extend_forwarding cs.ccs_fwd addr res.new_addr);
      assert (new_count + 1 <= old_count);
      assert (Seq.length cs'.ccs_queue ==
              Seq.length cs.ccs_queue + 1)
    end
  end

private let chunked_cheney_forward_one_preserves_queue_potential
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (alloc_fuel: nat)
  : Lemma
      (requires minor_wf minor /\
                chunked_queue_potential minor cs)
      (ensures
        chunked_queue_potential minor
          (ChunkedCheney.chunked_cheney_forward_one
            minor cs addr alloc_fuel))
  =
  if cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_one_noop
      minor cs addr alloc_fuel
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    chunked_cheney_forward_normal_preserves_queue_potential
      minor cs parent alloc_fuel;
    let csn =
      ChunkedCheney.chunked_cheney_forward_normal
        minor cs parent alloc_fuel in
    let r =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs addr alloc_fuel in
    assert (chunked_queue_potential minor csn);
    if csn.ccs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (csn.ccs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then begin
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_pass
        minor cs addr alloc_fuel;
      let objs = minor_objects minor in
      let delta = U64.v addr - U64.v parent in
      let sum =
        U64.uint_to_t (U64.v (csn.ccs_fwd parent) + delta) in
      assert (r.ccs_fwd == extend_forwarding csn.ccs_fwd addr sum);
      assert (r.ccs_queue == csn.ccs_queue);
      let aux_ext (k:nat{k >= 0 /\ k < Seq.length objs})
        : Lemma (r.ccs_fwd (Seq.index objs k) ==
                 csn.ccs_fwd (Seq.index objs k))
        =
        let y = Seq.index objs k in
        minor_objects_not_infix minor y;
        assert (minor_tag minor y <> 249);
        assert (minor_tag minor addr = 249);
        assert (y <> addr);
        assert ((extend_forwarding csn.ccs_fwd addr sum) y ==
                csn.ccs_fwd y)
      in
      FStar.Classical.forall_intro aux_ext;
      SimOne.count_unforwarded_ext objs r.ccs_fwd csn.ccs_fwd 0;
      assert (SimOne.count_unforwarded objs r.ccs_fwd 0 ==
              SimOne.count_unforwarded objs csn.ccs_fwd 0)
    end else
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_fail
        minor cs addr alloc_fuel
  end else begin
    ChunkedCheney.chunked_cheney_forward_one_normal
      minor cs addr alloc_fuel;
    chunked_cheney_forward_normal_preserves_queue_potential
      minor cs addr alloc_fuel
  end

private let rec chunked_cheney_forward_fields_preserves_queue_potential
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx wosize alloc_fuel: nat)
  : Lemma
      (requires minor_wf minor /\
                chunked_queue_potential minor cs)
      (ensures
        chunked_queue_potential minor
          (ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent idx wosize alloc_fuel))
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    ChunkedCheney.chunked_cheney_forward_fields_base
      minor cs parent idx wosize alloc_fuel
  else begin
    ChunkedCheney.chunked_cheney_forward_fields_step
      minor cs parent idx wosize alloc_fuel;
    let child = to_minor_offset (minor_read_field minor parent idx) in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs child alloc_fuel in
    chunked_cheney_forward_one_preserves_queue_potential
      minor cs child alloc_fuel;
    chunked_cheney_forward_fields_preserves_queue_potential
      minor cs' parent (idx + 1) wosize alloc_fuel
  end

private let rec chunked_cheney_forward_roots_preserves_queue_potential
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (idx alloc_fuel: nat)
  : Lemma
      (requires minor_wf minor /\
                chunked_queue_potential minor cs)
      (ensures
        chunked_queue_potential minor
          (ChunkedCheney.chunked_cheney_forward_roots
            minor cs roots idx alloc_fuel))
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    ChunkedCheney.chunked_cheney_forward_roots_base
      minor cs roots idx alloc_fuel
  else begin
    ChunkedCheney.chunked_cheney_forward_roots_step
      minor cs roots idx alloc_fuel;
    let r = Seq.index roots idx in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs r alloc_fuel in
    chunked_cheney_forward_one_preserves_queue_potential
      minor cs r alloc_fuel;
    chunked_cheney_forward_roots_preserves_queue_potential
      minor cs' roots (idx + 1) alloc_fuel
  end

private let rec chunked_cheney_scan_preserves_queue_potential
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat)
  : Lemma
      (requires minor_wf minor /\
                chunked_queue_potential minor cs)
      (ensures
        chunked_queue_potential minor
          (ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel))
      (decreases scan_fuel)
  =
  if scan_fuel = 0 || scan >= Seq.length cs.ccs_queue then
    ChunkedCheney.chunked_cheney_scan_base
      minor cs scan scan_fuel alloc_fuel
  else begin
    assert (scan_fuel > 0);
    let fuel' : f:nat{f < scan_fuel} = scan_fuel - 1 in
    ChunkedCheney.chunked_cheney_scan_step
      minor cs scan scan_fuel alloc_fuel;
    let obj = Seq.index cs.ccs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_fields
        minor cs obj 0 wz alloc_fuel in
    chunked_cheney_forward_fields_preserves_queue_potential
      minor cs obj 0 wz alloc_fuel;
    chunked_cheney_scan_preserves_queue_potential
      minor cs' (scan + 1) fuel' alloc_fuel
  end

let chunked_cheney_promote_scan_exhaustion
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
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
         chunked_cheney_scan_end_index
          minor cs1 0 (cheney_fuel minor) alloc_fuel >=
         Seq.length cs2.ccs_queue))
  =
  let cs0 : ChunkedCheney.chunked_cheney_state =
    { ccs_major = major; ccs_fp = fp;
      ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
  chunked_queue_potential_initial minor cs0;
  chunked_cheney_forward_roots_preserves_queue_potential
    minor cs0 roots 0 alloc_fuel;
  let cs1 =
    ChunkedCheney.chunked_cheney_forward_roots
      minor cs0 roots 0 alloc_fuel in
  assert (chunked_queue_potential minor cs1);
  chunked_cheney_scan_preserves_queue_potential
    minor cs1 0 (cheney_fuel minor) alloc_fuel;
  let cs2 =
    ChunkedCheney.chunked_cheney_scan
      minor cs1 0 (cheney_fuel minor) alloc_fuel in
  assert (chunked_queue_potential minor cs2);
  chunked_queue_potential_bound minor cs2;
  chunked_cheney_scan_end_exhausted_or_fuel
    minor cs1 0 (cheney_fuel minor) alloc_fuel;
  let end_idx =
    chunked_cheney_scan_end_index
      minor cs1 0 (cheney_fuel minor) alloc_fuel in
  assert (end_idx >= Seq.length cs2.ccs_queue \/
          end_idx == 0 + cheney_fuel minor);
  if end_idx >= Seq.length cs2.ccs_queue then ()
  else begin
    assert (end_idx == cheney_fuel minor);
    cheney_fuel_eq minor;
    assert (cheney_fuel minor == Seq.length (minor_objects minor));
    assert (Seq.length cs2.ccs_queue <= Seq.length (minor_objects minor));
    assert (end_idx >= Seq.length cs2.ccs_queue)
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
private let chunked_demand_view
  (cs: ChunkedCheney.chunked_cheney_state)
  : GTot cheney_state =
  { cs_major = Seq.create heap_size 0uy;
    cs_fp = 0UL;
    cs_fwd = cs.ccs_fwd;
    cs_queue = cs.ccs_queue }

private let chunked_cheney_unforwarded_split_demand
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  : GTot nat =
  cheney_unforwarded_split_demand minor (chunked_demand_view cs)

private let chunked_cheney_unforwarded_split_demand_bound
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  : Lemma
      (ensures
        chunked_cheney_unforwarded_split_demand minor cs <=
        PromotionDemand.minor_promotion_demand minor)
  =
  cheney_unforwarded_split_demand_bound minor (chunked_demand_view cs)

private let chunked_cheney_unforwarded_split_demand_object_bound
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (obj: U64.t)
  : Lemma
      (requires Seq.mem obj (minor_objects minor) /\
                cs.ccs_fwd obj = 0UL)
      (ensures
        SpecMajorAllocMultiAlloc.request_split_demand
          (minor_wosize minor obj) <=
        chunked_cheney_unforwarded_split_demand minor cs)
  =
  cheney_unforwarded_split_demand_object_bound
    minor (chunked_demand_view cs) obj

private let chunked_cheney_unforwarded_split_demand_state_extend_decrease
  (minor: minor_state)
  (cs cs_after: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (new_addr: U64.t)
  : Lemma
      (requires new_addr <> 0UL /\
                Seq.mem addr (minor_objects minor) /\
                cs.ccs_fwd addr = 0UL /\
                cs_after.ccs_fwd ==
                  extend_forwarding cs.ccs_fwd addr new_addr)
      (ensures
        SpecMajorAllocMultiAlloc.request_split_demand
          (minor_wosize minor addr) +
        chunked_cheney_unforwarded_split_demand minor cs_after <=
        chunked_cheney_unforwarded_split_demand minor cs)
  =
  let dv = chunked_demand_view cs in
  let dv_after = chunked_demand_view cs_after in
  assert (dv_after.cs_fwd == extend_forwarding dv.cs_fwd addr new_addr);
  cheney_unforwarded_split_demand_state_extend_decrease
    minor dv dv_after addr new_addr

private let chunked_cheney_unforwarded_split_demand_state_extend_infix_monotone
  (minor: minor_state)
  (cs cs_after: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (new_addr: U64.t)
  : Lemma
      (requires minor_wf minor /\
                is_infix_in_minor minor addr /\
                cs_after.ccs_fwd ==
                  extend_forwarding cs.ccs_fwd addr new_addr)
      (ensures
        chunked_cheney_unforwarded_split_demand minor cs_after <=
        chunked_cheney_unforwarded_split_demand minor cs)
  =
  let dv = chunked_demand_view cs in
  let dv_after = chunked_demand_view cs_after in
  assert (dv_after.cs_fwd == extend_forwarding dv.cs_fwd addr new_addr);
  cheney_unforwarded_split_demand_state_extend_infix_monotone
    minor dv dv_after addr new_addr

private let chunked_cheney_forward_one_split_demand
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t)
  : GTot nat =
  if cs.ccs_fwd addr <> 0UL then 0
  else if is_infix_in_minor minor addr then
    let parent = infix_parent minor addr in
    if Seq.mem parent (minor_objects minor) &&
       cs.ccs_fwd parent = 0UL &&
       minor_wosize minor parent > 0
    then SpecMajorAllocMultiAlloc.request_split_demand
           (minor_wosize minor parent)
    else 0
  else if Seq.mem addr (minor_objects minor) &&
          minor_wosize minor addr > 0
  then SpecMajorAllocMultiAlloc.request_split_demand
         (minor_wosize minor addr)
  else 0

private let chunked_cheney_forward_one_budget_ready_from_split_demand
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (remaining: nat)
  : Lemma
      (requires
        remaining > 0 /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >=
        chunked_cheney_forward_one_split_demand minor cs addr + remaining)
      (ensures
        chunked_cheney_forward_one_budget_ready
          minor cs addr remaining)
  =
  let head =
    SpecMajorAlloc.major_fl_head_wosize cs.ccs_major cs.ccs_fp in
  assert (head >= remaining);
  if Seq.mem addr (minor_objects minor) &&
     cs.ccs_fwd addr = 0UL &&
     not (is_infix_in_minor minor addr) &&
     minor_wosize minor addr > 0
  then begin
    let wz = minor_wosize minor addr in
    SpecMajorAllocMultiAlloc.request_split_demand_positive_identity wz;
    assert (chunked_cheney_forward_one_split_demand minor cs addr ==
            SpecMajorAllocMultiAlloc.request_split_demand wz);
    assert (SpecMajorAllocMultiAlloc.request_split_demand wz == wz + 1);
    assert (head >= wz + 1 + remaining);
    if cs.ccs_fp = 0UL then begin
      assert (head == 0);
      assert False
    end
  end;
  assert (Seq.mem addr (minor_objects minor) /\
          cs.ccs_fwd addr = 0UL /\
          ~(is_infix_in_minor minor addr) /\
          minor_wosize minor addr > 0 ==>
            cs.ccs_fp <> 0UL /\
            SpecMajorAlloc.major_fl_head_wosize
              cs.ccs_major cs.ccs_fp >=
            minor_wosize minor addr + 1 + remaining);
  if cs.ccs_fwd addr = 0UL && is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    if Seq.mem parent (minor_objects minor) &&
       cs.ccs_fwd parent = 0UL &&
       minor_wosize minor parent > 0
    then begin
      let wz = minor_wosize minor parent in
      SpecMajorAllocMultiAlloc.request_split_demand_positive_identity wz;
      assert (chunked_cheney_forward_one_split_demand minor cs addr ==
              SpecMajorAllocMultiAlloc.request_split_demand wz);
      assert (SpecMajorAllocMultiAlloc.request_split_demand wz == wz + 1);
      assert (head >= wz + 1 + remaining);
      if cs.ccs_fp = 0UL then begin
        assert (head == 0);
        assert False
      end
    end
  end;
  assert (cs.ccs_fwd addr = 0UL /\
          is_infix_in_minor minor addr ==>
            (let parent = infix_parent minor addr in
             Seq.mem parent (minor_objects minor) /\
             cs.ccs_fwd parent = 0UL /\
             minor_wosize minor parent > 0 ==>
               cs.ccs_fp <> 0UL /\
               SpecMajorAlloc.major_fl_head_wosize
                 cs.ccs_major cs.ccs_fp >=
               minor_wosize minor parent + 1 + remaining))
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
private let chunked_cheney_forward_one_unforwarded_split_demand_decreases
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >=
        chunked_cheney_unforwarded_split_demand minor cs + 1)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_one
             minor cs addr alloc_fuel in
         chunked_cheney_forward_one_split_demand minor cs addr +
         chunked_cheney_unforwarded_split_demand minor cs' <=
         chunked_cheney_unforwarded_split_demand minor cs))
  =
  let head =
    SpecMajorAlloc.major_fl_head_wosize cs.ccs_major cs.ccs_fp in
  let old_demand = chunked_cheney_unforwarded_split_demand minor cs in
  assert (head >= old_demand + 1);
  assert (head > 0);
  if cs.ccs_fp = 0UL then begin
    assert (head == 0);
    assert False
  end;
  if cs.ccs_fwd addr <> 0UL then begin
    ChunkedCheney.chunked_cheney_forward_one_noop minor cs addr alloc_fuel;
    assert (chunked_cheney_forward_one_split_demand minor cs addr == 0);
    assert (ChunkedCheney.chunked_cheney_forward_one
              minor cs addr alloc_fuel == cs)
  end else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    let csn =
      ChunkedCheney.chunked_cheney_forward_normal
        minor cs parent alloc_fuel in
    if Seq.mem parent (minor_objects minor) &&
       cs.ccs_fwd parent = 0UL &&
       minor_wosize minor parent > 0
    then begin
      let wz = minor_wosize minor parent in
      let req = SpecMajorAllocMultiAlloc.request_split_demand wz in
      chunked_cheney_unforwarded_split_demand_object_bound minor cs parent;
      SpecMajorAllocMultiAlloc.request_split_demand_positive_identity wz;
      assert (req == wz + 1);
      assert (req <= old_demand);
      assert (head >= wz + 2);
      chunked_promote_object_head_split_preserves_remaining_head_wosize
        minor cs.ccs_major parent cs.ccs_fp wz alloc_fuel 1;
      let res =
        ChunkedPromote.chunked_promote_object_with_fuel
          minor cs.ccs_major parent cs.ccs_fp wz alloc_fuel in
      assert (res.new_addr <> 0UL);
      ChunkedCheney.chunked_cheney_forward_normal_success
        minor cs parent alloc_fuel;
      assert (csn.ccs_fwd ==
              extend_forwarding cs.ccs_fwd parent res.new_addr);
      chunked_cheney_unforwarded_split_demand_state_extend_decrease
        minor cs csn parent res.new_addr;
      assert (req +
              chunked_cheney_unforwarded_split_demand minor csn <=
              old_demand);
      if csn.ccs_fwd parent <> 0UL &&
         U64.v addr >= U64.v parent &&
         U64.v (csn.ccs_fwd parent) + (U64.v addr - U64.v parent) <
           heap_size
      then begin
        let sum =
          U64.uint_to_t
            (U64.v (csn.ccs_fwd parent) +
             (U64.v addr - U64.v parent)) in
        ChunkedCheney.chunked_cheney_forward_one_infix_guard_pass
          minor cs addr alloc_fuel;
        assert ((ChunkedCheney.chunked_cheney_forward_one
                   minor cs addr alloc_fuel).ccs_fwd ==
                extend_forwarding csn.ccs_fwd addr sum);
        chunked_cheney_unforwarded_split_demand_state_extend_infix_monotone
          minor csn
          (ChunkedCheney.chunked_cheney_forward_one
             minor cs addr alloc_fuel)
          addr sum;
        assert (chunked_cheney_unforwarded_split_demand
                  minor
                  (ChunkedCheney.chunked_cheney_forward_one
                     minor cs addr alloc_fuel) <=
                chunked_cheney_unforwarded_split_demand minor csn)
      end else begin
        ChunkedCheney.chunked_cheney_forward_one_infix_guard_fail
          minor cs addr alloc_fuel;
        assert (ChunkedCheney.chunked_cheney_forward_one
                  minor cs addr alloc_fuel == csn);
        assert (chunked_cheney_unforwarded_split_demand
                  minor
                  (ChunkedCheney.chunked_cheney_forward_one
                     minor cs addr alloc_fuel) <=
                chunked_cheney_unforwarded_split_demand minor csn)
      end;
      assert (req +
              chunked_cheney_unforwarded_split_demand
                minor
                (ChunkedCheney.chunked_cheney_forward_one
                   minor cs addr alloc_fuel) <=
              old_demand);
      assert (chunked_cheney_forward_one_split_demand minor cs addr == req)
    end else begin
      if not (Seq.mem parent (minor_objects minor)) then
        ChunkedCheney.chunked_cheney_forward_normal_noop
          minor cs parent alloc_fuel
      else if cs.ccs_fwd parent <> 0UL then
        ChunkedCheney.chunked_cheney_forward_normal_noop
          minor cs parent alloc_fuel
      else begin
        assert (minor_wosize minor parent = 0);
        ChunkedCheney.chunked_cheney_forward_normal_noop_wz0
          minor cs parent alloc_fuel
      end;
      assert (csn == cs);
      if csn.ccs_fwd parent <> 0UL &&
         U64.v addr >= U64.v parent &&
         U64.v (csn.ccs_fwd parent) + (U64.v addr - U64.v parent) <
           heap_size
      then begin
        let sum =
          U64.uint_to_t
            (U64.v (csn.ccs_fwd parent) +
             (U64.v addr - U64.v parent)) in
        ChunkedCheney.chunked_cheney_forward_one_infix_guard_pass
          minor cs addr alloc_fuel;
        assert ((ChunkedCheney.chunked_cheney_forward_one
                   minor cs addr alloc_fuel).ccs_fwd ==
                extend_forwarding cs.ccs_fwd addr sum);
        chunked_cheney_unforwarded_split_demand_state_extend_infix_monotone
          minor cs
          (ChunkedCheney.chunked_cheney_forward_one
             minor cs addr alloc_fuel)
          addr sum;
        assert (chunked_cheney_unforwarded_split_demand
                  minor
                  (ChunkedCheney.chunked_cheney_forward_one
                     minor cs addr alloc_fuel) <=
                old_demand)
      end else begin
        ChunkedCheney.chunked_cheney_forward_one_infix_guard_fail
          minor cs addr alloc_fuel;
        assert (ChunkedCheney.chunked_cheney_forward_one
                  minor cs addr alloc_fuel == cs);
        assert (chunked_cheney_unforwarded_split_demand
                  minor
                  (ChunkedCheney.chunked_cheney_forward_one
                     minor cs addr alloc_fuel) <=
                old_demand)
      end;
      assert (chunked_cheney_forward_one_split_demand minor cs addr == 0)
    end
  end else begin
    ChunkedCheney.chunked_cheney_forward_one_normal
      minor cs addr alloc_fuel;
    if not (Seq.mem addr (minor_objects minor)) then begin
      ChunkedCheney.chunked_cheney_forward_normal_noop
        minor cs addr alloc_fuel;
      assert (ChunkedCheney.chunked_cheney_forward_one
                minor cs addr alloc_fuel == cs);
      assert (chunked_cheney_forward_one_split_demand minor cs addr == 0)
    end else begin
      let wz = minor_wosize minor addr in
      if wz = 0 then begin
        ChunkedCheney.chunked_cheney_forward_normal_noop_wz0
          minor cs addr alloc_fuel;
        assert (ChunkedCheney.chunked_cheney_forward_one
                  minor cs addr alloc_fuel == cs);
        assert (chunked_cheney_forward_one_split_demand minor cs addr == 0)
      end else begin
        assert (wz > 0);
        let req = SpecMajorAllocMultiAlloc.request_split_demand wz in
        chunked_cheney_unforwarded_split_demand_object_bound minor cs addr;
        SpecMajorAllocMultiAlloc.request_split_demand_positive_identity wz;
        assert (req == wz + 1);
        assert (req <= old_demand);
        assert (head >= wz + 2);
        chunked_promote_object_head_split_preserves_remaining_head_wosize
          minor cs.ccs_major addr cs.ccs_fp wz alloc_fuel 1;
        let res =
          ChunkedPromote.chunked_promote_object_with_fuel
            minor cs.ccs_major addr cs.ccs_fp wz alloc_fuel in
        assert (res.new_addr <> 0UL);
        ChunkedCheney.chunked_cheney_forward_normal_success
          minor cs addr alloc_fuel;
        assert ((ChunkedCheney.chunked_cheney_forward_one
                   minor cs addr alloc_fuel).ccs_fwd ==
                extend_forwarding cs.ccs_fwd addr res.new_addr);
        chunked_cheney_unforwarded_split_demand_state_extend_decrease
          minor cs
          (ChunkedCheney.chunked_cheney_forward_one
             minor cs addr alloc_fuel)
          addr res.new_addr;
        assert (req +
                chunked_cheney_unforwarded_split_demand
                  minor
                  (ChunkedCheney.chunked_cheney_forward_one
                     minor cs addr alloc_fuel) <=
                old_demand);
        assert (chunked_cheney_forward_one_split_demand minor cs addr == req)
      end
    end
  end

private let chunked_cheney_forward_one_budget_ready_from_unforwarded
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >=
        chunked_cheney_unforwarded_split_demand minor cs + 1)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_one
             minor cs addr alloc_fuel in
         chunked_cheney_forward_one_budget_ready minor cs addr 1 /\
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           cs'.ccs_major cs'.ccs_fp >=
         chunked_cheney_unforwarded_split_demand minor cs' + 1))
  =
  let cs' =
    ChunkedCheney.chunked_cheney_forward_one
      minor cs addr alloc_fuel in
  let d = chunked_cheney_forward_one_split_demand minor cs addr in
  let after = chunked_cheney_unforwarded_split_demand minor cs' in
  let old_demand = chunked_cheney_unforwarded_split_demand minor cs in
  let head =
    SpecMajorAlloc.major_fl_head_wosize cs.ccs_major cs.ccs_fp in
  chunked_cheney_forward_one_unforwarded_split_demand_decreases
    minor cs addr alloc_fuel;
  assert (d + after <= old_demand);
  assert (head >= d + after + 1);
  assert (head >= d + 1);
  chunked_cheney_forward_one_budget_ready_from_split_demand
    minor cs addr 1;
  chunked_cheney_forward_one_budget_ready_from_split_demand
    minor cs addr (after + 1);
  chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
    minor cs addr alloc_fuel (after + 1)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
private let rec chunked_cheney_forward_roots_budget_ready_from_unforwarded
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (idx: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >=
        chunked_cheney_unforwarded_split_demand minor cs + 1)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_roots
             minor cs roots idx alloc_fuel in
         chunked_cheney_forward_roots_budget_ready
           minor cs roots idx alloc_fuel 1 /\
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           cs'.ccs_major cs'.ccs_fp >=
         chunked_cheney_unforwarded_split_demand minor cs' + 1))
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then begin
    ChunkedCheney.chunked_cheney_forward_roots_base
      minor cs roots idx alloc_fuel;
    assert (SpecMajorAlloc.major_fl_head_wosize
              cs.ccs_major cs.ccs_fp >= 1)
  end else begin
    ChunkedCheney.chunked_cheney_forward_roots_step
      minor cs roots idx alloc_fuel;
    let r = Seq.index roots idx in
    let cs1 =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs r alloc_fuel in
    chunked_cheney_forward_one_budget_ready_from_unforwarded
      minor cs r alloc_fuel;
    assert (GenInv.chunked_major_alloc_shape
              cs1.ccs_major cs1.ccs_fp alloc_fuel);
    assert (SpecMajorAlloc.major_fl_chain_terminates
              cs1.ccs_major cs1.ccs_fp alloc_fuel = true);
    assert (SpecMajorAlloc.major_fl_head_wosize
              cs1.ccs_major cs1.ccs_fp >=
            chunked_cheney_unforwarded_split_demand minor cs1 + 1);
    chunked_cheney_forward_roots_budget_ready_from_unforwarded
      minor cs1 roots (idx + 1) alloc_fuel;
    assert (chunked_cheney_forward_one_budget_ready minor cs r 1);
    assert (chunked_cheney_forward_roots_budget_ready
              minor cs1 roots (idx + 1) alloc_fuel 1)
  end

private let rec chunked_cheney_forward_fields_budget_ready_from_unforwarded
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >=
        chunked_cheney_unforwarded_split_demand minor cs + 1)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_fields
             minor cs parent idx wosize alloc_fuel in
         chunked_cheney_forward_fields_budget_ready
           minor cs parent idx wosize alloc_fuel 1 /\
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           cs'.ccs_major cs'.ccs_fp >=
         chunked_cheney_unforwarded_split_demand minor cs' + 1))
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then begin
    ChunkedCheney.chunked_cheney_forward_fields_base
      minor cs parent idx wosize alloc_fuel;
    assert (SpecMajorAlloc.major_fl_head_wosize
              cs.ccs_major cs.ccs_fp >= 1)
  end else begin
    ChunkedCheney.chunked_cheney_forward_fields_step
      minor cs parent idx wosize alloc_fuel;
    let field_val =
      to_minor_offset (minor_read_field minor parent idx) in
    let cs1 =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs field_val alloc_fuel in
    chunked_cheney_forward_one_budget_ready_from_unforwarded
      minor cs field_val alloc_fuel;
    assert (GenInv.chunked_major_alloc_shape
              cs1.ccs_major cs1.ccs_fp alloc_fuel);
    assert (SpecMajorAlloc.major_fl_chain_terminates
              cs1.ccs_major cs1.ccs_fp alloc_fuel = true);
    assert (SpecMajorAlloc.major_fl_head_wosize
              cs1.ccs_major cs1.ccs_fp >=
            chunked_cheney_unforwarded_split_demand minor cs1 + 1);
    chunked_cheney_forward_fields_budget_ready_from_unforwarded
      minor cs1 parent (idx + 1) wosize alloc_fuel;
    assert (chunked_cheney_forward_one_budget_ready
              minor cs field_val 1);
    assert (chunked_cheney_forward_fields_budget_ready
              minor cs1 parent (idx + 1) wosize alloc_fuel 1)
  end

private let rec chunked_cheney_scan_budget_ready_from_unforwarded
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat) (scan_fuel: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >=
        chunked_cheney_unforwarded_split_demand minor cs + 1)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
         chunked_cheney_scan_budget_ready
           minor cs scan scan_fuel alloc_fuel 1 /\
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           cs'.ccs_major cs'.ccs_fp >=
         chunked_cheney_unforwarded_split_demand minor cs' + 1))
      (decreases scan_fuel)
  =
  if scan_fuel > 0 then
    if scan >= Seq.length cs.ccs_queue then begin
      ChunkedCheney.chunked_cheney_scan_base
        minor cs scan scan_fuel alloc_fuel;
      assert (SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= 1)
    end else begin
      ChunkedCheney.chunked_cheney_scan_step
        minor cs scan scan_fuel alloc_fuel;
      let fuel' : f:nat{f < scan_fuel} = scan_fuel - 1 in
      let obj = Seq.index cs.ccs_queue scan in
      let wz = minor_wosize minor obj in
      let cs1 =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs obj 0 wz alloc_fuel in
      chunked_cheney_forward_fields_budget_ready_from_unforwarded
        minor cs obj 0 wz alloc_fuel;
      assert (GenInv.chunked_major_alloc_shape
                cs1.ccs_major cs1.ccs_fp alloc_fuel);
      assert (SpecMajorAlloc.major_fl_chain_terminates
                cs1.ccs_major cs1.ccs_fp alloc_fuel = true);
      assert (SpecMajorAlloc.major_fl_head_wosize
                cs1.ccs_major cs1.ccs_fp >=
              chunked_cheney_unforwarded_split_demand minor cs1 + 1);
      chunked_cheney_scan_budget_ready_from_unforwarded
        minor cs1 (scan + 1) fuel' alloc_fuel;
      assert (chunked_cheney_forward_fields_budget_ready
                minor cs obj 0 wz alloc_fuel 1);
      assert (chunked_cheney_scan_budget_ready
                minor cs1 (scan + 1) fuel' alloc_fuel 1)
    end
  else begin
    ChunkedCheney.chunked_cheney_scan_base
      minor cs scan scan_fuel alloc_fuel;
    assert (SpecMajorAlloc.major_fl_head_wosize
              cs.ccs_major cs.ccs_fp >= 1)
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let chunked_cheney_promote_budget_ready_from_minor_demand
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
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
        chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel 1)
  =
  let cs0 : ChunkedCheney.chunked_cheney_state =
    { ccs_major = major; ccs_fp = fp;
      ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
  chunked_cheney_unforwarded_split_demand_bound minor cs0;
  assert (chunked_cheney_unforwarded_split_demand minor cs0 <=
          PromotionDemand.minor_promotion_demand minor);
  assert (SpecMajorAlloc.major_fl_head_wosize major fp >=
          chunked_cheney_unforwarded_split_demand minor cs0 + 1);
  chunked_cheney_forward_roots_budget_ready_from_unforwarded
    minor cs0 roots 0 alloc_fuel;
  let cs1 =
    ChunkedCheney.chunked_cheney_forward_roots
      minor cs0 roots 0 alloc_fuel in
  assert (GenInv.chunked_major_alloc_shape
            cs1.ccs_major cs1.ccs_fp alloc_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            cs1.ccs_major cs1.ccs_fp alloc_fuel = true);
  assert (SpecMajorAlloc.major_fl_head_wosize
            cs1.ccs_major cs1.ccs_fp >=
          chunked_cheney_unforwarded_split_demand minor cs1 + 1);
  chunked_cheney_scan_budget_ready_from_unforwarded
    minor cs1 0 (cheney_fuel minor) alloc_fuel;
  assert (chunked_cheney_forward_roots_budget_ready
            minor cs0 roots 0 alloc_fuel 1);
  assert (chunked_cheney_scan_budget_ready
            minor cs1 0 (cheney_fuel minor) alloc_fuel 1)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let chunked_cheney_scan_preserves_fwd_covers_roots
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (scan scan_fuel alloc_fuel: nat)
  : Lemma
      (requires CheneyBFS.fwd_covers_roots minor cs.ccs_fwd roots)
      (ensures
        CheneyBFS.fwd_covers_roots minor
          (ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel).ccs_fwd
          roots)
  =
  let cs' =
    ChunkedCheney.chunked_cheney_scan
      minor cs scan scan_fuel alloc_fuel in
  let aux (r: U64.t)
    : Lemma
        (requires Seq.mem r roots /\
                  Seq.mem r (minor_objects minor) /\
                  minor_wosize minor r > 0)
        (ensures cs'.ccs_fwd r <> 0UL)
    =
    assert (cs.ccs_fwd r <> 0UL);
    chunked_cheney_scan_fwd_monotone
      minor cs scan scan_fuel alloc_fuel r
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let chunked_cheney_no_oom
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
  : GTot prop =
  CheneyBFS.fwd_well_formed minor
    (ChunkedCheney.chunked_cheney_promote
      minor major fp roots alloc_fuel).fwd_map
    roots

let chunked_cheney_promote_no_oom_from_budget_and_scan_exhaustion
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
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
         chunked_cheney_scan_end_index
          minor cs1 0 (cheney_fuel minor) alloc_fuel >=
         Seq.length cs2.ccs_queue))
      (ensures
        chunked_cheney_no_oom minor major fp roots alloc_fuel)
  =
  let cs0 : ChunkedCheney.chunked_cheney_state =
    { ccs_major = major; ccs_fp = fp;
      ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
  chunked_cheney_promote_budget_ready_from_minor_demand
    minor major fp roots alloc_fuel;
  assert (chunked_cheney_forward_roots_budget_ready
            minor cs0 roots 0 alloc_fuel 1);
  chunked_cheney_forward_roots_covers_roots_from_budget
    minor cs0 roots alloc_fuel 1;
  chunked_cheney_forward_roots_head_split_preserves_remaining_head_wosize
    minor cs0 roots 0 alloc_fuel 1;
  chunked_fwd_in_queue_initial minor cs0;
  chunked_cheney_forward_roots_preserves_fwd_in_queue
    minor cs0 roots 0 alloc_fuel;
  let cs1 =
    ChunkedCheney.chunked_cheney_forward_roots
      minor cs0 roots 0 alloc_fuel in
  assert (CheneyBFS.fwd_covers_roots minor cs1.ccs_fwd roots);
  assert (GenInv.chunked_major_alloc_shape
            cs1.ccs_major cs1.ccs_fp alloc_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            cs1.ccs_major cs1.ccs_fp alloc_fuel = true);
  assert (chunked_fwd_in_queue minor cs1);
  assert (chunked_cheney_scan_budget_ready
            minor cs1 0 (cheney_fuel minor) alloc_fuel 1);
  chunked_scanned_prefix_empty minor cs1;
  chunked_cheney_scan_fwd_closed_from_budget
    minor cs1 0 (cheney_fuel minor) alloc_fuel 1;
  chunked_cheney_scan_preserves_fwd_covers_roots
    minor cs1 roots 0 (cheney_fuel minor) alloc_fuel;
  let cs2 =
    ChunkedCheney.chunked_cheney_scan
      minor cs1 0 (cheney_fuel minor) alloc_fuel in
  assert (CheneyBFS.fwd_covers_roots minor cs2.ccs_fwd roots);
  assert (CheneyBFS.fwd_closed minor cs2.ccs_fwd);
  let res =
    ChunkedCheney.chunked_cheney_promote
      minor major fp roots alloc_fuel in
  ChunkedCheney.chunked_cheney_promote_equation
    minor major fp roots alloc_fuel;
  assert (res.fwd_map == cs2.ccs_fwd)

let chunked_cheney_promote_no_oom_from_budget
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
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
        chunked_cheney_no_oom minor major fp roots alloc_fuel)
  =
  chunked_cheney_promote_scan_exhaustion
    minor major fp roots alloc_fuel;
  chunked_cheney_promote_no_oom_from_budget_and_scan_exhaustion
    minor major fp roots alloc_fuel
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_cheney_promote_after_minor_promotion_head_preflight
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
         GenInv.chunked_major_alloc_shape
           res.major_final res.fp_final r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_final res.fp_final r.capacity_fuel_out = true /\
         SpecMajorAlloc.major_fl_head_wosize
           res.major_final res.fp_final >= 1))
  =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  assert (needed > 0);
  GenInv.chunked_collection_heap_shape_ensure_head_capacity_with_chain
    minor major fp alloc_fuel needed fresh;
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  assert (GenInv.chunked_collection_heap_shape
            minor r.capacity_major_out r.capacity_fp_out
            r.capacity_fuel_out);
  assert (SpecMajorAlloc.major_fl_head_wosize
            r.capacity_major_out r.capacity_fp_out >= needed);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out =
          true);
  GenInv.chunked_collection_heap_shape_elim
    minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out;
  assert (GenInv.chunked_major_alloc_shape
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out);
  if SpecMajorAlloc.major_fl_head_wosize major fp >= needed then begin
    assert (r.capacity_major_out == major);
    assert (r.capacity_fp_out == fp);
    assert (r.capacity_fuel_out == alloc_fuel)
  end else begin
    assert (r.capacity_fuel_out == alloc_fuel + 1);
    assert (r.capacity_fp_out == SpecMajorAlloc.fresh_chunk_object fresh);
    SpecMajorAlloc.fresh_chunk_object_in_chunk fresh;
    assert (SpecMajorAlloc.fresh_chunk_object fresh <> 0UL);
    assert (r.capacity_fp_out <> 0UL)
  end;
  assert (r.capacity_fuel_out > 1);
  assert (r.capacity_fp_out <> 0UL);
  chunked_cheney_promote_budget_ready_from_minor_demand
    minor r.capacity_major_out r.capacity_fp_out roots
    r.capacity_fuel_out;
  assert (chunked_cheney_promote_budget_ready
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out 1);
  chunked_cheney_promote_head_split_preserves_remaining_head_wosize
    minor r.capacity_major_out r.capacity_fp_out roots
    r.capacity_fuel_out 1;
  let res =
    ChunkedCheney.chunked_cheney_promote
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  assert (GenInv.chunked_major_alloc_shape
            res.major_final res.fp_final r.capacity_fuel_out);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            res.major_final res.fp_final r.capacity_fuel_out = true);
  assert (SpecMajorAlloc.major_fl_head_wosize
            res.major_final res.fp_final >= 1)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let promote_object_head_split_preserves_chunked_alloc_shape_single_chunk
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
  let fuel = SpecAlloc.alloc_search_fuel in
  let mh = MH.single_chunk_major_heap major in
  GenInv.chunked_major_alloc_shape_elim mh fp fuel;
  alloc_spec_head_split_alloc_wosize_single_chunk major fp wosize;
  promote_object_head_split_padding_noop_single_chunk minor major obj fp wosize;
  let alloc_res = SpecAlloc.alloc_spec major fp wosize in
  promote_object_success minor major obj fp wosize;
  let res = promote_object minor major obj fp wosize in
  assert (res.new_addr == fp);
  assert (res.fp_out == alloc_res.fp_out);
  assert (res.fp_out <> 0UL);
  SpecMajorAlloc.major_alloc_spec_with_fuel_single_chunk_compat
    major fp wosize fuel;
  assert (SpecAlloc.alloc_spec major fp wosize ==
          SpecAlloc.alloc_spec_with_fuel major fp wosize fuel);
  let ma =
    SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
  assert (ma.major_alloc_out == MH.single_chunk_major_heap alloc_res.heap_out);
  assert (ma.major_fp_out == alloc_res.fp_out);
  assert (ma.major_obj_out == alloc_res.obj_out);
  SpecMajorAllocSplitShape.major_alloc_head_split_preserves_alloc_shape
    mh fp wosize fuel;
  SpecMajorAllocSplitShape.major_alloc_head_split_remainder_avoids_allocated_head
    mh fp wosize fuel;
  assert (SpecMajorAlloc.major_fl_valid
            (MH.single_chunk_major_heap alloc_res.heap_out)
            alloc_res.fp_out fuel);
  assert (SpecMajorAlloc.major_fl_above_zero
            (MH.single_chunk_major_heap alloc_res.heap_out)
            alloc_res.fp_out fuel);
  assert (SpecMajorAlloc.major_fl_blocks_fit
            (MH.single_chunk_major_heap alloc_res.heap_out)
            alloc_res.fp_out fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            (MH.single_chunk_major_heap alloc_res.heap_out)
            alloc_res.fp_out fuel = true);
  assert (SpecMajorAlloc.major_fl_chain_avoids
            (MH.single_chunk_major_heap alloc_res.heap_out)
            alloc_res.fp_out (fp <: obj_addr) fuel = true);
  promote_object_head_split_preserves_objects_from_alloc_single_chunk
    minor major obj fp wosize;
  let header_frame (src: obj_addr)
    : Lemma
        (requires Seq.mem src (objects zero_addr alloc_res.heap_out) /\
                  src <> (fp <: obj_addr))
        (ensures read_word res.major_out (hd_address src) ==
                 read_word alloc_res.heap_out (hd_address src))
    =
    promote_object_head_split_frame_header_from_alloc_single_chunk
      minor major obj fp wosize src
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires header_frame);
  let link_frame (src: obj_addr)
    : Lemma
        (requires Seq.mem src (objects zero_addr alloc_res.heap_out) /\
                  src <> (fp <: obj_addr) /\
                  U64.v (wosize_of_object src alloc_res.heap_out) >= 1)
        (ensures read_word res.major_out src ==
                 read_word alloc_res.heap_out src)
    =
    promote_object_head_split_frame_field0_from_alloc_single_chunk
      minor major obj fp wosize src
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires link_frame);
  single_chunk_fl_shape_transfer_avoids
    alloc_res.heap_out res.major_out (fp <: obj_addr) alloc_res.fp_out fuel;
  assert (res.fp_out == alloc_res.fp_out);
  assert (SpecMajorAlloc.major_fl_valid
            (MH.single_chunk_major_heap res.major_out) res.fp_out fuel);
  assert (SpecMajorAlloc.major_fl_above_zero
            (MH.single_chunk_major_heap res.major_out) res.fp_out fuel);
  assert (SpecMajorAlloc.major_fl_blocks_fit
            (MH.single_chunk_major_heap res.major_out) res.fp_out fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            (MH.single_chunk_major_heap res.major_out) res.fp_out fuel = true);
  MH.single_chunk_major_heap_wf res.major_out;
  GenInv.chunked_major_alloc_shape_intro
    (MH.single_chunk_major_heap res.major_out) res.fp_out fuel
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let promote_object_head_split_preserves_remaining_head_wosize_single_chunk
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
  let fuel = SpecAlloc.alloc_search_fuel in
  let mh = MH.single_chunk_major_heap major in
  assert (SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2);
  promote_object_head_split_preserves_chunked_alloc_shape_single_chunk
    minor major obj fp wosize;
  GenInv.chunked_major_alloc_shape_elim mh fp fuel;
  let alloc_res = SpecAlloc.alloc_spec major fp wosize in
  let res = promote_object minor major obj fp wosize in
  assert (res.new_addr == fp);
  assert (res.fp_out == alloc_res.fp_out);
  assert (res.fp_out <> 0UL);
  SpecMajorAlloc.major_alloc_spec_with_fuel_single_chunk_compat
    major fp wosize fuel;
  assert (SpecAlloc.alloc_spec major fp wosize ==
          SpecAlloc.alloc_spec_with_fuel major fp wosize fuel);
  let ma =
    SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
  assert (ma.major_alloc_out == MH.single_chunk_major_heap alloc_res.heap_out);
  assert (ma.major_fp_out == alloc_res.fp_out);
  SpecMajorAlloc.major_alloc_head_split_preserves_head_wosize
    mh fp wosize fuel remaining;
  assert (SpecMajorAlloc.major_fl_head_wosize
            (MH.single_chunk_major_heap alloc_res.heap_out)
            alloc_res.fp_out >= remaining);
  SpecMajorAllocSplitShape.major_alloc_head_split_remainder_avoids_allocated_head
    mh fp wosize fuel;
  assert (SpecMajorAlloc.major_fl_chain_avoids
            (MH.single_chunk_major_heap alloc_res.heap_out)
            alloc_res.fp_out (fp <: obj_addr) fuel = true);
  SpecMajorAllocSplitShape.major_alloc_head_split_preserves_alloc_shape
    mh fp wosize fuel;
  assert (SpecMajorAlloc.major_fl_valid
            (MH.single_chunk_major_heap alloc_res.heap_out)
            alloc_res.fp_out fuel);
  assert (SpecMajorAlloc.major_fl_above_zero
            (MH.single_chunk_major_heap alloc_res.heap_out)
            alloc_res.fp_out fuel);
  assert (SpecMajorAlloc.major_fl_blocks_fit
            (MH.single_chunk_major_heap alloc_res.heap_out)
            alloc_res.fp_out fuel);
  SpecMajorAlloc.major_fl_above_zero_current
    (MH.single_chunk_major_heap alloc_res.heap_out) alloc_res.fp_out fuel;
  assert (U64.v alloc_res.fp_out >= U64.v zero_addr + U64.v mword);
  assert (U64.v alloc_res.fp_out >= U64.v mword);
  assert (U64.v alloc_res.fp_out < heap_size);
  assert (U64.v alloc_res.fp_out % U64.v mword == 0);
  SpecMajorAlloc.major_fl_chain_avoids_head_ne
    (MH.single_chunk_major_heap alloc_res.heap_out)
    alloc_res.fp_out (fp <: obj_addr) fuel;
  let rem : obj_addr = alloc_res.fp_out in
  assert (rem <> (fp <: obj_addr));
  let mem_goal = Seq.mem rem (objects zero_addr alloc_res.heap_out) in
  let prove_mem (new_fp: obj_addr)
    : Lemma
        (requires new_fp == ma.major_fp_out /\
                  Seq.mem new_fp (MH.major_objects ma.major_alloc_out))
        (ensures mem_goal)
    =
    assert (new_fp == rem);
    MH.single_chunk_major_objects_compat alloc_res.heap_out;
    assert (Seq.mem new_fp (objects zero_addr alloc_res.heap_out))
  in
  FStar.Classical.exists_elim mem_goal #obj_addr
    #(fun new_fp ->
        new_fp == ma.major_fp_out /\
        Seq.mem new_fp (MH.major_objects ma.major_alloc_out))
    ()
    (fun new_fp -> FStar.Classical.move_requires prove_mem new_fp);
  promote_object_head_split_frame_header_from_alloc_single_chunk
    minor major obj fp wosize rem;
  GenInv.chunked_major_alloc_shape_elim
    (MH.single_chunk_major_heap res.major_out) res.fp_out fuel;
  SpecMajorAlloc.major_fl_head_wosize_current
    (MH.single_chunk_major_heap alloc_res.heap_out) alloc_res.fp_out fuel;
  SpecMajorAlloc.major_fl_head_wosize_current
    (MH.single_chunk_major_heap res.major_out) res.fp_out fuel;
  let rem_hd = hd_address rem in
  hd_address_bounds rem;
  hd_address_spec rem;
  assert (U64.v rem >= U64.v zero_addr + U64.v mword);
  assert (U64.v rem_hd == U64.v rem - U64.v mword);
  assert (U64.v rem_hd >= U64.v zero_addr);
  assert (U64.v rem_hd + U64.v mword <= heap_size);
  MH.single_chunk_read_word_compat alloc_res.heap_out rem_hd;
  MH.single_chunk_read_word_compat res.major_out rem_hd;
  assert (read_word res.major_out rem_hd ==
          read_word alloc_res.heap_out rem_hd);
  assert (MH.read_word_in_major
            (MH.single_chunk_major_heap res.major_out) rem_hd ==
          MH.read_word_in_major
            (MH.single_chunk_major_heap alloc_res.heap_out) rem_hd)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let cheney_forward_one_split_ready_single_chunk
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : GTot prop =
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
        minor_wosize minor parent + 2))

let cheney_forward_one_budget_ready_single_chunk
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (remaining: nat)
  : GTot prop =
  remaining > 0 /\
  SpecMajorAlloc.major_fl_head_wosize
    (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >= remaining /\
  (Seq.mem addr (minor_objects minor) /\
   cs.cs_fwd addr = 0UL /\
   ~(is_infix_in_minor minor addr) /\
   minor_wosize minor addr > 0 ==>
     cs.cs_fp <> 0UL /\
     SpecMajorAlloc.major_fl_head_wosize
       (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
     minor_wosize minor addr + 1 + remaining) /\
  (cs.cs_fwd addr = 0UL /\
   is_infix_in_minor minor addr ==>
     (let parent = infix_parent minor addr in
      Seq.mem parent (minor_objects minor) /\
      cs.cs_fwd parent = 0UL /\
      minor_wosize minor parent > 0 ==>
        cs.cs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
        minor_wosize minor parent + 1 + remaining))

let cheney_forward_one_split_demand
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : GTot nat =
  if cs.cs_fwd addr <> 0UL then 0
  else if is_infix_in_minor minor addr then
    let parent = infix_parent minor addr in
    if Seq.mem parent (minor_objects minor) &&
       cs.cs_fwd parent = 0UL &&
       minor_wosize minor parent > 0
    then SpecMajorAllocMultiAlloc.request_split_demand
          (minor_wosize minor parent)
    else 0
  else if Seq.mem addr (minor_objects minor) &&
         minor_wosize minor addr > 0
  then SpecMajorAllocMultiAlloc.request_split_demand
        (minor_wosize minor addr)
  else 0

let cheney_forward_one_budget_ready_from_split_demand_single_chunk
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (remaining: nat)
  : Lemma
      (requires remaining > 0 /\
               SpecMajorAlloc.major_fl_head_wosize
                 (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
               cheney_forward_one_split_demand minor cs addr + remaining)
      (ensures
        cheney_forward_one_budget_ready_single_chunk
         minor cs addr remaining)
  =
  let mh = MH.single_chunk_major_heap cs.cs_major in
  let head = SpecMajorAlloc.major_fl_head_wosize mh cs.cs_fp in
  assert (head >= remaining);
  if Seq.mem addr (minor_objects minor) &&
     cs.cs_fwd addr = 0UL &&
     not (is_infix_in_minor minor addr) &&
     minor_wosize minor addr > 0
  then begin
    let wz = minor_wosize minor addr in
    SpecMajorAllocMultiAlloc.request_split_demand_positive_identity wz;
    assert (cheney_forward_one_split_demand minor cs addr ==
           SpecMajorAllocMultiAlloc.request_split_demand wz);
    assert (SpecMajorAllocMultiAlloc.request_split_demand wz == wz + 1);
    assert (head >= wz + 1 + remaining);
    assert (cs.cs_fp <> 0UL)
  end;
  assert (Seq.mem addr (minor_objects minor) /\
         cs.cs_fwd addr = 0UL /\
         ~(is_infix_in_minor minor addr) /\
         minor_wosize minor addr > 0 ==>
           cs.cs_fp <> 0UL /\
           SpecMajorAlloc.major_fl_head_wosize
             (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
           minor_wosize minor addr + 1 + remaining);
  if cs.cs_fwd addr = 0UL && is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    if Seq.mem parent (minor_objects minor) &&
       cs.cs_fwd parent = 0UL &&
       minor_wosize minor parent > 0
    then begin
      let wz = minor_wosize minor parent in
      SpecMajorAllocMultiAlloc.request_split_demand_positive_identity wz;
      assert (cheney_forward_one_split_demand minor cs addr ==
             SpecMajorAllocMultiAlloc.request_split_demand wz);
      assert (SpecMajorAllocMultiAlloc.request_split_demand wz == wz + 1);
      assert (head >= wz + 1 + remaining);
      assert (cs.cs_fp <> 0UL)
    end
  end;
  assert (cs.cs_fwd addr = 0UL /\
         is_infix_in_minor minor addr ==>
           (let parent = infix_parent minor addr in
            Seq.mem parent (minor_objects minor) /\
            cs.cs_fwd parent = 0UL /\
            minor_wosize minor parent > 0 ==>
              cs.cs_fp <> 0UL /\
              SpecMajorAlloc.major_fl_head_wosize
                (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
              minor_wosize minor parent + 1 + remaining))

let cheney_forward_one_split_ready_from_minor_demand_single_chunk
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires minor_wf minor /\
               cs.cs_fp <> 0UL /\
               SpecMajorAlloc.major_fl_head_wosize
                 (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
               PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        cheney_forward_one_split_ready_single_chunk minor cs addr)
  =
  let mh = MH.single_chunk_major_heap cs.cs_major in
  let head = SpecMajorAlloc.major_fl_head_wosize mh cs.cs_fp in
  if Seq.mem addr (minor_objects minor) &&
     cs.cs_fwd addr = 0UL &&
     not (is_infix_in_minor minor addr) &&
     minor_wosize minor addr > 0
  then begin
    let wz = minor_wosize minor addr in
    PromotionDemand.minor_promotion_object_split_demand_bound minor addr;
    SpecMajorAllocMultiAlloc.request_split_demand_positive_identity wz;
    assert (SpecMajorAllocMultiAlloc.request_split_demand wz == wz + 1);
    assert (wz + 1 <= PromotionDemand.minor_promotion_demand minor);
    assert (head >= wz + 2)
  end;
  assert (Seq.mem addr (minor_objects minor) /\
         cs.cs_fwd addr = 0UL /\
         ~(is_infix_in_minor minor addr) /\
         minor_wosize minor addr > 0 ==>
           cs.cs_fp <> 0UL /\
           SpecMajorAlloc.major_fl_head_wosize
             (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
           minor_wosize minor addr + 2);
  if cs.cs_fwd addr = 0UL && is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    if Seq.mem parent (minor_objects minor) &&
       cs.cs_fwd parent = 0UL &&
       minor_wosize minor parent > 0
    then begin
      let wz = minor_wosize minor parent in
      PromotionDemand.minor_promotion_object_split_demand_bound minor parent;
      SpecMajorAllocMultiAlloc.request_split_demand_positive_identity wz;
      assert (SpecMajorAllocMultiAlloc.request_split_demand wz == wz + 1);
      assert (wz + 1 <= PromotionDemand.minor_promotion_demand minor);
      assert (head >= wz + 2)
    end
  end;
  assert (cs.cs_fwd addr = 0UL /\
         is_infix_in_minor minor addr ==>
           (let parent = infix_parent minor addr in
            Seq.mem parent (minor_objects minor) /\
            cs.cs_fwd parent = 0UL /\
            minor_wosize minor parent > 0 ==>
              cs.cs_fp <> 0UL /\
              SpecMajorAlloc.major_fl_head_wosize
                (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
              minor_wosize minor parent + 2))

private let cheney_forward_normal_head_split_preserves_chunked_alloc_shape_single_chunk
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
                 minor_wosize minor addr > 0 ==>
                   cs.cs_fp <> 0UL /\
                   SpecMajorAlloc.major_fl_head_wosize
                     (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                   minor_wosize minor addr + 2))
      (ensures
        (let cs' = cheney_forward_normal minor cs addr in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then
    cheney_forward_normal_noop minor cs addr
  else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then
      cheney_forward_normal_noop_wz0 minor cs addr
    else begin
      assert (wz > 0);
      assert (cs.cs_fp <> 0UL);
      assert (SpecMajorAlloc.major_fl_head_wosize
                (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
              wz + 2);
      promote_object_head_split_preserves_chunked_alloc_shape_single_chunk
        minor cs.cs_major addr cs.cs_fp wz;
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      assert (res.new_addr <> 0UL);
      cheney_forward_normal_success minor cs addr
    end
  end

let cheney_forward_one_head_split_preserves_chunked_alloc_shape_single_chunk
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
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    cheney_forward_normal_head_split_preserves_chunked_alloc_shape_single_chunk
      minor cs parent;
    let cs' = cheney_forward_normal minor cs parent in
    assert (GenInv.chunked_major_alloc_shape
              (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
              SpecAlloc.alloc_search_fuel);
    assert (SpecMajorAlloc.major_fl_chain_terminates
              (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
              SpecAlloc.alloc_search_fuel = true);
    if cs'.cs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then
      cheney_forward_one_infix_guard_pass minor cs addr
    else
      cheney_forward_one_infix_guard_fail minor cs addr
  end else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_head_split_preserves_chunked_alloc_shape_single_chunk
      minor cs addr
  end

private let cheney_forward_normal_head_split_preserves_remaining_head_wosize_single_chunk
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
                remaining > 0 /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                remaining /\
                (Seq.mem addr (minor_objects minor) /\
                 cs.cs_fwd addr = 0UL /\
                 minor_wosize minor addr > 0 ==>
                   cs.cs_fp <> 0UL /\
                   SpecMajorAlloc.major_fl_head_wosize
                     (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                   minor_wosize minor addr + 1 + remaining))
      (ensures
        (let cs' = cheney_forward_normal minor cs addr in
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
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then
    cheney_forward_normal_noop minor cs addr
  else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then
      cheney_forward_normal_noop_wz0 minor cs addr
    else begin
      assert (wz > 0);
      assert (cs.cs_fp <> 0UL);
      assert (SpecMajorAlloc.major_fl_head_wosize
                (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
              wz + 1 + remaining);
      assert (SpecMajorAlloc.major_fl_head_wosize
                (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
              wz + 2);
      promote_object_head_split_preserves_chunked_alloc_shape_single_chunk
        minor cs.cs_major addr cs.cs_fp wz;
      promote_object_head_split_preserves_remaining_head_wosize_single_chunk
        minor cs.cs_major addr cs.cs_fp wz remaining;
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      assert (res.new_addr <> 0UL);
      cheney_forward_normal_success minor cs addr
    end
  end

let cheney_forward_one_head_split_preserves_remaining_head_wosize_single_chunk
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
  =
  assert (remaining > 0);
  assert (SpecMajorAlloc.major_fl_head_wosize
            (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
          remaining);
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    cheney_forward_normal_head_split_preserves_remaining_head_wosize_single_chunk
      minor cs parent remaining;
    let cs' = cheney_forward_normal minor cs parent in
    assert (GenInv.chunked_major_alloc_shape
              (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
              SpecAlloc.alloc_search_fuel);
    assert (SpecMajorAlloc.major_fl_chain_terminates
              (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
              SpecAlloc.alloc_search_fuel = true);
    assert (SpecMajorAlloc.major_fl_head_wosize
              (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
            remaining);
    if cs'.cs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then
      cheney_forward_one_infix_guard_pass minor cs addr
    else
      cheney_forward_one_infix_guard_fail minor cs addr
  end else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_head_split_preserves_remaining_head_wosize_single_chunk
      minor cs addr remaining
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let rec cheney_forward_roots_split_ready_single_chunk
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : GTot prop
  (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then True
  else
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_split_ready_single_chunk minor cs r /\
    cheney_forward_roots_split_ready_single_chunk
      minor cs' roots (idx + 1)

let rec cheney_forward_roots_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma
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
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots idx
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    assert (cheney_forward_one_split_ready_single_chunk minor cs r);
    assert (cheney_forward_roots_split_ready_single_chunk
              minor cs' roots (idx + 1));
    cheney_forward_one_head_split_preserves_chunked_alloc_shape_single_chunk
      minor cs r;
    cheney_forward_roots_head_split_preserves_chunked_alloc_shape_single_chunk
      minor cs' roots (idx + 1)
  end

let rec cheney_forward_roots_budget_ready_single_chunk
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  (remaining: nat)
  : GTot prop
  (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    remaining > 0 /\
    SpecMajorAlloc.major_fl_head_wosize
      (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >= remaining
  else
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_budget_ready_single_chunk minor cs r remaining /\
    cheney_forward_roots_budget_ready_single_chunk
      minor cs' roots (idx + 1) remaining

let rec cheney_forward_roots_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  (remaining: nat)
  : Lemma
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
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots idx
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    assert (cheney_forward_one_budget_ready_single_chunk
              minor cs r remaining);
    assert (cheney_forward_roots_budget_ready_single_chunk
              minor cs' roots (idx + 1) remaining);
    cheney_forward_one_head_split_preserves_remaining_head_wosize_single_chunk
      minor cs r remaining;
    cheney_forward_roots_head_split_preserves_remaining_head_wosize_single_chunk
      minor cs' roots (idx + 1) remaining
  end

let rec cheney_forward_roots_split_demand
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : GTot nat
  (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then 0
  else
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_split_demand minor cs r +
    cheney_forward_roots_split_demand minor cs' roots (idx + 1)

let rec cheney_forward_roots_budget_ready_from_split_demand_single_chunk
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
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
                cheney_forward_roots_split_demand minor cs roots idx + remaining)
      (ensures
        cheney_forward_roots_budget_ready_single_chunk
          minor cs roots idx remaining)
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    ()
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    let step_demand = cheney_forward_one_split_demand minor cs r in
    let tail_demand =
      cheney_forward_roots_split_demand minor cs' roots (idx + 1) in
    let step_remaining = tail_demand + remaining in
    assert (step_remaining > 0);
    assert (cheney_forward_roots_split_demand minor cs roots idx ==
            step_demand + tail_demand);
    assert (SpecMajorAlloc.major_fl_head_wosize
              (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
            step_demand + step_remaining);
    cheney_forward_one_budget_ready_from_split_demand_single_chunk
      minor cs r step_remaining;
    cheney_forward_one_head_split_preserves_remaining_head_wosize_single_chunk
      minor cs r step_remaining;
    assert (GenInv.chunked_major_alloc_shape
              (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
              SpecAlloc.alloc_search_fuel);
    assert (SpecMajorAlloc.major_fl_chain_terminates
              (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
              SpecAlloc.alloc_search_fuel = true);
    assert (SpecMajorAlloc.major_fl_head_wosize
              (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
            tail_demand + remaining);
    cheney_forward_roots_budget_ready_from_split_demand_single_chunk
      minor cs' roots (idx + 1) remaining;
    assert (SpecMajorAlloc.major_fl_head_wosize
              (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
            step_demand + remaining);
    cheney_forward_one_budget_ready_from_split_demand_single_chunk
      minor cs r remaining;
    assert (cheney_forward_one_budget_ready_single_chunk
              minor cs r remaining);
    assert (cheney_forward_roots_budget_ready_single_chunk
              minor cs' roots (idx + 1) remaining)
  end

let rec cheney_forward_fields_split_ready_single_chunk
  (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat)
  : GTot prop
  (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then True
  else
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_one_split_ready_single_chunk minor cs field_val /\
    cheney_forward_fields_split_ready_single_chunk
      minor cs' parent (idx + 1) wosize

let rec cheney_forward_fields_head_split_preserves_chunked_alloc_shape_single_chunk
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
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    cheney_forward_fields_base minor cs parent idx wosize
  else begin
    cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    assert (cheney_forward_one_split_ready_single_chunk minor cs field_val);
    assert (cheney_forward_fields_split_ready_single_chunk
              minor cs' parent (idx + 1) wosize);
    cheney_forward_one_head_split_preserves_chunked_alloc_shape_single_chunk
      minor cs field_val;
    cheney_forward_fields_head_split_preserves_chunked_alloc_shape_single_chunk
      minor cs' parent (idx + 1) wosize
  end

let rec cheney_forward_fields_budget_ready_single_chunk
  (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (remaining: nat)
  : GTot prop
  (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    remaining > 0 /\
    SpecMajorAlloc.major_fl_head_wosize
      (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >= remaining
  else
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_one_budget_ready_single_chunk minor cs field_val remaining /\
    cheney_forward_fields_budget_ready_single_chunk
      minor cs' parent (idx + 1) wosize remaining

let rec cheney_forward_fields_head_split_preserves_remaining_head_wosize_single_chunk
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
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    cheney_forward_fields_base minor cs parent idx wosize
  else begin
    cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    assert (cheney_forward_one_budget_ready_single_chunk
              minor cs field_val remaining);
    assert (cheney_forward_fields_budget_ready_single_chunk
              minor cs' parent (idx + 1) wosize remaining);
    cheney_forward_one_head_split_preserves_remaining_head_wosize_single_chunk
      minor cs field_val remaining;
    cheney_forward_fields_head_split_preserves_remaining_head_wosize_single_chunk
      minor cs' parent (idx + 1) wosize remaining
  end

let rec cheney_forward_fields_split_demand
  (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat)
  : GTot nat
  (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then 0
  else
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_one_split_demand minor cs field_val +
    cheney_forward_fields_split_demand
      minor cs' parent (idx + 1) wosize

let rec cheney_forward_fields_budget_ready_from_split_demand_single_chunk
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
                cheney_forward_fields_split_demand
                  minor cs parent idx wosize + remaining)
      (ensures
        cheney_forward_fields_budget_ready_single_chunk
          minor cs parent idx wosize remaining)
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    ()
  else begin
    cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    let step_demand = cheney_forward_one_split_demand minor cs field_val in
    let tail_demand =
      cheney_forward_fields_split_demand
        minor cs' parent (idx + 1) wosize in
    let step_remaining = tail_demand + remaining in
    assert (step_remaining > 0);
    assert (cheney_forward_fields_split_demand minor cs parent idx wosize ==
            step_demand + tail_demand);
    assert (SpecMajorAlloc.major_fl_head_wosize
              (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
            step_demand + step_remaining);
    cheney_forward_one_budget_ready_from_split_demand_single_chunk
      minor cs field_val step_remaining;
    cheney_forward_one_head_split_preserves_remaining_head_wosize_single_chunk
      minor cs field_val step_remaining;
    assert (GenInv.chunked_major_alloc_shape
              (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
              SpecAlloc.alloc_search_fuel);
    assert (SpecMajorAlloc.major_fl_chain_terminates
              (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
              SpecAlloc.alloc_search_fuel = true);
    assert (SpecMajorAlloc.major_fl_head_wosize
              (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
            tail_demand + remaining);
    cheney_forward_fields_budget_ready_from_split_demand_single_chunk
      minor cs' parent (idx + 1) wosize remaining;
    assert (SpecMajorAlloc.major_fl_head_wosize
              (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
            step_demand + remaining);
    cheney_forward_one_budget_ready_from_split_demand_single_chunk
      minor cs field_val remaining;
    assert (cheney_forward_one_budget_ready_single_chunk
              minor cs field_val remaining);
    assert (cheney_forward_fields_budget_ready_single_chunk
              minor cs' parent (idx + 1) wosize remaining)
  end

let rec cheney_scan_split_ready_single_chunk
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : GTot prop
  (decreases fuel)
  =
  if fuel > 0 then
    if scan >= Seq.length cs.cs_queue then True
    else
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' = cheney_forward_fields minor cs obj 0 wz in
      cheney_forward_fields_split_ready_single_chunk minor cs obj 0 wz /\
      cheney_scan_split_ready_single_chunk minor cs' (scan + 1) fuel'
  else True

let rec cheney_scan_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma
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
      (decreases fuel)
  =
  if fuel > 0 then
    if scan >= Seq.length cs.cs_queue then
      cheney_scan_base minor cs scan fuel
    else begin
      assert (scan < Seq.length cs.cs_queue);
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      cheney_scan_step minor cs scan fuel;
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' = cheney_forward_fields minor cs obj 0 wz in
      assert (cheney_forward_fields_split_ready_single_chunk
                minor cs obj 0 wz);
      assert (cheney_scan_split_ready_single_chunk
                minor cs' (scan + 1) fuel');
      cheney_forward_fields_head_split_preserves_chunked_alloc_shape_single_chunk
        minor cs obj 0 wz;
      cheney_scan_head_split_preserves_chunked_alloc_shape_single_chunk
        minor cs' (scan + 1) fuel'
    end
  else begin
    assert (fuel = 0);
    cheney_scan_base minor cs scan fuel
  end

let rec cheney_scan_budget_ready_single_chunk
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  (remaining: nat)
  : GTot prop
  (decreases fuel)
  =
  if fuel > 0 then
    if scan >= Seq.length cs.cs_queue then
      remaining > 0 /\
      SpecMajorAlloc.major_fl_head_wosize
        (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >= remaining
    else
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' = cheney_forward_fields minor cs obj 0 wz in
      cheney_forward_fields_budget_ready_single_chunk
        minor cs obj 0 wz remaining /\
      cheney_scan_budget_ready_single_chunk
        minor cs' (scan + 1) fuel' remaining
  else
    remaining > 0 /\
    SpecMajorAlloc.major_fl_head_wosize
      (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >= remaining

let rec cheney_scan_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  (remaining: nat)
  : Lemma
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
      (decreases fuel)
  =
  if fuel > 0 then
    if scan >= Seq.length cs.cs_queue then
      cheney_scan_base minor cs scan fuel
    else begin
      assert (scan < Seq.length cs.cs_queue);
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      cheney_scan_step minor cs scan fuel;
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' = cheney_forward_fields minor cs obj 0 wz in
      assert (cheney_forward_fields_budget_ready_single_chunk
                minor cs obj 0 wz remaining);
      assert (cheney_scan_budget_ready_single_chunk
                minor cs' (scan + 1) fuel' remaining);
      cheney_forward_fields_head_split_preserves_remaining_head_wosize_single_chunk
        minor cs obj 0 wz remaining;
      cheney_scan_head_split_preserves_remaining_head_wosize_single_chunk
        minor cs' (scan + 1) fuel' remaining
    end
  else begin
    assert (fuel = 0);
    cheney_scan_base minor cs scan fuel
  end

let rec cheney_scan_split_demand
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : GTot nat
  (decreases fuel)
  =
  if fuel > 0 then
    if scan >= Seq.length cs.cs_queue then 0
    else
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' = cheney_forward_fields minor cs obj 0 wz in
      cheney_forward_fields_split_demand minor cs obj 0 wz +
      cheney_scan_split_demand minor cs' (scan + 1) fuel'
  else 0

let rec cheney_scan_budget_ready_from_split_demand_single_chunk
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
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
                cheney_scan_split_demand minor cs scan fuel + remaining)
      (ensures
        cheney_scan_budget_ready_single_chunk
          minor cs scan fuel remaining)
      (decreases fuel)
  =
  if fuel > 0 then
    if scan >= Seq.length cs.cs_queue then
      ()
    else begin
      assert (scan < Seq.length cs.cs_queue);
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      cheney_scan_step minor cs scan fuel;
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' = cheney_forward_fields minor cs obj 0 wz in
      let step_demand =
        cheney_forward_fields_split_demand minor cs obj 0 wz in
      let tail_demand =
        cheney_scan_split_demand minor cs' (scan + 1) fuel' in
      let step_remaining = tail_demand + remaining in
      assert (step_remaining > 0);
      assert (cheney_scan_split_demand minor cs scan fuel ==
              step_demand + tail_demand);
      assert (SpecMajorAlloc.major_fl_head_wosize
                (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
              step_demand + step_remaining);
      cheney_forward_fields_budget_ready_from_split_demand_single_chunk
        minor cs obj 0 wz step_remaining;
      cheney_forward_fields_head_split_preserves_remaining_head_wosize_single_chunk
        minor cs obj 0 wz step_remaining;
      assert (GenInv.chunked_major_alloc_shape
                (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
                SpecAlloc.alloc_search_fuel);
      assert (SpecMajorAlloc.major_fl_chain_terminates
                (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
                SpecAlloc.alloc_search_fuel = true);
      assert (SpecMajorAlloc.major_fl_head_wosize
                (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
              tail_demand + remaining);
      cheney_scan_budget_ready_from_split_demand_single_chunk
        minor cs' (scan + 1) fuel' remaining;
      assert (SpecMajorAlloc.major_fl_head_wosize
                (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
              step_demand + remaining);
      cheney_forward_fields_budget_ready_from_split_demand_single_chunk
        minor cs obj 0 wz remaining;
      assert (cheney_forward_fields_budget_ready_single_chunk
                minor cs obj 0 wz remaining);
      assert (cheney_scan_budget_ready_single_chunk
                minor cs' (scan + 1) fuel' remaining)
    end
  else
    ()

let cheney_promote_split_ready_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : GTot prop =
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_forward_roots_split_ready_single_chunk minor cs0 roots 0 /\
  cheney_scan_split_ready_single_chunk minor cs1 0 (cheney_fuel minor)

let cheney_promote_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
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
  =
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  assert (GenInv.chunked_major_alloc_shape
            (MH.single_chunk_major_heap cs0.cs_major) cs0.cs_fp
            SpecAlloc.alloc_search_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            (MH.single_chunk_major_heap cs0.cs_major) cs0.cs_fp
            SpecAlloc.alloc_search_fuel = true);
  assert (cheney_forward_roots_split_ready_single_chunk
            minor cs0 roots 0);
  cheney_forward_roots_head_split_preserves_chunked_alloc_shape_single_chunk
    minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  assert (GenInv.chunked_major_alloc_shape
            (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp
            SpecAlloc.alloc_search_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp
            SpecAlloc.alloc_search_fuel = true);
  assert (cheney_scan_split_ready_single_chunk
            minor cs1 0 (cheney_fuel minor));
  cheney_scan_head_split_preserves_chunked_alloc_shape_single_chunk
    minor cs1 0 (cheney_fuel minor);
  let cs2 = cheney_scan minor cs1 0 (cheney_fuel minor) in
  let res = cheney_promote minor major fp roots in
  assert (res.major_final == cs2.cs_major);
  assert (res.fp_final == cs2.cs_fp)

let cheney_promote_budget_ready_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (remaining: nat)
  : GTot prop =
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_forward_roots_budget_ready_single_chunk minor cs0 roots 0 remaining /\
  cheney_scan_budget_ready_single_chunk minor cs1 0 (cheney_fuel minor) remaining

let cheney_promote_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (remaining: nat)
  : Lemma
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
  =
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  assert (GenInv.chunked_major_alloc_shape
            (MH.single_chunk_major_heap cs0.cs_major) cs0.cs_fp
            SpecAlloc.alloc_search_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            (MH.single_chunk_major_heap cs0.cs_major) cs0.cs_fp
            SpecAlloc.alloc_search_fuel = true);
  assert (cheney_forward_roots_budget_ready_single_chunk
            minor cs0 roots 0 remaining);
  cheney_forward_roots_head_split_preserves_remaining_head_wosize_single_chunk
    minor cs0 roots 0 remaining;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  assert (GenInv.chunked_major_alloc_shape
            (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp
            SpecAlloc.alloc_search_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp
            SpecAlloc.alloc_search_fuel = true);
  assert (SpecMajorAlloc.major_fl_head_wosize
            (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp >=
          remaining);
  assert (cheney_scan_budget_ready_single_chunk
            minor cs1 0 (cheney_fuel minor) remaining);
  cheney_scan_head_split_preserves_remaining_head_wosize_single_chunk
    minor cs1 0 (cheney_fuel minor) remaining;
  let cs2 = cheney_scan minor cs1 0 (cheney_fuel minor) in
  let res = cheney_promote minor major fp roots in
  assert (res.major_final == cs2.cs_major);
  assert (res.fp_final == cs2.cs_fp)

let cheney_promote_split_demand
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : GTot nat =
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_forward_roots_split_demand minor cs0 roots 0 +
  cheney_scan_split_demand minor cs1 0 (cheney_fuel minor)

let cheney_promote_budget_ready_from_split_demand_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
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
                cheney_promote_split_demand minor major fp roots + remaining)
      (ensures
        cheney_promote_budget_ready_single_chunk
          minor major fp roots remaining)
  =
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  let roots_demand = cheney_forward_roots_split_demand minor cs0 roots 0 in
  let scan_demand = cheney_scan_split_demand minor cs1 0 (cheney_fuel minor) in
  let roots_remaining = scan_demand + remaining in
  assert (roots_remaining > 0);
  assert (cheney_promote_split_demand minor major fp roots ==
          roots_demand + scan_demand);
  assert (SpecMajorAlloc.major_fl_head_wosize
            (MH.single_chunk_major_heap major) fp >=
          roots_demand + roots_remaining);
  cheney_forward_roots_budget_ready_from_split_demand_single_chunk
    minor cs0 roots 0 roots_remaining;
  cheney_forward_roots_head_split_preserves_remaining_head_wosize_single_chunk
    minor cs0 roots 0 roots_remaining;
  assert (GenInv.chunked_major_alloc_shape
            (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp
            SpecAlloc.alloc_search_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp
            SpecAlloc.alloc_search_fuel = true);
  assert (SpecMajorAlloc.major_fl_head_wosize
            (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp >=
          scan_demand + remaining);
  cheney_scan_budget_ready_from_split_demand_single_chunk
    minor cs1 0 (cheney_fuel minor) remaining;
  assert (SpecMajorAlloc.major_fl_head_wosize
            (MH.single_chunk_major_heap major) fp >=
          roots_demand + remaining);
  cheney_forward_roots_budget_ready_from_split_demand_single_chunk
    minor cs0 roots 0 remaining;
  assert (cheney_forward_roots_budget_ready_single_chunk
            minor cs0 roots 0 remaining);
  assert (cheney_scan_budget_ready_single_chunk
            minor cs1 0 (cheney_fuel minor) remaining)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_one_unforwarded_split_demand_decreases_single_chunk
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires minor_wf minor /\
                SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                cheney_unforwarded_split_demand minor cs + 1)
      (ensures
        (let cs' = cheney_forward_one minor cs addr in
         cheney_forward_one_split_demand minor cs addr +
         cheney_unforwarded_split_demand minor cs' <=
         cheney_unforwarded_split_demand minor cs))
  =
  let mh = MH.single_chunk_major_heap cs.cs_major in
  let head = SpecMajorAlloc.major_fl_head_wosize mh cs.cs_fp in
  let old_demand = cheney_unforwarded_split_demand minor cs in
  assert (head >= old_demand + 1);
  assert (head > 0);
  assert (cs.cs_fp <> 0UL);
  if cs.cs_fwd addr <> 0UL then begin
    cheney_forward_one_noop minor cs addr;
    assert (cheney_forward_one_split_demand minor cs addr == 0);
    assert (cheney_forward_one minor cs addr == cs)
  end else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    let csn = cheney_forward_normal minor cs parent in
    if Seq.mem parent (minor_objects minor) &&
       cs.cs_fwd parent = 0UL &&
       minor_wosize minor parent > 0
    then begin
      let wz = minor_wosize minor parent in
      let req = SpecMajorAllocMultiAlloc.request_split_demand wz in
      cheney_unforwarded_split_demand_object_bound minor cs parent;
      SpecMajorAllocMultiAlloc.request_split_demand_positive_identity wz;
      assert (req == wz + 1);
      assert (req <= old_demand);
      assert (head >= wz + 2);
      promote_object_head_split_preserves_chunked_alloc_shape_single_chunk
        minor cs.cs_major parent cs.cs_fp wz;
      let res = promote_object minor cs.cs_major parent cs.cs_fp wz in
      assert (res.new_addr <> 0UL);
      cheney_forward_normal_success minor cs parent;
      assert (csn.cs_fwd == extend_forwarding cs.cs_fwd parent res.new_addr);
      cheney_unforwarded_split_demand_state_extend_decrease
        minor cs csn parent res.new_addr;
      assert (req +
              cheney_unforwarded_split_demand minor csn <=
              old_demand);
      if csn.cs_fwd parent <> 0UL &&
         U64.v addr >= U64.v parent &&
         U64.v (csn.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
      then begin
        let sum =
          U64.uint_to_t
            (U64.v (csn.cs_fwd parent) + (U64.v addr - U64.v parent)) in
        cheney_forward_one_infix_guard_pass minor cs addr;
        assert ((cheney_forward_one minor cs addr).cs_fwd ==
                extend_forwarding csn.cs_fwd addr sum);
        cheney_unforwarded_split_demand_state_extend_infix_monotone
          minor csn (cheney_forward_one minor cs addr) addr sum;
        assert (cheney_unforwarded_split_demand
                  minor (cheney_forward_one minor cs addr) <=
                cheney_unforwarded_split_demand minor csn)
      end else begin
        cheney_forward_one_infix_guard_fail minor cs addr;
        assert (cheney_forward_one minor cs addr == csn);
        assert (cheney_unforwarded_split_demand
                  minor (cheney_forward_one minor cs addr) <=
                cheney_unforwarded_split_demand minor csn)
      end;
      assert (req +
              cheney_unforwarded_split_demand
                minor (cheney_forward_one minor cs addr) <=
              old_demand);
      assert (cheney_forward_one_split_demand minor cs addr == req)
    end else begin
      if not (Seq.mem parent (minor_objects minor)) then
        cheney_forward_normal_noop minor cs parent
      else if cs.cs_fwd parent <> 0UL then
        cheney_forward_normal_noop minor cs parent
      else begin
        assert (minor_wosize minor parent = 0);
        cheney_forward_normal_noop_wz0 minor cs parent
      end;
      assert (csn == cs);
      if csn.cs_fwd parent <> 0UL &&
         U64.v addr >= U64.v parent &&
         U64.v (csn.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
      then begin
        let sum =
          U64.uint_to_t
            (U64.v (csn.cs_fwd parent) + (U64.v addr - U64.v parent)) in
        cheney_forward_one_infix_guard_pass minor cs addr;
        assert ((cheney_forward_one minor cs addr).cs_fwd ==
                extend_forwarding cs.cs_fwd addr sum);
        cheney_unforwarded_split_demand_state_extend_infix_monotone
          minor cs (cheney_forward_one minor cs addr) addr sum;
        assert (cheney_unforwarded_split_demand
                  minor (cheney_forward_one minor cs addr) <=
                old_demand)
      end else begin
        cheney_forward_one_infix_guard_fail minor cs addr;
        assert (cheney_forward_one minor cs addr == cs);
        assert (cheney_unforwarded_split_demand
                  minor (cheney_forward_one minor cs addr) <=
                old_demand)
      end;
      assert (cheney_forward_one_split_demand minor cs addr == 0)
    end
  end else begin
    cheney_forward_one_normal minor cs addr;
    if not (Seq.mem addr (minor_objects minor)) then begin
      cheney_forward_normal_noop minor cs addr;
      assert (cheney_forward_one minor cs addr == cs);
      assert (cheney_forward_one_split_demand minor cs addr == 0)
    end else begin
      let wz = minor_wosize minor addr in
      if wz = 0 then begin
        cheney_forward_normal_noop_wz0 minor cs addr;
        assert (cheney_forward_one minor cs addr == cs);
        assert (cheney_forward_one_split_demand minor cs addr == 0)
      end else begin
        assert (wz > 0);
        let req = SpecMajorAllocMultiAlloc.request_split_demand wz in
        cheney_unforwarded_split_demand_object_bound minor cs addr;
        SpecMajorAllocMultiAlloc.request_split_demand_positive_identity wz;
        assert (req == wz + 1);
        assert (req <= old_demand);
        assert (head >= wz + 2);
        promote_object_head_split_preserves_chunked_alloc_shape_single_chunk
          minor cs.cs_major addr cs.cs_fp wz;
        let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
        assert (res.new_addr <> 0UL);
        cheney_forward_normal_success minor cs addr;
        assert ((cheney_forward_one minor cs addr).cs_fwd ==
                extend_forwarding cs.cs_fwd addr res.new_addr);
        cheney_unforwarded_split_demand_state_extend_decrease
          minor cs (cheney_forward_one minor cs addr) addr res.new_addr;
        assert (req +
                cheney_unforwarded_split_demand
                  minor (cheney_forward_one minor cs addr) <=
                old_demand);
        assert (cheney_forward_one_split_demand minor cs addr == req)
      end
    end
  end

private let cheney_forward_one_budget_ready_from_unforwarded_single_chunk
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires minor_wf minor /\
                SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                cheney_unforwarded_split_demand minor cs + 1)
      (ensures
        (let cs' = cheney_forward_one minor cs addr in
         cheney_forward_one_budget_ready_single_chunk minor cs addr 1 /\
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
         cheney_unforwarded_split_demand minor cs' + 1))
  =
  let cs' = cheney_forward_one minor cs addr in
  let d = cheney_forward_one_split_demand minor cs addr in
  let after = cheney_unforwarded_split_demand minor cs' in
  let old_demand = cheney_unforwarded_split_demand minor cs in
  let head =
    SpecMajorAlloc.major_fl_head_wosize
      (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp in
  cheney_forward_one_unforwarded_split_demand_decreases_single_chunk
    minor cs addr;
  assert (d + after <= old_demand);
  assert (head >= d + after + 1);
  assert (head >= d + 1);
  cheney_forward_one_budget_ready_from_split_demand_single_chunk
    minor cs addr 1;
  cheney_forward_one_budget_ready_from_split_demand_single_chunk
    minor cs addr (after + 1);
  cheney_forward_one_head_split_preserves_remaining_head_wosize_single_chunk
    minor cs addr (after + 1)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
private let rec cheney_forward_roots_budget_ready_from_unforwarded_single_chunk
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma
      (requires minor_wf minor /\
                SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                cheney_unforwarded_split_demand minor cs + 1)
      (ensures
        (let cs' = cheney_forward_roots minor cs roots idx in
         cheney_forward_roots_budget_ready_single_chunk
           minor cs roots idx 1 /\
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
         cheney_unforwarded_split_demand minor cs' + 1))
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then begin
    cheney_forward_roots_base minor cs roots idx;
    assert (SpecMajorAlloc.major_fl_head_wosize
              (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >= 1)
  end else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs1 = cheney_forward_one minor cs r in
    cheney_forward_one_budget_ready_from_unforwarded_single_chunk
      minor cs r;
    assert (GenInv.chunked_major_alloc_shape
              (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp
              SpecAlloc.alloc_search_fuel);
    assert (SpecMajorAlloc.major_fl_chain_terminates
              (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp
              SpecAlloc.alloc_search_fuel = true);
    assert (SpecMajorAlloc.major_fl_head_wosize
              (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp >=
            cheney_unforwarded_split_demand minor cs1 + 1);
    cheney_forward_roots_budget_ready_from_unforwarded_single_chunk
      minor cs1 roots (idx + 1);
    assert (cheney_forward_one_budget_ready_single_chunk minor cs r 1);
    assert (cheney_forward_roots_budget_ready_single_chunk
              minor cs1 roots (idx + 1) 1)
  end

private let rec cheney_forward_fields_budget_ready_from_unforwarded_single_chunk
  (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma
      (requires minor_wf minor /\
                SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                cheney_unforwarded_split_demand minor cs + 1)
      (ensures
        (let cs' = cheney_forward_fields minor cs parent idx wosize in
         cheney_forward_fields_budget_ready_single_chunk
           minor cs parent idx wosize 1 /\
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
         cheney_unforwarded_split_demand minor cs' + 1))
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then begin
    cheney_forward_fields_base minor cs parent idx wosize;
    assert (SpecMajorAlloc.major_fl_head_wosize
              (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >= 1)
  end else begin
    cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs1 = cheney_forward_one minor cs field_val in
    cheney_forward_one_budget_ready_from_unforwarded_single_chunk
      minor cs field_val;
    assert (GenInv.chunked_major_alloc_shape
              (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp
              SpecAlloc.alloc_search_fuel);
    assert (SpecMajorAlloc.major_fl_chain_terminates
              (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp
              SpecAlloc.alloc_search_fuel = true);
    assert (SpecMajorAlloc.major_fl_head_wosize
              (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp >=
            cheney_unforwarded_split_demand minor cs1 + 1);
    cheney_forward_fields_budget_ready_from_unforwarded_single_chunk
      minor cs1 parent (idx + 1) wosize;
    assert (cheney_forward_one_budget_ready_single_chunk
              minor cs field_val 1);
    assert (cheney_forward_fields_budget_ready_single_chunk
              minor cs1 parent (idx + 1) wosize 1)
  end

private let rec cheney_scan_budget_ready_from_unforwarded_single_chunk
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma
      (requires minor_wf minor /\
                SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                cheney_unforwarded_split_demand minor cs + 1)
      (ensures
        (let cs' = cheney_scan minor cs scan fuel in
         cheney_scan_budget_ready_single_chunk minor cs scan fuel 1 /\
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
         cheney_unforwarded_split_demand minor cs' + 1))
      (decreases fuel)
  =
  if fuel > 0 then
    if scan >= Seq.length cs.cs_queue then begin
      cheney_scan_base minor cs scan fuel;
      assert (SpecMajorAlloc.major_fl_head_wosize
                (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >= 1)
    end else begin
      cheney_scan_step minor cs scan fuel;
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      let cs1 = cheney_forward_fields minor cs obj 0 wz in
      cheney_forward_fields_budget_ready_from_unforwarded_single_chunk
        minor cs obj 0 wz;
      assert (GenInv.chunked_major_alloc_shape
                (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp
                SpecAlloc.alloc_search_fuel);
      assert (SpecMajorAlloc.major_fl_chain_terminates
                (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp
                SpecAlloc.alloc_search_fuel = true);
      assert (SpecMajorAlloc.major_fl_head_wosize
                (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp >=
              cheney_unforwarded_split_demand minor cs1 + 1);
      cheney_scan_budget_ready_from_unforwarded_single_chunk
        minor cs1 (scan + 1) fuel';
      assert (cheney_forward_fields_budget_ready_single_chunk
                minor cs obj 0 wz 1);
      assert (cheney_scan_budget_ready_single_chunk
                minor cs1 (scan + 1) fuel' 1)
    end
  else begin
    cheney_scan_base minor cs scan fuel;
    assert (SpecMajorAlloc.major_fl_head_wosize
              (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >= 1)
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let cheney_promote_budget_ready_from_minor_demand_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
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
        cheney_promote_budget_ready_single_chunk
          minor major fp roots 1)
  =
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_unforwarded_split_demand_bound minor cs0;
  assert (cheney_unforwarded_split_demand minor cs0 <=
          PromotionDemand.minor_promotion_demand minor);
  assert (SpecMajorAlloc.major_fl_head_wosize
            (MH.single_chunk_major_heap major) fp >=
          cheney_unforwarded_split_demand minor cs0 + 1);
  cheney_forward_roots_budget_ready_from_unforwarded_single_chunk
    minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  assert (GenInv.chunked_major_alloc_shape
            (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp
            SpecAlloc.alloc_search_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp
            SpecAlloc.alloc_search_fuel = true);
  assert (SpecMajorAlloc.major_fl_head_wosize
            (MH.single_chunk_major_heap cs1.cs_major) cs1.cs_fp >=
          cheney_unforwarded_split_demand minor cs1 + 1);
  cheney_scan_budget_ready_from_unforwarded_single_chunk
    minor cs1 0 (cheney_fuel minor);
  assert (cheney_forward_roots_budget_ready_single_chunk
            minor cs0 roots 0 1);
  assert (cheney_scan_budget_ready_single_chunk
            minor cs1 0 (cheney_fuel minor) 1)
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let cheney_promote_budgeted_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
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
  =
  GenInv.chunked_major_alloc_shape_elim
    (MH.single_chunk_major_heap major) fp SpecAlloc.alloc_search_fuel;
  cheney_promote_budget_ready_from_minor_demand_single_chunk
    minor major fp roots;
  cheney_forwarded_dense_alloc_list_default_single_chunk_no_oom
    minor major fp roots;
  cheney_promote_head_split_preserves_remaining_head_wosize_single_chunk
    minor major fp roots 1
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let cheney_promote_after_minor_promotion_head_preflight_no_expansion_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
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
  =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  assert (needed > 0);
  GenInv.chunked_collection_heap_shape_ensure_head_capacity_with_chain
    minor (MH.single_chunk_major_heap major) fp
    SpecAlloc.alloc_search_fuel needed fresh;
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      (MH.single_chunk_major_heap major) fp
      SpecAlloc.alloc_search_fuel needed fresh in
  assert (r.capacity_major_out == MH.single_chunk_major_heap major);
  assert (r.capacity_fp_out == fp);
  assert (r.capacity_fuel_out == SpecAlloc.alloc_search_fuel);
  GenInv.chunked_collection_heap_shape_elim
    minor (MH.single_chunk_major_heap major) fp SpecAlloc.alloc_search_fuel;
  cheney_promote_budgeted_head_split_preserves_chunked_alloc_shape_single_chunk
    minor major fp roots
#pop-options

/// ---------------------------------------------------------------------------
/// Core sub-lemma: promote_object preserves no_black_objects
/// ---------------------------------------------------------------------------
///
/// Proof: alloc_spec_preserves_no_black_part1 gives no_black for the
/// post-alloc heap. copy_fields only writes body fields (within
/// [dst, dst+wz*8)), preserving all headers. So colors are unchanged,
/// and no_black carries through.

/// Helper: set_promoted_tag preserves no_black_objects.
/// The written header has color White, and all other headers are preserved.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --split_queries always"
private let set_promoted_tag_preserves_no_black
  (g: heap) (dst: obj_addr) (tag: nat{tag < 256})
  : Lemma (requires Mark.no_black_objects g /\
                    Seq.mem dst (objects zero_addr g))
          (ensures Mark.no_black_objects (set_promoted_tag g dst tag))
  = let g' = set_promoted_tag g dst tag in
    set_promoted_tag_preserves_objects g dst tag;
    set_promoted_tag_unfold g dst tag;
    let hdr = read_word g (hd_address dst) in
    getWosize_bound hdr;
    let new_hdr = makeHeader (getWosize hdr) White (U64.uint_to_t tag) in
    hd_address_spec dst;
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g'))
      (ensures ~(is_black h g'))
    = hd_address_spec h;
      if h = dst then begin
        read_write_same g (hd_address dst) new_hdr;
        makeHeader_getColor (getWosize hdr) White (U64.uint_to_t tag);
        color_of_object_spec dst g';
        is_black_iff dst g'
      end else begin
        hd_address_injective h dst;
        set_promoted_tag_read_frame g dst tag (hd_address h);
        color_of_header_eq h g g';
        is_black_iff h g;
        is_black_iff h g'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// Helper: copy_fields preserves no_black_objects when dst_fields_valid
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"
private let copy_fields_preserves_no_black
  (minor: minor_state) (g: heap) (obj: U64.t) (dst: obj_addr) (wz: nat{wz > 0})
  : Lemma (requires Mark.no_black_objects g /\
                    Seq.mem dst (objects zero_addr g) /\
                    well_formed_heap_part1 g /\
                    U64.v (wosize_of_object dst g) >= wz /\
                    dst_fields_valid dst wz)
          (ensures Mark.no_black_objects (copy_fields minor g obj dst 0 wz))
  = copy_fields_preserves_objects_aux minor g obj dst 0 wz;
    let result = copy_fields minor g obj dst 0 wz in
    assert (objects zero_addr result == objects zero_addr g);
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr result))
      (ensures ~(is_black h result))
    = assert (Seq.mem h (objects zero_addr g));
      hd_address_spec h;
      hd_address_spec dst;
      if h = dst then begin
        copy_fields_frame minor g obj dst 0 wz (hd_address h);
        color_of_header_eq h g result;
        is_black_iff h g;
        is_black_iff h result
      end else if U64.v h < U64.v dst then begin
        objects_separated zero_addr g h dst;
        copy_fields_frame minor g obj dst 0 wz (hd_address h);
        color_of_header_eq h g result;
        is_black_iff h g;
        is_black_iff h result
      end else begin
        objects_separated zero_addr g dst h;
        wosize_of_object_spec dst g;
        copy_fields_frame minor g obj dst 0 wz (hd_address h);
        color_of_header_eq h g result;
        is_black_iff h g;
        is_black_iff h result
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// Helper: zero_promote_padding preserves no_black_objects
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --split_queries always"
private let zero_promote_padding_preserves_no_black
  (g: heap) (dst: obj_addr) (wz: nat{wz > 0})
  : Lemma (requires Mark.no_black_objects g /\
                    well_formed_heap_part1 g /\
                    Seq.mem dst (objects zero_addr g))
          (ensures Mark.no_black_objects (zero_promote_padding g dst wz))
  = zero_promote_padding_preserves_objects g dst wz;
    let padded = zero_promote_padding g dst wz in
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr padded))
      (ensures ~(is_black h padded))
    = assert (Seq.mem h (objects zero_addr g));
      hd_address_spec h;
      hd_address_spec dst;
      if h = dst then begin
        // hd_address dst = dst - 8, pad at dst + wz*8: these differ since wz*8 + 8 > 0
        assert (U64.v (hd_address h) == U64.v dst - U64.v mword);
        assert (U64.v (hd_address h) <> U64.v dst + wz * U64.v mword);
        zero_promote_padding_frame g dst wz (hd_address h);
        color_of_header_eq h g padded;
        is_black_iff h g;
        is_black_iff h padded
      end else begin
        if U64.v h < U64.v dst then begin
          objects_separated zero_addr g h dst;
          zero_promote_padding_frame g dst wz (hd_address h)
        end else begin
          objects_separated zero_addr g dst h;
          wosize_of_object_spec dst g;
          let actual_wz = U64.v (wosize_of_object dst g) in
          if actual_wz <= wz then
            zero_promote_padding_noop g dst wz
          else
            zero_promote_padding_frame g dst wz (hd_address h)
        end;
        color_of_header_eq h g padded;
        is_black_iff h g;
        is_black_iff h padded
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"

private let promote_object_preserves_no_black
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects major)
          (ensures (let res = promote_object minor major obj fp wz in
                    Mark.no_black_objects res.major_out))
  =
  let alloc_res = Allocator.alloc_spec major fp wz in
  if alloc_res.obj_out = 0UL then
    promote_object_oom minor major obj fp wz
  else begin
    promote_object_success minor major obj fp wz;
    let g_alloc = alloc_res.heap_out in

    // Step 1: alloc preserves no_black
    AllocLemmas.alloc_spec_preserves_no_black_part1 major fp wz;
    assert (Mark.no_black_objects g_alloc);

    // Step 2: dst is in objects of g_alloc with sufficient wosize
    AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
    AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    let dst : obj_addr = alloc_res.obj_out in
    assert (Seq.mem dst (objects zero_addr g_alloc));
    assert (U64.v (wosize_of_object dst g_alloc) >= wz);

    // Step 3: copy_fields preserves no_black (delegated)
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    wfh_part1_obj_bound g_alloc dst;
    dst_fields_valid_from_bounds dst wz;
    copy_fields_preserves_no_black minor g_alloc obj dst wz;
    let result = copy_fields minor g_alloc obj dst 0 wz in

    // Step 4: zero_promote_padding + set_promoted_tag preserve no_black
    copy_fields_preserves_objects_aux minor g_alloc obj dst 0 wz;
    copy_fields_preserves_wfh_part1 minor g_alloc obj dst wz;
    assert (Seq.mem dst (objects zero_addr result));
    zero_promote_padding_preserves_no_black result dst wz;
    zero_promote_padding_preserves_objects result dst wz;
    zero_promote_padding_preserves_wfh_part1 result dst wz;
    let padded = zero_promote_padding result dst wz in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    set_promoted_tag_preserves_no_black padded dst tag
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_one preserves no_black_objects
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"

private let cheney_forward_one_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects cs.cs_major /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    Mark.no_black_objects cs'.cs_major))
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    // Use infix unfold lemma: result.cs_major == (forward_normal parent).cs_major
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    // Now prove cheney_forward_normal minor cs parent preserves no_black
    if not (Seq.mem parent (minor_objects minor)) || cs.cs_fwd parent <> 0UL then
      cheney_forward_normal_noop minor cs parent
    else if minor_wosize minor parent = 0 then
      cheney_forward_normal_noop_wz0 minor cs parent
    else begin
      let wz = minor_wosize minor parent in
      let res = promote_object minor cs.cs_major parent cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_normal_noop_oom minor cs parent
      else begin
        cheney_forward_normal_success minor cs parent;
        promote_object_preserves_no_black minor cs.cs_major parent cs.cs_fp wz
      end
    end
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    if not (Seq.mem addr (minor_objects minor)) then
      cheney_forward_normal_noop minor cs addr
    else if minor_wosize minor addr = 0 then
      cheney_forward_normal_noop_wz0 minor cs addr
    else begin
      let wz = minor_wosize minor addr in
      assert (wz <> 0);
      assert (wz > 0);
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then begin
        assert (minor_wosize minor addr == wz);
        assert (minor_wosize minor addr > 0);
        assert ((promote_object minor cs.cs_major addr cs.cs_fp
                  (minor_wosize minor addr)).new_addr = 0UL);
        cheney_forward_normal_noop_oom minor cs addr
      end
      else begin
        assert (minor_wosize minor addr == wz);
        assert (minor_wosize minor addr > 0);
        assert ((promote_object minor cs.cs_major addr cs.cs_fp
                  (minor_wosize minor addr)).new_addr <> 0UL);
        cheney_forward_normal_success minor cs addr;
        promote_object_preserves_no_black minor cs.cs_major addr cs.cs_fp wz
      end
    end
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_fields preserves no_black_objects (recursive)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"

private let rec cheney_forward_fields_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects cs.cs_major /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    Mark.no_black_objects cs'.cs_major))
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    cheney_forward_fields_base minor cs parent idx wosize
  else begin
    cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_no_black minor cs field_val;
    cheney_forward_fields_preserves_no_black minor cs' parent (idx + 1) wosize
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_roots preserves wfh_part1 (needed for scan precondition)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots idx
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_roots_preserves_wfh_part1 minor cs' roots (idx + 1)
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_roots preserves no_black_objects (recursive)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects cs.cs_major /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    Mark.no_black_objects cs'.cs_major))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots idx
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_one_preserves_no_black minor cs r;
    cheney_forward_roots_preserves_no_black minor cs' roots (idx + 1)
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_scan preserves no_black_objects (recursive)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0 --split_queries always"

private let rec cheney_scan_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects cs.cs_major /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    Mark.no_black_objects cs'.cs_major))
          (decreases fuel)
  =
  if fuel = 0 then
    cheney_scan_base minor cs scan fuel
  else if scan >= Seq.length cs.cs_queue then
    cheney_scan_base minor cs scan fuel
  else begin
    cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    cheney_forward_fields_preserves_no_black minor cs obj 0 wz;
    cheney_scan_preserves_no_black minor cs' (scan + 1) (fuel - 1)
  end

#pop-options

/// ---------------------------------------------------------------------------
/// Top-level: cheney_promote preserves no_black_objects
/// ---------------------------------------------------------------------------

let cheney_promote_preserves_no_black
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects major /\
                    minor_infix_wf minor)
          (ensures (let res = cheney_promote minor major fp roots in
                    Mark.no_black_objects res.major_final))
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  // Phase 1: forward_roots preserves no_black + wfh_part1
  cheney_forward_roots_preserves_no_black minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  // Phase 2: scan preserves no_black
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_no_black minor cs1 0 (cheney_fuel minor)

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --split_queries always"
let cheney_collect_preserves_no_black
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects major /\
                    minor_infix_wf minor)
          (ensures Mark.no_black_objects
            (cheney_collect_spec minor major fp roots).mc_major)
  =
  cheney_promote_preserves_no_black minor major fp roots;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  let updated = update_major_pointers prom.major_final prom.fwd_map in
  assert ((cheney_collect_spec minor major fp roots).mc_major == updated);
  update_major_pointers_preserves_objects prom.major_final prom.fwd_map;
  let aux (obj: obj_addr)
    : Lemma (requires Seq.mem obj (objects zero_addr updated))
            (ensures ~(is_black obj updated))
    =
    assert (Seq.mem obj (objects zero_addr prom.major_final));
    update_major_pointers_preserves_header prom.major_final prom.fwd_map obj;
    color_of_header_eq obj updated prom.major_final;
    assert (~(is_black obj prom.major_final));
    assert (~(is_black obj updated))
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --split_queries always"
let cheney_collect_preserves_fp_pointer_or_zero
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires GenInv.collection_heap_shape minor major fp)
          (ensures FreeListShape.fp_pointer_or_zero
            (cheney_collect_spec minor major fp roots).mc_fp)
  =
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    cheney_promote_preserves_free_list_shape minor major fp roots;
    let prom = cheney_promote minor major fp roots in
    assert ((cheney_collect_spec minor major fp roots).mc_fp == prom.fp_final)
#pop-options


/// ---------------------------------------------------------------------------
/// Cheney promotion preserves the MajorGC color-stack precondition conjunct
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0 --split_queries always"
private let alloc_spec_preserves_gray_black_objects_on_stack_part1
  (g: heap) (fp: U64.t) (wz: nat{wz > 0}) (st: seq obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates g fp (heap_size / U64.v mword) /\
                    chain_objects_blue g fp /\
                    gray_black_objects_on_stack g st)
          (ensures gray_black_objects_on_stack (Allocator.alloc_spec g fp wz).heap_out st)
  =
  let r = Allocator.alloc_spec g fp wz in
  if r.obj_out = 0UL then begin
    AllocProps.alloc_spec_oom_unchanged g fp wz;
    assert (r.heap_out == g)
  end else begin
    AllocLemmas.alloc_spec_new_objects_blue_part1 g fp wz;
    AllocProps.alloc_spec_obj_not_blue_part1 g fp wz;
    let dst : obj_addr = r.obj_out in
    let aux (h: obj_addr)
      : Lemma (requires Seq.mem h (objects zero_addr r.heap_out) /\
                        (is_gray h r.heap_out \/ is_black h r.heap_out))
              (ensures Seq.mem h st)
      =
      if h = dst then begin
        assert (color_of_object h r.heap_out == White);
        is_gray_iff h r.heap_out;
        is_black_iff h r.heap_out;
        assert False
      end else if Seq.mem h (objects zero_addr g) then begin
        assert ((h <: U64.t) <> r.obj_out);
        AllocProps.alloc_spec_read_header_other_part1 g fp wz h;
        color_of_header_eq h g r.heap_out;
        assert (is_gray h g \/ is_black h g);
        assert (Seq.mem h st)
      end else begin
        assert (~(Seq.mem h (objects zero_addr g)));
        assert (is_blue h r.heap_out = true);
        is_blue_iff h r.heap_out;
        is_gray_iff h r.heap_out;
        is_black_iff h r.heap_out;
        assert False
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
  end
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --split_queries always"
private let set_promoted_tag_preserves_gray_black_objects_on_stack
  (g: heap) (dst: obj_addr) (tag: nat{tag < 256}) (st: seq obj_addr)
  : Lemma (requires gray_black_objects_on_stack g st /\
                    Seq.mem dst (objects zero_addr g))
          (ensures gray_black_objects_on_stack (set_promoted_tag g dst tag) st)
  =
  let g' = set_promoted_tag g dst tag in
  set_promoted_tag_preserves_objects g dst tag;
  set_promoted_tag_unfold g dst tag;
  let hdr = read_word g (hd_address dst) in
  getWosize_bound hdr;
  let new_hdr = makeHeader (getWosize hdr) White (U64.uint_to_t tag) in
  hd_address_spec dst;
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (objects zero_addr g') /\
                      (is_gray h g' \/ is_black h g'))
            (ensures Seq.mem h st)
    =
    assert (Seq.mem h (objects zero_addr g));
    hd_address_spec h;
    if h = dst then begin
      read_write_same g (hd_address dst) new_hdr;
      makeHeader_getColor (getWosize hdr) White (U64.uint_to_t tag);
      color_of_object_spec dst g';
      is_gray_iff dst g';
      is_black_iff dst g';
      assert False
    end else begin
      hd_address_injective h dst;
      set_promoted_tag_read_frame g dst tag (hd_address h);
      color_of_header_eq h g g';
      assert (is_gray h g \/ is_black h g);
      assert (Seq.mem h st)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"
private let copy_fields_preserves_gray_black_objects_on_stack
  (minor: minor_state) (g: heap) (obj: U64.t) (dst: obj_addr) (wz: nat{wz > 0})
  (st: seq obj_addr)
  : Lemma (requires gray_black_objects_on_stack g st /\
                    Seq.mem dst (objects zero_addr g) /\
                    well_formed_heap_part1 g /\
                    U64.v (wosize_of_object dst g) >= wz /\
                    dst_fields_valid dst wz)
          (ensures gray_black_objects_on_stack (copy_fields minor g obj dst 0 wz) st)
  =
  copy_fields_preserves_objects_aux minor g obj dst 0 wz;
  let result = copy_fields minor g obj dst 0 wz in
  assert (objects zero_addr result == objects zero_addr g);
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (objects zero_addr result) /\
                      (is_gray h result \/ is_black h result))
            (ensures Seq.mem h st)
    =
    assert (Seq.mem h (objects zero_addr g));
    hd_address_spec h;
    hd_address_spec dst;
    if h = dst then begin
      copy_fields_frame minor g obj dst 0 wz (hd_address h);
      color_of_header_eq h g result;
      assert (is_gray h g \/ is_black h g);
      assert (Seq.mem h st)
    end else if U64.v h < U64.v dst then begin
      objects_separated zero_addr g h dst;
      copy_fields_frame minor g obj dst 0 wz (hd_address h);
      color_of_header_eq h g result;
      assert (is_gray h g \/ is_black h g);
      assert (Seq.mem h st)
    end else begin
      objects_separated zero_addr g dst h;
      wosize_of_object_spec dst g;
      copy_fields_frame minor g obj dst 0 wz (hd_address h);
      color_of_header_eq h g result;
      assert (is_gray h g \/ is_black h g);
      assert (Seq.mem h st)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --split_queries always"
private let zero_promote_padding_preserves_gray_black_objects_on_stack
  (g: heap) (dst: obj_addr) (wz: nat{wz > 0}) (st: seq obj_addr)
  : Lemma (requires gray_black_objects_on_stack g st /\
                    well_formed_heap_part1 g /\
                    Seq.mem dst (objects zero_addr g))
          (ensures gray_black_objects_on_stack (zero_promote_padding g dst wz) st)
  =
  zero_promote_padding_preserves_objects g dst wz;
  let padded = zero_promote_padding g dst wz in
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (objects zero_addr padded) /\
                      (is_gray h padded \/ is_black h padded))
            (ensures Seq.mem h st)
    =
    assert (Seq.mem h (objects zero_addr g));
    hd_address_spec h;
    hd_address_spec dst;
    if h = dst then begin
      assert (U64.v (hd_address h) == U64.v dst - U64.v mword);
      assert (U64.v (hd_address h) <> U64.v dst + wz * U64.v mword);
      zero_promote_padding_frame g dst wz (hd_address h);
      color_of_header_eq h g padded;
      assert (is_gray h g \/ is_black h g);
      assert (Seq.mem h st)
    end else begin
      if U64.v h < U64.v dst then begin
        objects_separated zero_addr g h dst;
        zero_promote_padding_frame g dst wz (hd_address h)
      end else begin
        objects_separated zero_addr g dst h;
        wosize_of_object_spec dst g;
        let actual_wz = U64.v (wosize_of_object dst g) in
        if actual_wz <= wz then
          zero_promote_padding_noop g dst wz
        else
          zero_promote_padding_frame g dst wz (hd_address h)
      end;
      color_of_header_eq h g padded;
      assert (is_gray h g \/ is_black h g);
      assert (Seq.mem h st)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"
private let promote_object_preserves_gray_black_objects_on_stack
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (st: seq obj_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    gray_black_objects_on_stack major st)
          (ensures (let res = promote_object minor major obj fp wz in
                    gray_black_objects_on_stack res.major_out st))
  =
  let alloc_res = Allocator.alloc_spec major fp wz in
  if alloc_res.obj_out = 0UL then
    promote_object_oom minor major obj fp wz
  else begin
    promote_object_success minor major obj fp wz;
    let g_alloc = alloc_res.heap_out in
    alloc_spec_preserves_gray_black_objects_on_stack_part1 major fp wz st;

    AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
    AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    let dst : obj_addr = alloc_res.obj_out in
    assert (Seq.mem dst (objects zero_addr g_alloc));
    assert (U64.v (wosize_of_object dst g_alloc) >= wz);
    wfh_part1_obj_bound g_alloc dst;
    dst_fields_valid_from_bounds dst wz;

    copy_fields_preserves_gray_black_objects_on_stack minor g_alloc obj dst wz st;
    let result = copy_fields minor g_alloc obj dst 0 wz in
    copy_fields_preserves_objects_aux minor g_alloc obj dst 0 wz;
    copy_fields_preserves_wfh_part1 minor g_alloc obj dst wz;
    assert (Seq.mem dst (objects zero_addr result));

    zero_promote_padding_preserves_gray_black_objects_on_stack result dst wz st;
    zero_promote_padding_preserves_objects result dst wz;
    zero_promote_padding_preserves_wfh_part1 result dst wz;
    let padded = zero_promote_padding result dst wz in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    set_promoted_tag_preserves_gray_black_objects_on_stack padded dst tag st
  end
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_one_preserves_gray_black_objects_on_stack
  (minor: minor_state) (cs: cheney_state) (addr: U64.t) (st: seq obj_addr)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    gray_black_objects_on_stack cs.cs_major st /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    gray_black_objects_on_stack cs'.cs_major st))
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    if not (Seq.mem parent (minor_objects minor)) || cs.cs_fwd parent <> 0UL then
      cheney_forward_normal_noop minor cs parent
    else if minor_wosize minor parent = 0 then
      cheney_forward_normal_noop_wz0 minor cs parent
    else begin
      let wz = minor_wosize minor parent in
      assert (wz <> 0);
      assert (wz > 0);
      let res = promote_object minor cs.cs_major parent cs.cs_fp wz in
      if res.new_addr = 0UL then begin
        assert (minor_wosize minor parent == wz);
        assert (minor_wosize minor parent > 0);
        assert ((promote_object minor cs.cs_major parent cs.cs_fp
                  (minor_wosize minor parent)).new_addr = 0UL);
        cheney_forward_normal_noop_oom minor cs parent
      end
      else begin
        assert (minor_wosize minor parent == wz);
        assert (minor_wosize minor parent > 0);
        assert ((promote_object minor cs.cs_major parent cs.cs_fp
                  (minor_wosize minor parent)).new_addr <> 0UL);
        cheney_forward_normal_success minor cs parent;
        promote_object_preserves_gray_black_objects_on_stack minor cs.cs_major parent cs.cs_fp wz st
      end
    end
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    if not (Seq.mem addr (minor_objects minor)) then
      cheney_forward_normal_noop minor cs addr
    else if minor_wosize minor addr = 0 then
      cheney_forward_normal_noop_wz0 minor cs addr
    else begin
      let wz = minor_wosize minor addr in
      assert (wz <> 0);
      assert (wz > 0);
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then begin
        assert (minor_wosize minor addr == wz);
        assert (minor_wosize minor addr > 0);
        assert ((promote_object minor cs.cs_major addr cs.cs_fp
                  (minor_wosize minor addr)).new_addr = 0UL);
        cheney_forward_normal_noop_oom minor cs addr
      end
      else begin
        assert (minor_wosize minor addr == wz);
        assert (minor_wosize minor addr > 0);
        assert ((promote_object minor cs.cs_major addr cs.cs_fp
                  (minor_wosize minor addr)).new_addr <> 0UL);
        cheney_forward_normal_success minor cs addr;
        promote_object_preserves_gray_black_objects_on_stack minor cs.cs_major addr cs.cs_fp wz st
      end
    end
  end
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let rec cheney_forward_fields_preserves_gray_black_objects_on_stack
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  (st: seq obj_addr)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    gray_black_objects_on_stack cs.cs_major st /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    gray_black_objects_on_stack cs'.cs_major st))
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    cheney_forward_fields_base minor cs parent idx wosize
  else begin
    cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    Forwarding.cheney_forward_one_preserves_cob minor cs field_val;
    cheney_forward_one_preserves_gray_black_objects_on_stack minor cs field_val st;
    cheney_forward_fields_preserves_gray_black_objects_on_stack minor cs' parent (idx + 1) wosize st
  end
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let rec cheney_forward_roots_preserves_gray_black_objects_on_stack
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  (st: seq obj_addr)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    gray_black_objects_on_stack cs.cs_major st /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    gray_black_objects_on_stack cs'.cs_major st))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots idx
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    Forwarding.cheney_forward_one_preserves_cob minor cs r;
    cheney_forward_one_preserves_gray_black_objects_on_stack minor cs r st;
    cheney_forward_roots_preserves_gray_black_objects_on_stack minor cs' roots (idx + 1) st
  end
#pop-options

#restart-solver

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let rec cheney_scan_preserves_gray_black_objects_on_stack
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  (st: seq obj_addr)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    gray_black_objects_on_stack cs.cs_major st /\
                    minor_infix_wf minor)
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    gray_black_objects_on_stack cs'.cs_major st))
          (decreases fuel)
  =
  if fuel = 0 then
    cheney_scan_base minor cs scan fuel
  else if fuel > 0 then
    if scan >= Seq.length cs.cs_queue then
      cheney_scan_base minor cs scan fuel
    else begin
      cheney_scan_step minor cs scan fuel;
      let fuel' : nat = fuel - 1 in
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' = cheney_forward_fields minor cs obj 0 wz in
      cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
      Forwarding.cheney_forward_fields_preserves_cob minor cs obj 0 wz;
      cheney_forward_fields_preserves_gray_black_objects_on_stack minor cs obj 0 wz st;
      cheney_scan_preserves_gray_black_objects_on_stack minor cs' (scan + 1) fuel' st
    end
  else begin
    assert False
  end
#pop-options

#restart-solver

let cheney_promote_preserves_gray_black_objects_on_stack
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
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_forward_roots_preserves_gray_black_objects_on_stack minor cs0 roots 0 st;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  Forwarding.cheney_forward_roots_preserves_cob minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_gray_black_objects_on_stack minor cs1 0 (cheney_fuel minor) st

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0 --split_queries always"
let update_major_pointers_preserves_gray_black_objects_on_stack
  (major: heap) (fwd: forwarding_map) (st: seq obj_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    gray_black_objects_on_stack major st)
          (ensures gray_black_objects_on_stack (update_major_pointers major fwd) st)
  =
  let major' = update_major_pointers major fwd in
  update_major_pointers_preserves_objects major fwd;
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (objects zero_addr major') /\
                      (is_gray h major' \/ is_black h major'))
            (ensures Seq.mem h st)
    =
    assert (Seq.mem h (objects zero_addr major));
    update_major_pointers_preserves_header major fwd h;
    color_of_header_eq h major major';
    assert (is_gray h major \/ is_black h major);
    assert (Seq.mem h st)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

let cheney_collect_preserves_gray_black_objects_on_stack
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
  =
  cheney_promote_preserves_gray_black_objects_on_stack minor major fp roots st;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  update_major_pointers_preserves_gray_black_objects_on_stack prom.major_final prom.fwd_map st;
  assert ((cheney_collect_spec minor major fp roots).mc_major ==
          update_major_pointers prom.major_final prom.fwd_map)

/// ---------------------------------------------------------------------------
/// Cheney promotion preserves no_scan_invariant
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let chain_objects_blue_implies_allocated_avoid_chain
  (major: heap) (fp: U64.t)
  : Lemma (requires chain_objects_blue major fp)
          (ensures allocated_avoid_chain major fp)
  =
  reveal_opaque (`%chain_objects_blue) chain_objects_blue
#pop-options

#restart-solver

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"
private let cheney_forward_one_preserves_no_scan_invariant
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    no_scan_invariant cs.cs_major /\
                    minor_no_scan_invariant minor /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor)
          (ensures no_scan_invariant (cheney_forward_one minor cs addr).cs_major)
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    if not (Seq.mem parent (minor_objects minor)) || cs.cs_fwd parent <> 0UL then
      cheney_forward_normal_noop minor cs parent
    else if minor_wosize minor parent = 0 then
      cheney_forward_normal_noop_wz0 minor cs parent
    else begin
      let wz = minor_wosize minor parent in
      let res = promote_object minor cs.cs_major parent cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_normal_noop_oom minor cs parent
      else begin
        cheney_forward_normal_success minor cs parent;
        chain_objects_blue_implies_allocated_avoid_chain cs.cs_major cs.cs_fp;
        promote_object_preserves_no_scan_invariant minor cs.cs_major parent cs.cs_fp wz
      end
    end
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    if not (Seq.mem addr (minor_objects minor)) then
      cheney_forward_normal_noop minor cs addr
    else if minor_wosize minor addr = 0 then
      cheney_forward_normal_noop_wz0 minor cs addr
    else begin
      let wz = minor_wosize minor addr in
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_normal_noop_oom minor cs addr
      else begin
        cheney_forward_normal_success minor cs addr;
        chain_objects_blue_implies_allocated_avoid_chain cs.cs_major cs.cs_fp;
        promote_object_preserves_no_scan_invariant minor cs.cs_major addr cs.cs_fp wz
      end
    end
  end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec cheney_forward_fields_preserves_no_scan_invariant
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    no_scan_invariant cs.cs_major /\
                    minor_no_scan_invariant minor /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor)
          (ensures no_scan_invariant (cheney_forward_fields minor cs parent idx wosize).cs_major)
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    cheney_forward_fields_base minor cs parent idx wosize
  else begin
    cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    Forwarding.cheney_forward_one_preserves_cob minor cs field_val;
    cheney_forward_one_preserves_no_scan_invariant minor cs field_val;
    cheney_forward_fields_preserves_no_scan_invariant minor cs' parent (idx + 1) wosize
  end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec cheney_forward_roots_preserves_no_scan_invariant
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    no_scan_invariant cs.cs_major /\
                    minor_no_scan_invariant minor /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor)
          (ensures no_scan_invariant (cheney_forward_roots minor cs roots idx).cs_major)
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots idx
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    Forwarding.cheney_forward_one_preserves_cob minor cs r;
    cheney_forward_one_preserves_no_scan_invariant minor cs r;
    cheney_forward_roots_preserves_no_scan_invariant minor cs' roots (idx + 1)
  end
#pop-options

#restart-solver

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec cheney_scan_preserves_no_scan_invariant
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    no_scan_invariant cs.cs_major /\
                    minor_no_scan_invariant minor /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor)
          (ensures no_scan_invariant (cheney_scan minor cs scan fuel).cs_major)
          (decreases fuel)
  =
  if fuel = 0 then
    cheney_scan_base minor cs scan fuel
  else if fuel > 0 then
    if scan >= Seq.length cs.cs_queue then
      cheney_scan_base minor cs scan fuel
    else begin
      cheney_scan_step minor cs scan fuel;
      let fuel' : nat = fuel - 1 in
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' = cheney_forward_fields minor cs obj 0 wz in
      cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
      Forwarding.cheney_forward_fields_preserves_cob minor cs obj 0 wz;
      cheney_forward_fields_preserves_no_scan_invariant minor cs obj 0 wz;
      cheney_scan_preserves_no_scan_invariant minor cs' (scan + 1) fuel'
    end
  else
    assert False
#pop-options

let cheney_promote_preserves_no_scan_invariant
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    no_scan_invariant major /\
                    minor_no_scan_invariant minor /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor)
          (ensures no_scan_invariant (cheney_promote minor major fp roots).major_final)
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_forward_roots_preserves_no_scan_invariant minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  Forwarding.cheney_forward_roots_preserves_cob minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_no_scan_invariant minor cs1 0 (cheney_fuel minor)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let cheney_forward_one_preserves_blue_fields_closed
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    blue_fields_closed cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor)
          (ensures blue_fields_closed (cheney_forward_one minor cs addr).cs_major)
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    if not (Seq.mem parent (minor_objects minor)) || cs.cs_fwd parent <> 0UL then
      cheney_forward_normal_noop minor cs parent
    else if minor_wosize minor parent = 0 then
      cheney_forward_normal_noop_wz0 minor cs parent
    else begin
      let wz = minor_wosize minor parent in
      let res = promote_object minor cs.cs_major parent cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_normal_noop_oom minor cs parent
      else begin
        cheney_forward_normal_success minor cs parent;
        BlueProm.promote_object_preserves_bfc minor cs.cs_major parent cs.cs_fp wz
      end
    end
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    if not (Seq.mem addr (minor_objects minor)) then
      cheney_forward_normal_noop minor cs addr
    else if minor_wosize minor addr = 0 then
      cheney_forward_normal_noop_wz0 minor cs addr
    else begin
      let wz = minor_wosize minor addr in
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_normal_noop_oom minor cs addr
      else begin
        cheney_forward_normal_success minor cs addr;
        BlueProm.promote_object_preserves_bfc minor cs.cs_major addr cs.cs_fp wz
      end
    end
  end

private let rec cheney_forward_fields_preserves_blue_fields_closed
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    blue_fields_closed cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor)
          (ensures blue_fields_closed (cheney_forward_fields minor cs parent idx wosize).cs_major)
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    cheney_forward_fields_base minor cs parent idx wosize
  else begin
    cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    Forwarding.cheney_forward_one_preserves_cob minor cs field_val;
    cheney_forward_one_preserves_blue_fields_closed minor cs field_val;
    cheney_forward_fields_preserves_blue_fields_closed minor cs' parent (idx + 1) wosize
  end

private let rec cheney_forward_roots_preserves_blue_fields_closed
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    blue_fields_closed cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor)
          (ensures blue_fields_closed (cheney_forward_roots minor cs roots idx).cs_major)
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots idx
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    Forwarding.cheney_forward_one_preserves_cob minor cs r;
    cheney_forward_one_preserves_blue_fields_closed minor cs r;
    cheney_forward_roots_preserves_blue_fields_closed minor cs' roots (idx + 1)
  end

private let rec cheney_scan_preserves_blue_fields_closed
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    blue_fields_closed cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor)
          (ensures blue_fields_closed (cheney_scan minor cs scan fuel).cs_major)
          (decreases fuel)
  =
  if fuel = 0 then
    cheney_scan_base minor cs scan fuel
  else if scan >= Seq.length cs.cs_queue then
    cheney_scan_base minor cs scan fuel
  else begin
    cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    Forwarding.cheney_forward_fields_preserves_cob minor cs obj 0 wz;
    cheney_forward_fields_preserves_blue_fields_closed minor cs obj 0 wz;
    assert (fuel > 0);
    assert (fuel - 1 < fuel);
    cheney_scan_preserves_blue_fields_closed minor cs' (scan + 1) (fuel - 1)
  end
#pop-options

let cheney_promote_preserves_blue_fields_closed
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor)
          (ensures blue_fields_closed (cheney_promote minor major fp roots).major_final)
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  BlueAlloc.wfh_part2_implies_blue_fields_closed major;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_forward_roots_preserves_blue_fields_closed minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  Forwarding.cheney_forward_roots_preserves_cob minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_blue_fields_closed minor cs1 0 (cheney_fuel minor)

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0 --split_queries always"
let update_major_pointers_preserves_no_scan_invariant
  (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\
                    no_scan_invariant major)
          (ensures no_scan_invariant (update_major_pointers major fwd))
  =
  let major' = update_major_pointers major fwd in
  update_major_pointers_preserves_objects major fwd;
  let aux (src: obj_addr) (idx: nat)
    : Lemma (ensures (
        Seq.mem src (objects zero_addr major') /\
        is_no_scan src major' /\
        ~(is_blue src major') /\
        idx < U64.v (wosize_of_object src major') /\
        U64.v src + idx * 8 < heap_size ==>
        (let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
         ~(is_pointer_field (read_word major' field_addr)))))
    =
    if Seq.mem src (objects zero_addr major') &&
       is_no_scan src major' &&
       not (is_blue src major') &&
       idx < U64.v (wosize_of_object src major') &&
       U64.v src + idx * 8 < heap_size then begin
      assert (Seq.mem src (objects zero_addr major));
      update_major_pointers_preserves_header major fwd src;
      assert (read_word major' (hd_address src) == read_word major (hd_address src));
      is_no_scan_spec src major;
      is_no_scan_spec src major';
      tag_of_object_spec src major;
      tag_of_object_spec src major';
      color_of_header_eq src major major';
      wosize_of_object_spec src major;
      wosize_of_object_spec src major';
      assert (is_no_scan src major);
      assert (~(is_blue src major));
      assert (idx < U64.v (wosize_of_object src major));
      wfh_part1_obj_bound major src;
      assert (U64.v src + idx * 8 + 8 <= heap_size);
      assert ((U64.v src + idx * 8) % 8 == 0);
      update_major_pointers_preserves_no_scan_field major fwd src idx;
      no_scan_invariant_elim major src idx
    end
  in
  FStar.Classical.forall_intro_2 aux;
  no_scan_invariant_intro major'
#pop-options

let cheney_collect_preserves_no_scan_invariant
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    no_scan_invariant major /\
                    minor_no_scan_invariant minor /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor)
          (ensures no_scan_invariant (cheney_collect_spec minor major fp roots).mc_major)
  =
  cheney_promote_preserves_no_scan_invariant minor major fp roots;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  update_major_pointers_preserves_no_scan_invariant prom.major_final prom.fwd_map;
  assert ((cheney_collect_spec minor major fp roots).mc_major ==
          update_major_pointers prom.major_final prom.fwd_map)



/// ---------------------------------------------------------------------------
/// Delegated preservation families
/// ---------------------------------------------------------------------------

module Injectivity = GC.Gen.CheneyPreservation.Injectivity

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let cheney_promote_fwd_valid_or_infix
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_valid_or_infix (cheney_promote minor major fp roots).fwd_map
                                      (cheney_promote minor major fp roots).major_final)
  = Forwarding.cheney_promote_fwd_valid_or_infix minor major fp roots

let cheney_promote_frame_old_fields = Frame.cheney_promote_frame_old_fields

let cheney_promote_frame_old_header = Frame.cheney_promote_frame_old_header

let cheney_promote_fwd_normal_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
           (ensures fwd_normal_injective (cheney_promote minor major fp roots).fwd_map
                                         (cheney_promote minor major fp roots).major_final)
  = Injectivity.cheney_promote_fwd_normal_injective minor major fp roots

let cheney_promote_fwd_targets_not_blue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_targets_not_blue (cheney_promote minor major fp roots).fwd_map
                                        (cheney_promote minor major fp roots).major_final)
  = Injectivity.cheney_promote_fwd_targets_not_blue minor major fp roots

let cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
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
  = Injectivity.cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
      minor major fp roots

let cheney_promote_nonblue_origin
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
  = NonBlueOrigin.cheney_promote_nonblue_origin minor major fp roots obj
#pop-options

let field_fwd_targets_in_objects (major: heap) (fwd: forwarding_map) : prop =
  forall (src: obj_addr) (j: nat).
    Seq.mem src (objects zero_addr major) /\
    ~(is_blue src major) /\
    ~(is_no_scan src major) /\
    j < U64.v (wosize_of_object src major) /\
    U64.v src + j * 8 + 8 <= heap_size /\
    (U64.v src + j * 8) % 8 == 0 ==>
     (let old_val = to_minor_offset
        (read_word major (U64.uint_to_t (U64.v src + j * 8))) in
      is_minor_pointer old_val /\ fwd old_val <> 0UL ==>
      U64.v (fwd old_val) >= U64.v mword /\
      U64.v (fwd old_val) < heap_size /\
      U64.v (fwd old_val) % U64.v mword == 0 /\
      Seq.mem ((fwd old_val) <: obj_addr) (objects zero_addr major))

let field_old_pointer_targets_in_objects (major: heap) (fwd: forwarding_map) : prop =
  forall (src: obj_addr) (j: nat).
    Seq.mem src (objects zero_addr major) /\
    ~(is_blue src major) /\
    ~(is_no_scan src major) /\
    j < U64.v (wosize_of_object src major) /\
    U64.v src + j * 8 + 8 <= heap_size /\
    (U64.v src + j * 8) % 8 == 0 ==>
    (let old_raw = read_word major (U64.uint_to_t (U64.v src + j * 8)) in
     let old_val = to_minor_offset old_raw in
     is_pointer old_raw /\
     ~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==>
     Seq.mem (old_raw <: obj_addr) (objects zero_addr major))

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --split_queries always"
private let header_eq_preserves_no_scan
  (g1 g2: heap) (obj: obj_addr)
  : Lemma
    (requires read_word g1 (hd_address obj) == read_word g2 (hd_address obj))
    (ensures is_no_scan obj g1 == is_no_scan obj g2)
  =
  tag_of_object_spec obj g1;
  tag_of_object_spec obj g2;
  is_no_scan_spec obj g1;
  is_no_scan_spec obj g2

private let fwd_noninfix_target_exists
  (minor: minor_state) (fwd: forwarding_map) (g: heap) (x: U64.t)
  : Lemma
    (requires Forwarding.fwd_noninfix_targets_valid minor fwd g /\
              fwd x <> 0UL /\
              ~(is_infix_in_minor minor x))
    (ensures exists (target: obj_addr).
       fwd x == target /\ Seq.mem target (objects zero_addr g))
  =
  assert (U64.v (fwd x) >= U64.v mword);
  assert (U64.v (fwd x) < heap_size);
  assert (U64.v (fwd x) % U64.v mword == 0);
  is_val_addr_spec (fwd x);
  FStar.Classical.exists_intro
    (fun (target: obj_addr) -> fwd x == target /\
      Seq.mem target (objects zero_addr g))
    ((fwd x) <: obj_addr)
#pop-options

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0 --split_queries always"
private let cheney_promote_field_fwd_targets_in_objects_from_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures
      field_fwd_targets_in_objects
        (cheney_promote minor major fp roots).major_final
        (cheney_promote minor major fp roots).fwd_map)
  =
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.minor_heap_shape_elim minor;
  cheney_promote_preserves_objects minor major fp roots;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  cheney_promote_preserves_wfh_part4 minor major fp roots;
  Forwarding.cheney_promote_fwd_noninfix_targets_valid minor major fp roots;
  Injectivity.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  let aux (src: obj_addr) (j: nat)
    : Lemma (ensures (
        Seq.mem src (objects zero_addr prom.major_final) /\
        ~(is_blue src prom.major_final) /\
        ~(is_no_scan src prom.major_final) /\
        j < U64.v (wosize_of_object src prom.major_final) /\
        U64.v src + j * 8 + 8 <= heap_size /\
        (U64.v src + j * 8) % 8 == 0 ==>
        (let old_val = to_minor_offset
           (read_word prom.major_final (U64.uint_to_t (U64.v src + j * 8))) in
         is_minor_pointer old_val /\ prom.fwd_map old_val <> 0UL ==>
         U64.v (prom.fwd_map old_val) >= U64.v mword /\
         U64.v (prom.fwd_map old_val) < heap_size /\
         U64.v (prom.fwd_map old_val) % U64.v mword == 0 /\
         Seq.mem ((prom.fwd_map old_val) <: obj_addr)
                 (objects zero_addr prom.major_final))))
    =
    if Seq.mem src (objects zero_addr prom.major_final) &&
       not (is_blue src prom.major_final) &&
       not (is_no_scan src prom.major_final) &&
       j < U64.v (wosize_of_object src prom.major_final) &&
       U64.v src + j * 8 + 8 <= heap_size &&
       (U64.v src + j * 8) % 8 = 0 then begin
      let field_addr = U64.uint_to_t (U64.v src + j * 8) in
      let old_raw = read_word prom.major_final field_addr in
      let old_val = to_minor_offset old_raw in
      if is_minor_pointer old_val && prom.fwd_map old_val <> 0UL then begin
        if Seq.mem src (objects zero_addr major) && is_blue src major = false then begin
          Frame.cheney_promote_frame_old_header minor major fp roots src;
          header_eq_preserves_no_scan major prom.major_final src;
          wosize_of_object_spec src major;
          wosize_of_object_spec src prom.major_final;
          assert (~(is_no_scan src major));
          assert (j < U64.v (wosize_of_object src major));
          Frame.cheney_promote_frame_old_fields minor major fp roots src j;
          assert (old_val == to_minor_offset (read_word major field_addr));
          GenInv.major_minor_fields_no_infix_targets_elim minor major src j;
          assert (~(is_infix_in_minor minor old_val));
          assert (U64.v (prom.fwd_map old_val) >= U64.v mword);
          assert (U64.v (prom.fwd_map old_val) < heap_size);
          assert (U64.v (prom.fwd_map old_val) % U64.v mword == 0);
          assert (Seq.mem ((prom.fwd_map old_val) <: obj_addr)
                  (objects zero_addr prom.major_final))
        end else begin
          assert (~(Seq.mem src (objects zero_addr major) /\
                    is_blue src major = false));
          NonBlueOrigin.cheney_promote_nonblue_origin minor major fp roots src;
          assert (exists (x: U64.t).
                    prom.fwd_map x == src /\ is_minor_pointer x);
          let x = IndDesc.indefinite_description_ghost U64.t
            (fun x -> prom.fwd_map x == src /\ is_minor_pointer x) in
          assert (prom.fwd_map x == src /\ is_minor_pointer x);
          assert (well_formed_heap_part4 prom.major_final);
          assert (~(is_infix src prom.major_final));
          assert (is_val_addr src);
          assert (is_val_addr (prom.fwd_map x));
          assert (is_infix (prom.fwd_map x) prom.major_final = false);
          assert (Seq.mem x (minor_objects minor));
          if j < minor_wosize minor x then begin
            Fields.cheney_promote_fwd_target_fields_match minor major fp roots x j;
            assert (old_raw == minor_read_field minor x j);
            assert (old_val == to_minor_offset (minor_read_field minor x j));
            GenInv.minor_fields_no_infix_targets_elim minor x j;
            assert (~(is_infix_in_minor minor old_val));
            assert (U64.v (prom.fwd_map old_val) >= U64.v mword);
            assert (U64.v (prom.fwd_map old_val) < heap_size);
            assert (U64.v (prom.fwd_map old_val) % U64.v mword == 0);
            assert (Seq.mem ((prom.fwd_map old_val) <: obj_addr)
                    (objects zero_addr prom.major_final))
          end else begin
            Fields.cheney_promote_fwd_target_extra_field_not_pointer minor major fp roots x j;
            assert (old_raw == 0UL);
            assert (old_val == 0UL);
            assert (~(is_minor_pointer old_val));
            assert False
          end
        end
      end
    end
  in
  FStar.Classical.forall_intro_2 aux
#pop-options

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0 --split_queries always"
private let cheney_promote_field_old_targets_in_objects_from_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures
      field_old_pointer_targets_in_objects
        (cheney_promote minor major fp roots).major_final
        (cheney_promote minor major fp roots).fwd_map)
  =
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.minor_heap_shape_elim minor;
  cheney_promote_preserves_objects minor major fp roots;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  cheney_promote_preserves_wfh_part4 minor major fp roots;
  Injectivity.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  let aux (src: obj_addr) (j: nat)
    : Lemma (ensures (
        Seq.mem src (objects zero_addr prom.major_final) /\
        ~(is_blue src prom.major_final) /\
        ~(is_no_scan src prom.major_final) /\
        j < U64.v (wosize_of_object src prom.major_final) /\
        U64.v src + j * 8 + 8 <= heap_size /\
        (U64.v src + j * 8) % 8 == 0 ==>
        (let v = read_word prom.major_final (U64.uint_to_t (U64.v src + j * 8)) in
         let minor_v = to_minor_offset v in
         is_pointer v /\
         ~(is_minor_pointer minor_v /\ prom.fwd_map minor_v <> 0UL) ==>
         Seq.mem (v <: obj_addr) (objects zero_addr prom.major_final))))
    =
    if Seq.mem src (objects zero_addr prom.major_final) &&
       not (is_blue src prom.major_final) &&
       not (is_no_scan src prom.major_final) &&
       j < U64.v (wosize_of_object src prom.major_final) &&
       U64.v src + j * 8 + 8 <= heap_size &&
       (U64.v src + j * 8) % 8 = 0 then begin
      assert ((U64.v src + j * 8) % 8 == 0);
      let field_addr = U64.uint_to_t (U64.v src + j * 8) in
      let v = read_word prom.major_final field_addr in
      let minor_v = to_minor_offset v in
      if is_pointer v &&
         not (is_minor_pointer minor_v && prom.fwd_map minor_v <> 0UL) then begin
        if Seq.mem src (objects zero_addr major) && is_blue src major = false then begin
          Frame.cheney_promote_frame_old_header minor major fp roots src;
          wosize_of_object_spec src major;
          wosize_of_object_spec src prom.major_final;
          assert (j < U64.v (wosize_of_object src major));
          Frame.cheney_promote_frame_old_fields minor major fp roots src j;
          assert (v == read_word major field_addr);
          let dst : obj_addr = v in
          assert (is_pointer_to (read_word major field_addr) dst);
          NoBlueUtil.field_pointer_target_in_objects_nat major src dst j;
          cheney_promote_preserves_objects minor major fp roots;
          assert (Seq.mem dst (objects zero_addr prom.major_final))
        end else begin
          assert (~(Seq.mem src (objects zero_addr major) /\
                    is_blue src major = false));
          NonBlueOrigin.cheney_promote_nonblue_origin minor major fp roots src;
          assert (exists (x: U64.t).
                    prom.fwd_map x == src /\ is_minor_pointer x);
          let goal = Seq.mem (v <: obj_addr) (objects zero_addr prom.major_final) in
          let proof (x: U64.t)
            : Lemma
              (requires prom.fwd_map x == src /\ is_minor_pointer x)
              (ensures goal)
            =
            assert (well_formed_heap_part4 prom.major_final);
            assert (~(is_infix src prom.major_final));
            assert (is_val_addr src);
            assert (is_val_addr (prom.fwd_map x));
            assert (is_infix (prom.fwd_map x) prom.major_final = false);
            assert (Seq.mem x (minor_objects minor));
            if j < minor_wosize minor x then begin
              Fields.cheney_promote_fwd_target_fields_match minor major fp roots x j;
              assert (v == minor_read_field minor x j);
              GenInv.minor_major_fields_no_blue_elim minor major x j;
              cheney_promote_preserves_objects minor major fp roots;
              assert (Seq.mem (v <: obj_addr) (objects zero_addr major));
              assert (Seq.mem (v <: obj_addr) (objects zero_addr prom.major_final))
            end else begin
              Fields.cheney_promote_fwd_target_extra_field_not_pointer minor major fp roots x j;
              assert (v == 0UL);
              assert (~(is_pointer v));
              assert False
            end
          in
          let x = IndDesc.indefinite_description_ghost U64.t
            (fun x -> prom.fwd_map x == src /\ is_minor_pointer x) in
          assert (prom.fwd_map x == src /\ is_minor_pointer x);
          proof x
        end
      end
    end
  in
  FStar.Classical.forall_intro_2 aux
#pop-options

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0 --split_queries always"
private let update_major_pointers_preserves_wfh_part2_from_field_targets
  (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\
                    field_old_pointer_targets_in_objects major fwd /\
                    field_fwd_targets_in_objects major fwd /\
                    blue_fields_closed major /\
                    no_scan_invariant major)
          (ensures well_formed_heap_part2 (update_major_pointers major fwd))
  =
  let updated = update_major_pointers major fwd in
  update_major_pointers_preserves_objects major fwd;
  let field_closure (src: obj_addr) (j: nat)
    : Lemma (requires Seq.mem src (objects zero_addr updated) /\
                      j < U64.v (wosize_of_object src updated) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let v = read_word updated (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr updated)))
    =
    update_major_pointers_preserves_header major fwd src;
    wosize_of_object_spec src updated;
    wosize_of_object_spec src major;
    assert (Seq.mem src (objects zero_addr major));
    assert (j < U64.v (wosize_of_object src major));
    assert ((U64.v src + j * 8) % 8 == 0);
    if is_blue src major then begin
      update_major_pointers_preserves_blue_field major fwd src j;
      GC.Gen.PromoteUpdate.Header.blue_fields_closed_inst major src j
    end else if is_no_scan src major then begin
      update_major_pointers_preserves_no_scan_field major fwd src j;
      no_scan_invariant_elim major src j
    end else begin
      update_major_pointers_field_effect major fwd src j;
      let field_addr = U64.uint_to_t (U64.v src + j * 8) in
      let old_raw = read_word major field_addr in
      let old_val = to_minor_offset old_raw in
      let new_val = read_word updated field_addr in
      if is_minor_pointer old_val && fwd old_val <> 0UL then begin
        assert (new_val == fwd old_val);
        assert (U64.v (fwd old_val) >= U64.v mword);
        assert (U64.v (fwd old_val) < heap_size);
        assert (U64.v (fwd old_val) % U64.v mword == 0);
        assert (Seq.mem ((fwd old_val) <: obj_addr) (objects zero_addr major));
        assert (Seq.mem ((fwd old_val) <: obj_addr) (objects zero_addr updated))
      end else begin
        assert (new_val == old_raw);
        assert (is_pointer old_raw ==> Seq.mem (old_raw <: obj_addr) (objects zero_addr major));
        assert (is_pointer old_raw ==> Seq.mem (old_raw <: obj_addr) (objects zero_addr updated))
      end
    end
  in
  update_major_pointers_preserves_wfh_part1 major fwd;
  well_formed_heap_part2_from_field_closure updated field_closure
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0 --split_queries always"
let cheney_collect_preserves_wfh_from_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures well_formed_heap
      (cheney_collect_spec minor major fp roots).mc_major)
  =
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.minor_heap_shape_elim minor;
  let prom = cheney_promote minor major fp roots in
  let updated = update_major_pointers prom.major_final prom.fwd_map in
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  cheney_promote_preserves_wfh_part4 minor major fp roots;
  cheney_promote_preserves_blue_fields_closed minor major fp roots;
  cheney_promote_preserves_no_scan_invariant minor major fp roots;
  cheney_promote_field_old_targets_in_objects_from_shape minor major fp roots;
  cheney_promote_field_fwd_targets_in_objects_from_shape minor major fp roots;
  update_major_pointers_preserves_wfh_part1 prom.major_final prom.fwd_map;
  update_major_pointers_preserves_wfh_part4 prom.major_final prom.fwd_map;
  update_major_pointers_preserves_wfh_part3 prom.major_final prom.fwd_map;
  update_major_pointers_preserves_wfh_part2_from_field_targets
    prom.major_final prom.fwd_map;
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  assert (well_formed_heap updated);
  assert ((cheney_collect_spec minor major fp roots).mc_major == updated)
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --split_queries always"
let cheney_collect_preserves_no_pointer_to_blue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp /\
              well_formed_heap (cheney_collect_spec minor major fp roots).mc_major)
    (ensures Mark.no_pointer_to_blue
      (cheney_collect_spec minor major fp roots).mc_major)
  =
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.minor_heap_shape_elim minor;
  NoBlue.cheney_promote_preserves_no_pointer_to_blue_from_shape minor major fp roots;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  cheney_collect_preserves_no_scan_invariant minor major fp roots;
  Forwarding.cheney_promote_fwd_valid_or_infix minor major fp roots;
  Injectivity.cheney_promote_fwd_targets_not_blue minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  assert ((cheney_collect_spec minor major fp roots).mc_major ==
          update_major_pointers prom.major_final prom.fwd_map);
  NoBlue.update_major_pointers_preserves_no_pointer_to_blue
    prom.major_final prom.fwd_map
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0 --split_queries always"
private let update_major_pointers_preserves_blue_link_fields_valid
  (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\
                    FreeListShape.blue_link_fields_valid major)
          (ensures FreeListShape.blue_link_fields_valid
            (update_major_pointers major fwd))
  =
  let updated = update_major_pointers major fwd in
  update_major_pointers_preserves_objects major fwd;
  let aux (src: obj_addr)
    : Lemma (requires Seq.mem src (objects zero_addr updated) /\
                      is_blue src updated /\
                      U64.v (wosize_of_object src updated) >= 1 /\
                      U64.v (hd_address src) + 16 <= heap_size)
            (ensures (let v = read_word updated src in
                      v = 0UL \/ HeapGraph.is_pointer_field v))
    =
    assert (Seq.mem src (objects zero_addr major));
    update_major_pointers_preserves_header major fwd src;
    color_of_header_eq src major updated;
    wosize_of_object_spec src major;
    wosize_of_object_spec src updated;
    assert (is_blue src major);
    assert (U64.v (wosize_of_object src major) >= 1);
    hd_address_spec src;
    assert (U64.v src + 8 <= heap_size);
    update_major_pointers_preserves_blue_field major fwd src 0;
    FreeListShape.blue_link_fields_valid_elim major src;
    assert (read_word updated src == read_word major src)
  in
  FreeListShape.blue_link_fields_valid_intro updated aux

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
private let objects_nonempty_from_header_local (g1 g2: heap) (start: hp_addr)
  : Lemma (requires Seq.length g1 == Seq.length g2 /\
                    read_word g1 start == read_word g2 start /\
                    Seq.length (objects start g1) > 0)
          (ensures Seq.length (objects start g2) > 0)
  = ()
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0 --split_queries always"
private let update_major_pointers_preserves_dense
  (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major)
          (ensures heap_objects_dense (update_major_pointers major fwd))
  =
  let updated = update_major_pointers major fwd in
  update_major_pointers_preserves_objects major fwd;
  let aux (start: hp_addr) : Lemma
    (requires U64.v start + 8 < heap_size /\
              Seq.mem (f_address start) (objects zero_addr updated) /\
              Seq.length (objects start updated) > 0)
    (ensures (let wz = getWosize (read_word updated start) in
              let next = U64.v start + ((U64.v wz + 1) * 8) in
              next + 8 < heap_size ==>
              Seq.length (objects (U64.uint_to_t next) updated) > 0 /\
              Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr updated)))
  =
    assert (Seq.mem (f_address start) (objects zero_addr major));
    update_major_pointers_preserves_header major fwd (f_address start);
    hd_f_roundtrip start;
    assert (read_word updated start == read_word major start);
    objects_nonempty_from_header_local updated major start;
    assert (Seq.length (objects start major) > 0);
    let wz = getWosize (read_word major start) in
    let next = U64.v start + ((U64.v wz + 1) * 8) in
    if next + 8 < heap_size then begin
      assert (Seq.length (objects (U64.uint_to_t next) major) > 0);
      assert (Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr major));
      let next_hp : hp_addr = U64.uint_to_t next in
      update_major_pointers_preserves_header major fwd (f_address next_hp);
      hd_f_roundtrip next_hp;
      assert (read_word updated next_hp == read_word major next_hp);
      objects_nonempty_from_header_local major updated next_hp
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0 --split_queries always"
private let update_major_pointers_preserves_chain_objects_blue
  (major: heap) (fwd: forwarding_map) (fp: U64.t)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp)
          (ensures chain_objects_blue (update_major_pointers major fwd) fp)
  =
  let updated = update_major_pointers major fwd in
  let fuel = heap_size / U64.v mword in
  update_major_pointers_preserves_objects major fwd;
  reveal_opaque (`%chain_objects_blue) chain_objects_blue;
  let aux (obj: obj_addr) : Lemma
    (requires Seq.mem obj (objects zero_addr updated) /\
              ~(is_blue obj updated))
    (ensures AllocLemmas.chain_avoids updated fp obj fuel = true)
  =
    assert (Seq.mem obj (objects zero_addr major));
    update_major_pointers_preserves_header major fwd obj;
    color_of_header_eq obj major updated;
    assert (~(is_blue obj major));
    assert (AllocLemmas.chain_avoids major fp obj fuel = true);
    let links (a: obj_addr) : Lemma
      (requires Seq.mem a (objects zero_addr major) /\
                U64.v (wosize_of_object a major) >= 1 /\
                U64.v (hd_address a) + 16 <= heap_size /\
                a <> obj /\
                AllocLemmas.chain_avoids major fp a fuel = false)
      (ensures read_word updated a == read_word major a)
    =
      if is_blue a major then begin
        hd_address_spec a;
        update_major_pointers_preserves_blue_field major fwd a 0
      end else begin
        assert (AllocLemmas.chain_avoids major fp a fuel = true)
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires links);
    AllocLemmas.chain_avoids_transfer_on_chain major updated fp obj fuel
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

let cheney_collect_preserves_collection_heap_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires GenInv.collection_heap_shape minor major fp)
          (ensures GenInv.collection_heap_shape
            (cheney_collect_spec minor major fp roots).mc_minor
            (cheney_collect_spec minor major fp roots).mc_major
            (cheney_collect_spec minor major fp roots).mc_fp)
  =
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.minor_heap_shape_elim minor;
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec minor major fp roots in
  let updated = update_major_pointers prom.major_final prom.fwd_map in
  assert (res.mc_major == updated);
  assert (res.mc_fp == prom.fp_final);
  assert (res.mc_minor == minor_reset minor);
  cheney_collect_preserves_wfh_from_shape minor major fp roots;
  cheney_collect_preserves_fl_valid minor major fp roots;
  cheney_collect_preserves_fp_pointer_or_zero minor major fp roots;
  cheney_promote_preserves_free_list_shape minor major fp roots;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  assert (well_formed_heap_part1 prom.major_final);
  update_major_pointers_preserves_blue_link_fields_valid
    prom.major_final prom.fwd_map;
  cheney_promote_preserves_dense minor major fp roots;
  update_major_pointers_preserves_objects prom.major_final prom.fwd_map;
  cheney_promote_preserves_cob minor major fp roots;
  update_major_pointers_preserves_dense prom.major_final prom.fwd_map;
  update_major_pointers_preserves_chain_objects_blue
    prom.major_final prom.fwd_map prom.fp_final;
  cheney_collect_preserves_no_black minor major fp roots;
  cheney_collect_preserves_no_scan_invariant minor major fp roots;
  assert (well_formed_heap res.mc_major);
  cheney_collect_preserves_no_pointer_to_blue minor major fp roots;
  FreeListShape.fp_pointer_or_zero_fl_valid_implies_fp_valid
    res.mc_fp res.mc_major (heap_size / U64.v mword);
  FreeListShape.fp_pointer_or_zero_implies_fp_in_heap res.mc_fp res.mc_major;
  assert (heap_objects_dense res.mc_major);
  assert (chain_objects_blue res.mc_major res.mc_fp);
  assert (AllocLemmas.fl_valid res.mc_major res.mc_fp (heap_size / U64.v mword));
  assert (AllocLemmas.fl_chain_terminates res.mc_major res.mc_fp (heap_size / U64.v mword));
  assert (FreeListShape.fp_pointer_or_zero res.mc_fp);
  assert (FreeListShape.blue_link_fields_valid res.mc_major);
  assert (Seq.length (objects zero_addr res.mc_major) > 0);
  assert (SweepInv.fp_valid res.mc_fp res.mc_major);
  assert (Sweep.fp_in_heap res.mc_fp res.mc_major);
  assert (Mark.no_black_objects res.mc_major);
  assert (Mark.no_pointer_to_blue res.mc_major);
  assert (no_scan_invariant res.mc_major);
  GenInv.major_heap_shape_intro res.mc_major res.mc_fp;
  GenInv.collection_heap_shape_after_minor_reset minor res.mc_major res.mc_fp
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"
private let rec stack_elements_valid_transfer_superset
  (g g': heap) (st: seq obj_addr)
  : Lemma
    (requires Mark.stack_elements_valid g st /\
              (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                Seq.mem x (objects zero_addr g')))
    (ensures Mark.stack_elements_valid g' st)
    (decreases Seq.length st)
  =
  if Seq.length st = 0 then ()
  else begin
    let obj = Seq.head st in
    assert (Seq.mem obj (objects zero_addr g));
    assert (Seq.mem obj (objects zero_addr g'));
    stack_elements_valid_transfer_superset g g' (Seq.tail st)
  end
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 0 --split_queries always"
let cheney_collect_preserves_bounded_stack_props
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
  =
  let prom = cheney_promote minor major fp roots in
  let updated = update_major_pointers prom.major_final prom.fwd_map in
  assert ((cheney_collect_spec minor major fp roots).mc_major == updated);
  assert (Mark.stack_elements_valid major st);
  assert (Mark.stack_points_to_gray major st);
  assert (Mark.stack_no_dups st);
  cheney_promote_preserves_objects minor major fp roots;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  update_major_pointers_preserves_objects prom.major_final prom.fwd_map;
  let survives (x: obj_addr)
    : Lemma (requires Seq.mem x (objects zero_addr major))
            (ensures Seq.mem x (objects zero_addr updated))
    =
    assert (Seq.mem x (objects zero_addr prom.major_final));
    assert (Seq.mem x (objects zero_addr updated))
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires survives);
  stack_elements_valid_transfer_superset major updated st;
  let gray_aux (obj: obj_addr)
    : Lemma (requires Seq.mem obj st)
            (ensures is_gray obj updated)
    =
    Mark.sev_mem_objects major st obj;
    assert (Seq.mem obj (objects zero_addr major));
    assert (is_gray obj major);
    Mark.colors_exclusive obj major;
    assert (is_blue obj major = false);
    Frame.cheney_promote_frame_old_header minor major fp roots obj;
    color_of_header_eq obj major prom.major_final;
    assert (is_gray obj prom.major_final);
    assert (Seq.mem obj (objects zero_addr prom.major_final));
    update_major_pointers_preserves_header prom.major_final prom.fwd_map obj;
    color_of_header_eq obj prom.major_final updated;
    assert (is_gray obj updated)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires gray_aux);
  assert (Mark.stack_points_to_gray updated st);
  assert (Mark.stack_no_dups st);
  assert (MarkBounded.bounded_stack_props updated st)
#pop-options
