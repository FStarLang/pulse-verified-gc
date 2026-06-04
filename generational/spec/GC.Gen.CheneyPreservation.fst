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
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SpecMajorAllocSplitShape = GC.Spec.MajorAllocator.SplitShape
module SpecMajorAllocMultiAlloc = GC.Spec.MajorAllocator.MultiAlloc
module AllocHeader = GC.Spec.Allocator.Lemmas.Header
module IndDesc = FStar.IndefiniteDescription

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
                  PromotionDemand.minor_promotion_demand minor + 1 /\
                cheney_promote_split_ready_single_chunk
                  minor major fp roots)
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
  cheney_forwarded_dense_alloc_list_default_single_chunk_no_oom
    minor major fp roots;
  cheney_promote_head_split_preserves_chunked_alloc_shape_single_chunk
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
