/// ---------------------------------------------------------------------------
/// GC.Spec.MajorAllocator.MultiAlloc -- Head-reserved multi-allocation demand
/// ---------------------------------------------------------------------------
///
/// This module packages the arithmetic needed by promotion preflight: a list of
/// positive allocation requests can be served by repeatedly splitting the active
/// free-list head, provided the head has one header word per request plus one
/// final reserve word.  It intentionally preserves only allocator shape; copied
/// object color/field invariants are established by later promotion proofs.

module GC.Spec.MajorAllocator.MultiAlloc

open FStar.List.Tot

module U64 = FStar.UInt64

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module Alloc = GC.Spec.Allocator
module MA = GC.Spec.MajorAllocator
module SplitShape = GC.Spec.MajorAllocator.SplitShape

let request_split_demand (requested_wz: nat) : Tot nat =
  MA.major_alloc_demand_wosize requested_wz + 1

let rec allocation_list_demand (requests: list nat) : Tot nat =
  match requests with
  | [] -> 0
  | requested_wz :: rest ->
    request_split_demand requested_wz + allocation_list_demand rest

let rec all_requests_positive (requests: list nat) : Tot prop =
  match requests with
  | [] -> True
  | requested_wz :: rest ->
    requested_wz > 0 /\ all_requests_positive rest

noeq
type major_alloc_list_result = {
  list_major_out: MH.major_heap;
  list_fp_out: U64.t;
  list_objs_out: list U64.t;
}

let rec major_alloc_list_spec
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (requests: list nat)
  : GTot major_alloc_list_result
  (decreases requests) =
  match requests with
  | [] ->
    { list_major_out = mh;
      list_fp_out = fp;
      list_objs_out = [] }
  | requested_wz :: rest ->
    let r = MA.major_alloc_spec_with_fuel mh fp requested_wz fuel in
    let tail =
      major_alloc_list_spec
        r.major_alloc_out r.major_fp_out fuel rest in
    { tail with list_objs_out = r.major_obj_out :: tail.list_objs_out }

let rec allocated_objects_nonzero (objs: list U64.t) : Tot prop =
  match objs with
  | [] -> True
  | obj :: rest -> obj <> 0UL /\ allocated_objects_nonzero rest

let request_split_demand_positive_identity (requested_wz: nat)
  : Lemma
      (requires requested_wz > 0)
      (ensures request_split_demand requested_wz == requested_wz + 1)
  =
  assert (Alloc.normalized_wosize requested_wz == requested_wz);
  assert (MA.major_alloc_demand_wosize requested_wz == requested_wz)

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let rec major_alloc_list_head_split_preserves_alloc_shape
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (requests: list nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                MH.well_formed_major_heap mh /\
                MA.major_fl_valid mh fp fuel /\
                MA.major_fl_above_zero mh fp fuel /\
                MA.major_fl_blocks_fit mh fp fuel /\
                all_requests_positive requests /\
                MA.major_fl_head_wosize mh fp >=
                  allocation_list_demand requests + 1)
      (ensures
        (let r = major_alloc_list_spec mh fp fuel requests in
         r.list_fp_out <> 0UL /\
         MH.well_formed_major_heap r.list_major_out /\
         MA.major_fl_valid r.list_major_out r.list_fp_out fuel /\
         MA.major_fl_above_zero r.list_major_out r.list_fp_out fuel /\
         MA.major_fl_blocks_fit r.list_major_out r.list_fp_out fuel /\
         MA.major_fl_head_wosize r.list_major_out r.list_fp_out >= 1 /\
         allocated_objects_nonzero r.list_objs_out))
      (decreases (length requests))
  =
  match requests with
  | [] ->
    ()
  | requested_wz :: rest ->
    assert (requested_wz > 0);
    assert (all_requests_positive rest);
    let remaining = allocation_list_demand rest + 1 in
    request_split_demand_positive_identity requested_wz;
    assert (remaining > 0);
    assert (allocation_list_demand (requested_wz :: rest) + 1 ==
            requested_wz + 1 + remaining);
    assert (MA.major_fl_head_wosize mh fp >= requested_wz + 1 + remaining);
    assert (MA.major_fl_head_wosize mh fp >= requested_wz + 2);
    SplitShape.major_alloc_head_split_preserves_alloc_shape
      mh fp requested_wz fuel;
    MA.major_alloc_head_split_preserves_head_wosize
      mh fp requested_wz fuel remaining;
    let step = MA.major_alloc_spec_with_fuel mh fp requested_wz fuel in
    assert (step.major_obj_out == fp);
    assert (step.major_obj_out <> 0UL);
    assert (step.major_fp_out <> 0UL);
    assert (MH.well_formed_major_heap step.major_alloc_out);
    assert (MA.major_fl_valid step.major_alloc_out step.major_fp_out fuel);
    assert (MA.major_fl_above_zero step.major_alloc_out step.major_fp_out fuel);
    assert (MA.major_fl_blocks_fit step.major_alloc_out step.major_fp_out fuel);
    assert (MA.major_fl_head_wosize step.major_alloc_out step.major_fp_out >=
            allocation_list_demand rest + 1);
    assert (length rest < length requests);
    major_alloc_list_head_split_preserves_alloc_shape
      step.major_alloc_out step.major_fp_out fuel rest;
    let tail =
      major_alloc_list_spec
        step.major_alloc_out step.major_fp_out fuel rest in
    assert (allocated_objects_nonzero tail.list_objs_out);
    assert (allocated_objects_nonzero
              (step.major_obj_out :: tail.list_objs_out))
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let major_alloc_list_head_split_preserves_alloc_shape_with_budget
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (requests: list nat) (budget: nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                MH.well_formed_major_heap mh /\
                MA.major_fl_valid mh fp fuel /\
                MA.major_fl_above_zero mh fp fuel /\
                MA.major_fl_blocks_fit mh fp fuel /\
                all_requests_positive requests /\
                allocation_list_demand requests <= budget /\
                MA.major_fl_head_wosize mh fp >= budget + 1)
      (ensures
        (let r = major_alloc_list_spec mh fp fuel requests in
         r.list_fp_out <> 0UL /\
         MH.well_formed_major_heap r.list_major_out /\
         MA.major_fl_valid r.list_major_out r.list_fp_out fuel /\
         MA.major_fl_above_zero r.list_major_out r.list_fp_out fuel /\
         MA.major_fl_blocks_fit r.list_major_out r.list_fp_out fuel /\
         MA.major_fl_head_wosize r.list_major_out r.list_fp_out >= 1 /\
         allocated_objects_nonzero r.list_objs_out))
  =
  assert (MA.major_fl_head_wosize mh fp >=
          allocation_list_demand requests + 1);
  major_alloc_list_head_split_preserves_alloc_shape
    mh fp fuel requests
#pop-options
