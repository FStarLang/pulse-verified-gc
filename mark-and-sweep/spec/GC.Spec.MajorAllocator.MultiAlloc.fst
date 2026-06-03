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

noeq
type dense_alloc_list_result = {
  dense_list_heap_out: heap;
  dense_list_fp_out: U64.t;
  dense_list_objs_out: list U64.t;
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

let rec dense_alloc_list_spec
  (g: heap) (fp: U64.t) (fuel: nat)
  (requests: list nat)
  : GTot dense_alloc_list_result
  (decreases requests) =
  match requests with
  | [] ->
    { dense_list_heap_out = g;
      dense_list_fp_out = fp;
      dense_list_objs_out = [] }
  | requested_wz :: rest ->
    let r = Alloc.alloc_spec_with_fuel g fp requested_wz fuel in
    let tail =
      dense_alloc_list_spec
        r.heap_out r.fp_out fuel rest in
    { tail with dense_list_objs_out = r.obj_out :: tail.dense_list_objs_out }

let rec dense_alloc_list_default_spec
  (g: heap) (fp: U64.t) (requests: list nat)
  : GTot dense_alloc_list_result
  (decreases requests) =
  match requests with
  | [] ->
    { dense_list_heap_out = g;
      dense_list_fp_out = fp;
      dense_list_objs_out = [] }
  | requested_wz :: rest ->
    let r = Alloc.alloc_spec g fp requested_wz in
    let tail =
      dense_alloc_list_default_spec r.heap_out r.fp_out rest in
    { tail with dense_list_objs_out = r.obj_out :: tail.dense_list_objs_out }

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

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let request_split_demand_lower_bound (requested_wz: nat)
  : Lemma (ensures requested_wz <= request_split_demand requested_wz)
  =
  if requested_wz = 0 then ()
  else request_split_demand_positive_identity requested_wz
#pop-options

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

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let rec major_alloc_list_spec_single_chunk_compat
  (g: heap) (fp: U64.t) (fuel: nat) (requests: list nat)
  : Lemma
      (ensures
        (let major_r =
           major_alloc_list_spec
             (MH.single_chunk_major_heap g) fp fuel requests in
         let dense_r =
           dense_alloc_list_spec g fp fuel requests in
         major_r.list_major_out ==
           MH.single_chunk_major_heap dense_r.dense_list_heap_out /\
         major_r.list_fp_out == dense_r.dense_list_fp_out /\
         major_r.list_objs_out == dense_r.dense_list_objs_out))
      (decreases (length requests))
  =
  match requests with
  | [] ->
    ()
  | requested_wz :: rest ->
    MA.major_alloc_spec_with_fuel_single_chunk_compat
      g fp requested_wz fuel;
    let major_step =
      MA.major_alloc_spec_with_fuel
        (MH.single_chunk_major_heap g) fp requested_wz fuel in
    let dense_step =
      Alloc.alloc_spec_with_fuel g fp requested_wz fuel in
    assert (major_step.major_alloc_out ==
            MH.single_chunk_major_heap dense_step.heap_out);
    assert (major_step.major_fp_out == dense_step.fp_out);
    assert (major_step.major_obj_out == dense_step.obj_out);
    major_alloc_list_spec_single_chunk_compat
      dense_step.heap_out dense_step.fp_out fuel rest;
    let major_tail =
      major_alloc_list_spec
        major_step.major_alloc_out major_step.major_fp_out fuel rest in
    let dense_tail =
      dense_alloc_list_spec
        dense_step.heap_out dense_step.fp_out fuel rest in
    assert (major_tail.list_major_out ==
            MH.single_chunk_major_heap dense_tail.dense_list_heap_out);
    assert (major_tail.list_fp_out == dense_tail.dense_list_fp_out);
    assert (major_tail.list_objs_out == dense_tail.dense_list_objs_out)
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let dense_alloc_list_head_split_nonzero_single_chunk
  (g: heap) (fp: U64.t) (fuel: nat)
  (requests: list nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                MH.well_formed_major_heap
                  (MH.single_chunk_major_heap g) /\
                MA.major_fl_valid
                  (MH.single_chunk_major_heap g) fp fuel /\
                MA.major_fl_above_zero
                  (MH.single_chunk_major_heap g) fp fuel /\
                MA.major_fl_blocks_fit
                  (MH.single_chunk_major_heap g) fp fuel /\
                all_requests_positive requests /\
                MA.major_fl_head_wosize
                  (MH.single_chunk_major_heap g) fp >=
                  allocation_list_demand requests + 1)
      (ensures
        (let r = dense_alloc_list_spec g fp fuel requests in
         allocated_objects_nonzero r.dense_list_objs_out))
  =
  major_alloc_list_head_split_preserves_alloc_shape
    (MH.single_chunk_major_heap g) fp fuel requests;
  major_alloc_list_spec_single_chunk_compat g fp fuel requests;
  let major_r =
    major_alloc_list_spec (MH.single_chunk_major_heap g) fp fuel requests in
  let dense_r = dense_alloc_list_spec g fp fuel requests in
  assert (allocated_objects_nonzero major_r.list_objs_out);
  assert (major_r.list_objs_out == dense_r.dense_list_objs_out)

let dense_alloc_list_head_split_nonzero_single_chunk_with_budget
  (g: heap) (fp: U64.t) (fuel: nat)
  (requests: list nat) (budget: nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                MH.well_formed_major_heap
                  (MH.single_chunk_major_heap g) /\
                MA.major_fl_valid
                  (MH.single_chunk_major_heap g) fp fuel /\
                MA.major_fl_above_zero
                  (MH.single_chunk_major_heap g) fp fuel /\
                MA.major_fl_blocks_fit
                  (MH.single_chunk_major_heap g) fp fuel /\
                all_requests_positive requests /\
                allocation_list_demand requests <= budget /\
                MA.major_fl_head_wosize
                  (MH.single_chunk_major_heap g) fp >= budget + 1)
      (ensures
        (let r = dense_alloc_list_spec g fp fuel requests in
         allocated_objects_nonzero r.dense_list_objs_out))
  =
  assert (MA.major_fl_head_wosize (MH.single_chunk_major_heap g) fp >=
          allocation_list_demand requests + 1);
  dense_alloc_list_head_split_nonzero_single_chunk
    g fp fuel requests
#pop-options

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
let rec dense_alloc_list_default_spec_eq_search_fuel
  (g: heap) (fp: U64.t) (requests: list nat)
  : Lemma
      (ensures
        dense_alloc_list_default_spec g fp requests ==
        dense_alloc_list_spec g fp Alloc.alloc_search_fuel requests)
      (decreases (length requests))
  =
  match requests with
  | [] ->
    ()
  | requested_wz :: rest ->
    let r = Alloc.alloc_spec g fp requested_wz in
    dense_alloc_list_default_spec_eq_search_fuel
      r.heap_out r.fp_out rest
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let dense_alloc_list_default_head_split_nonzero_single_chunk_with_budget
  (g: heap) (fp: U64.t)
  (requests: list nat) (budget: nat)
  : Lemma
      (requires Alloc.alloc_search_fuel > 1 /\
                fp <> 0UL /\
                MH.well_formed_major_heap
                  (MH.single_chunk_major_heap g) /\
                MA.major_fl_valid
                  (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel /\
                MA.major_fl_above_zero
                  (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel /\
                MA.major_fl_blocks_fit
                  (MH.single_chunk_major_heap g) fp Alloc.alloc_search_fuel /\
                all_requests_positive requests /\
                allocation_list_demand requests <= budget /\
                MA.major_fl_head_wosize
                  (MH.single_chunk_major_heap g) fp >= budget + 1)
      (ensures
        (let r = dense_alloc_list_default_spec g fp requests in
         allocated_objects_nonzero r.dense_list_objs_out))
  =
  dense_alloc_list_head_split_nonzero_single_chunk_with_budget
    g fp Alloc.alloc_search_fuel requests budget;
  dense_alloc_list_default_spec_eq_search_fuel g fp requests
#pop-options
