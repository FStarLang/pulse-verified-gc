/// ---------------------------------------------------------------------------
/// GC.Gen.HeapInvariant -- Central generational heap-shape invariant
/// ---------------------------------------------------------------------------

module GC.Gen.HeapInvariant

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module Sweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module HeapModel = GC.Spec.HeapModel
module HeapGraph = GC.Spec.HeapGraph
module Graph = GC.Spec.Graph
module FreeListShape = GC.Gen.FreeListShape
module MH = GC.Spec.MajorHeap
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SpecMajorAllocSplitShape = GC.Spec.MajorAllocator.SplitShape
module SpecMajorAllocMultiAlloc = GC.Spec.MajorAllocator.MultiAlloc
module PromotionDemand = GC.Gen.PromotionDemand
module Header = GC.Lib.Header
module CG = GC.Gen.CombinedGraph

private let rec seq_mem_to_index (#a:eqtype) (x:a) (s:seq a)
  : Ghost nat
    (requires Seq.mem x s)
    (ensures fun i -> i < Seq.length s /\ Seq.index s i == x)
    (decreases Seq.length s)
  =
  if Seq.index s 0 == x then 0
  else begin
    let tl = Seq.slice s 1 (Seq.length s) in
    Seq.lemma_count_slice s 1;
    1 + seq_mem_to_index x tl
  end

[@@"opaque_to_smt"]
let major_heap_shape (major: heap) (fp: U64.t) : prop =
  well_formed_heap major /\
  AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
  AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
  FreeListShape.fp_pointer_or_zero fp /\
  FreeListShape.blue_link_fields_valid major /\
  heap_objects_dense major /\
  chain_objects_blue major fp /\
  Seq.length (objects zero_addr major) > 0 /\
  SweepInv.fp_valid fp major /\
  Sweep.fp_in_heap fp major /\
  Mark.no_black_objects major /\
  Mark.no_pointer_to_blue major /\
  no_scan_invariant major

[@@"opaque_to_smt"]
let chunked_major_alloc_shape
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat) : Tot prop =
  MH.well_formed_major_heap mh /\
  SpecMajorAlloc.major_fl_valid mh fp fuel /\
  SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
  SpecMajorAlloc.major_fl_blocks_fit mh fp fuel

let chunked_color_of_object (mh: MH.major_heap) (obj: obj_addr)
  : GTot (option color)
  = match MH.read_word_in_major mh (hd_address obj) with
    | Some hdr -> Some (getColor hdr)
    | None -> None

let chunked_is_blue (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool
  = match chunked_color_of_object mh obj with
    | Some Header.Blue -> true
    | _ -> false

let chunked_is_blue_header
  (mh: MH.major_heap) (obj: obj_addr) (hdr: U64.t)
  : Lemma
      (requires MH.read_word_in_major mh (hd_address obj) == Some hdr)
      (ensures chunked_is_blue mh obj == (getColor hdr = Header.Blue))
  =
  assert (chunked_color_of_object mh obj == Some (getColor hdr));
  match getColor hdr with
  | Header.Blue ->
    assert (chunked_is_blue mh obj == true)
  | Header.White ->
    assert (getColor hdr <> Header.Blue);
    assert (chunked_is_blue mh obj == false)
  | Header.Gray ->
    assert (getColor hdr <> Header.Blue);
    assert (chunked_is_blue mh obj == false)
  | Header.Black ->
    assert (getColor hdr <> Header.Blue);
    assert (chunked_is_blue mh obj == false)

let chunked_is_black (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool
  = match chunked_color_of_object mh obj with
    | Some Header.Black -> true
    | _ -> false

[@@"opaque_to_smt"]
let chunked_no_black_objects (mh: MH.major_heap) : Tot prop =
  forall (obj: obj_addr).
    Seq.mem obj (MH.major_objects mh) ==>
    ~(chunked_is_black mh obj)

[@@"opaque_to_smt"]
let chunked_no_scan_invariant (mh: MH.major_heap) : Tot prop =
  forall (src: obj_addr) (idx: nat) (field_addr: hp_addr) (raw: U64.t).
    Seq.mem src (MH.major_objects mh) /\
    CG.chunked_is_no_scan mh src /\
    ~(chunked_is_blue mh src) /\
    idx < CG.chunked_wosize_nat_of_object mh src /\
    CG.chunked_major_field_slot src idx == Some field_addr /\
    MH.read_word_in_major mh field_addr == Some raw ==>
    ~(is_pointer_field raw)

[@@"opaque_to_smt"]
let chunked_no_pointer_to_blue (mh: MH.major_heap) : Tot prop =
  forall (src: obj_addr) (dst: obj_addr) (idx: nat)
         (field_addr: hp_addr) (raw: U64.t).
    Seq.mem src (MH.major_objects mh) /\
    ~(chunked_is_blue mh src) /\
    idx < CG.chunked_wosize_nat_of_object mh src /\
    CG.chunked_major_field_slot src idx == Some field_addr /\
    MH.read_word_in_major mh field_addr == Some raw /\
    Seq.mem dst (MH.major_objects mh) /\
    is_pointer_to raw dst ==>
    ~(chunked_is_blue mh dst)

[@@"opaque_to_smt"]
let chunked_chain_objects_blue
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat) : Tot prop =
  forall (obj: obj_addr).
    Seq.mem obj (MH.major_objects mh) /\
    ~(chunked_is_blue mh obj) ==>
    SpecMajorAlloc.major_fl_chain_avoids mh fp obj fuel = true

[@@"opaque_to_smt"]
let chunked_minor_major_fields_no_blue
  (minor: minor_state) (mh: MH.major_heap) : Tot prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    j < minor_wosize minor obj /\
    is_pointer_field (minor_read_field minor obj j) ==>
    Seq.mem ((minor_read_field minor obj j) <: obj_addr)
            (MH.major_objects mh) /\
    ~(chunked_is_blue mh ((minor_read_field minor obj j) <: obj_addr))

[@@"opaque_to_smt"]
let chunked_major_minor_fields_no_infix_targets
  (minor: minor_state) (mh: MH.major_heap) : Tot prop =
  forall (obj: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t).
    Seq.mem obj (MH.major_objects mh) /\
    ~(chunked_is_blue mh obj) /\
    ~(CG.chunked_is_no_scan mh obj) /\
    j < CG.chunked_wosize_nat_of_object mh obj /\
    CG.chunked_major_field_slot obj j == Some field_addr /\
    MH.read_word_in_major mh field_addr == Some raw /\
    is_minor_pointer (to_minor_offset raw) ==>
    ~(is_infix_in_minor minor (to_minor_offset raw))

[@@"opaque_to_smt"]
let minor_major_fields_no_blue (minor: minor_state) (major: heap) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    j < minor_wosize minor obj /\
    is_pointer_field (minor_read_field minor obj j) ==>
    Seq.mem ((minor_read_field minor obj j) <: obj_addr)
            (objects zero_addr major) /\
    ~(is_blue ((minor_read_field minor obj j) <: obj_addr) major)

[@@"opaque_to_smt"]
let minor_fields_no_infix_targets (minor: minor_state) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    j < minor_wosize minor obj /\
    is_minor_pointer (to_minor_offset (minor_read_field minor obj j)) ==>
    ~(is_infix_in_minor minor (to_minor_offset (minor_read_field minor obj j)))

[@@"opaque_to_smt"]
let major_minor_fields_no_infix_targets (minor: minor_state) (major: heap) : prop =
  forall (obj: obj_addr) (j: nat).
    Seq.mem obj (objects zero_addr major) /\
    ~(is_blue obj major) /\
    ~(is_no_scan obj major) /\
    j < U64.v (wosize_of_object obj major) /\
    U64.v obj + j * 8 + 8 <= heap_size /\
    (U64.v obj + j * 8) % 8 == 0 ==>
    (let v = to_minor_offset
       (read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
     is_minor_pointer v ==> ~(is_infix_in_minor minor v))

[@@"opaque_to_smt"]
let minor_heap_shape (minor: minor_state) : prop =
  minor_wf minor /\
  minor_guards_complete minor /\
  minor_infix_wf minor /\
  minor_no_scan_invariant minor /\
  minor_fields_no_infix_targets minor

[@@"opaque_to_smt"]
let major_stack_shape (major: heap) (st: seq obj_addr) (cap: nat) : prop =
  MarkBoundedInv.bounded_mark_inv major st cap /\
  Mark.root_props major st /\
  gray_black_objects_on_stack major st /\
  (let graph = HeapModel.create_graph major in
   let roots' = HeapGraph.coerce_to_vertex_list st in
   Graph.graph_wf graph /\ Graph.is_vertex_set roots' /\
   Graph.subset_vertices roots' graph.vertices)

[@@"opaque_to_smt"]
let chunked_collection_heap_shape
  (minor: minor_state) (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Tot prop =
  chunked_major_alloc_shape mh fp fuel /\
  chunked_no_black_objects mh /\
  chunked_no_scan_invariant mh /\
  chunked_no_pointer_to_blue mh /\
  minor_heap_shape minor /\
  chunked_minor_major_fields_no_blue minor mh /\
  chunked_major_minor_fields_no_infix_targets minor mh

[@@"opaque_to_smt"]
let collection_heap_shape (minor: minor_state) (major: heap) (fp: U64.t) : prop =
  major_heap_shape major fp /\
  minor_heap_shape minor /\
  minor_major_fields_no_blue minor major /\
  major_minor_fields_no_infix_targets minor major

[@@"opaque_to_smt"]
let full_heap_shape (minor: minor_state) (major: heap) (fp: U64.t)
                    (st: seq obj_addr) (cap: nat) : prop =
  collection_heap_shape minor major fp /\
  major_stack_shape major st cap

let major_heap_shape_intro (major: heap) (fp: U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    FreeListShape.fp_pointer_or_zero fp /\
                    FreeListShape.blue_link_fields_valid major /\
                    heap_objects_dense major /\
                    chain_objects_blue major fp /\
                    Seq.length (objects zero_addr major) > 0 /\
                    SweepInv.fp_valid fp major /\
                    Sweep.fp_in_heap fp major /\
                    Mark.no_black_objects major /\
                    Mark.no_pointer_to_blue major /\
                    no_scan_invariant major)
          (ensures major_heap_shape major fp)
  = reveal_opaque (`%major_heap_shape) (major_heap_shape major fp)

let major_heap_shape_elim (major: heap) (fp: U64.t)
  : Lemma (requires major_heap_shape major fp)
          (ensures well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    FreeListShape.fp_pointer_or_zero fp /\
                    FreeListShape.blue_link_fields_valid major /\
                    heap_objects_dense major /\
                   chain_objects_blue major fp /\
                   Seq.length (objects zero_addr major) > 0 /\
                   SweepInv.fp_valid fp major /\
                   Sweep.fp_in_heap fp major /\
                   Mark.no_black_objects major /\
                   Mark.no_pointer_to_blue major /\
                   no_scan_invariant major)
  = reveal_opaque (`%major_heap_shape) (major_heap_shape major fp)

let chunked_major_alloc_shape_intro
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Lemma
      (requires MH.well_formed_major_heap mh /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit mh fp fuel)
      (ensures chunked_major_alloc_shape mh fp fuel)
  = reveal_opaque (`%chunked_major_alloc_shape)
      (chunked_major_alloc_shape mh fp fuel)

let chunked_major_alloc_shape_elim
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Lemma
      (requires chunked_major_alloc_shape mh fp fuel)
      (ensures MH.well_formed_major_heap mh /\
               SpecMajorAlloc.major_fl_valid mh fp fuel /\
               SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
               SpecMajorAlloc.major_fl_blocks_fit mh fp fuel)
  = reveal_opaque (`%chunked_major_alloc_shape)
      (chunked_major_alloc_shape mh fp fuel)

let chunked_major_alloc_shape_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: obj_addr) (fuel: nat)
  : Lemma
      (requires chunked_major_alloc_shape mh fp fuel /\
                MH.chunk_disjoint_from_all fresh mh /\
                fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                U64.v fresh.base >= U64.v zero_addr)
      (ensures (
        let r = SpecMajorAlloc.expand_major_heap mh fresh fp in
        chunked_major_alloc_shape r.major_out r.fp_out (fuel + 1)))
  =
  chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAlloc.expand_major_heap_wf mh fresh fp;
  SpecMajorAlloc.expand_major_heap_links_fl_valid mh fresh fp fuel;
  SpecMajorAlloc.expand_major_heap_links_fl_above_zero mh fresh fp fuel;
  SpecMajorAlloc.expand_major_heap_links_fl_blocks_fit mh fresh fp fuel;
  let r = SpecMajorAlloc.expand_major_heap mh fresh fp in
  chunked_major_alloc_shape_intro r.major_out r.fp_out (fuel + 1)

let chunked_major_alloc_shape_ensure_capacity
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_major_alloc_shape mh fp fuel /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh +
                   SpecMajorAlloc.major_fl_capacity mh fp fuel >= needed))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh in
        chunked_major_alloc_shape
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_capacity
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out >= needed))
  =
  chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAlloc.ensure_major_capacity_wf mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_capacity_fl_valid mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_capacity_fl_above_zero mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_capacity_fl_blocks_fit mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_capacity_has_capacity mh fp fuel needed fresh;
  let r = SpecMajorAlloc.ensure_major_capacity_spec mh fp fuel needed fresh in
  chunked_major_alloc_shape_intro
    r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out

let chunked_major_alloc_shape_ensure_head_capacity
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_major_alloc_shape mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= needed))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        chunked_major_alloc_shape
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed))
  =
  chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAlloc.ensure_major_head_capacity_wf mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_head_capacity_fl_valid mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_head_capacity_fl_above_zero mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_head_capacity_fl_blocks_fit mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_head_capacity_has_head_wosize
    mh fp fuel needed fresh;
  let r = SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
  chunked_major_alloc_shape_intro
    r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out

let chunked_major_alloc_shape_active_head_split
  (mh: MH.major_heap) (fp: U64.t)
  (requested_wz fuel: nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                requested_wz > 0 /\
                chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >= requested_wz + 2)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             mh fp requested_wz fuel in
         r.major_obj_out == fp /\
         r.major_fp_out <> 0UL /\
         SpecMajorAlloc.major_alloc_result_fp_in_objects r /\
         chunked_major_alloc_shape
           r.major_alloc_out r.major_fp_out fuel))
  =
  chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAllocSplitShape.major_alloc_head_split_preserves_alloc_shape
    mh fp requested_wz fuel;
  let r =
    SpecMajorAlloc.major_alloc_spec_with_fuel
      mh fp requested_wz fuel in
  chunked_major_alloc_shape_intro
    r.major_alloc_out r.major_fp_out fuel

let chunked_major_alloc_shape_alloc_list_head_split
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (requests: list nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  SpecMajorAllocMultiAlloc.allocation_list_demand requests + 1)
      (ensures
        (let r =
           SpecMajorAllocMultiAlloc.major_alloc_list_spec
             mh fp fuel requests in
         r.list_fp_out <> 0UL /\
         chunked_major_alloc_shape r.list_major_out r.list_fp_out fuel /\
         SpecMajorAlloc.major_fl_head_wosize
           r.list_major_out r.list_fp_out >= 1 /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.list_objs_out))
  =
  chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAllocMultiAlloc.major_alloc_list_head_split_preserves_alloc_shape
    mh fp fuel requests;
  let r =
    SpecMajorAllocMultiAlloc.major_alloc_list_spec
      mh fp fuel requests in
  chunked_major_alloc_shape_intro r.list_major_out r.list_fp_out fuel

let chunked_major_alloc_shape_alloc_list_head_split_with_budget
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (requests: list nat) (budget: nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  budget /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >= budget + 1)
      (ensures
        (let r =
           SpecMajorAllocMultiAlloc.major_alloc_list_spec
             mh fp fuel requests in
         r.list_fp_out <> 0UL /\
         chunked_major_alloc_shape r.list_major_out r.list_fp_out fuel /\
         SpecMajorAlloc.major_fl_head_wosize
           r.list_major_out r.list_fp_out >= 1 /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.list_objs_out))
  =
  chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAllocMultiAlloc.major_alloc_list_head_split_preserves_alloc_shape_with_budget
    mh fp fuel requests budget;
  let r =
    SpecMajorAllocMultiAlloc.major_alloc_list_spec
      mh fp fuel requests in
  chunked_major_alloc_shape_intro r.list_major_out r.list_fp_out fuel

let chunked_major_alloc_shape_alloc_minor_objects_head_split
  (minor: minor_state) (mh: MH.major_heap) (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires fuel > 1 /\
                minor_wf minor /\
                fp <> 0UL /\
                chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let requests = PromotionDemand.minor_promotion_requests minor in
         let r =
           SpecMajorAllocMultiAlloc.major_alloc_list_spec
             mh fp fuel requests in
         r.list_fp_out <> 0UL /\
         chunked_major_alloc_shape r.list_major_out r.list_fp_out fuel /\
         SpecMajorAlloc.major_fl_head_wosize
           r.list_major_out r.list_fp_out >= 1 /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.list_objs_out))
  =
  PromotionDemand.minor_promotion_requests_positive minor;
  PromotionDemand.minor_promotion_demand_eq minor;
  assert (PromotionDemand.minor_promotion_demand minor ==
          SpecMajorAllocMultiAlloc.allocation_list_demand
            (PromotionDemand.minor_promotion_requests minor));
  chunked_major_alloc_shape_alloc_list_head_split
    mh fp fuel (PromotionDemand.minor_promotion_requests minor)

let chunked_minor_major_fields_no_blue_intro
  (minor: minor_state) (mh: MH.major_heap)
  : Lemma
      (requires
        (forall (obj: U64.t) (j: nat).
          Seq.mem obj (minor_objects minor) /\
          j < minor_wosize minor obj /\
          is_pointer_field (minor_read_field minor obj j) ==>
          Seq.mem ((minor_read_field minor obj j) <: obj_addr)
                  (MH.major_objects mh) /\
          ~(chunked_is_blue mh
              ((minor_read_field minor obj j) <: obj_addr))))
      (ensures chunked_minor_major_fields_no_blue minor mh)
  = reveal_opaque (`%chunked_minor_major_fields_no_blue)
      (chunked_minor_major_fields_no_blue minor mh)

let chunked_minor_major_fields_no_blue_no_pointer_fields
  (minor: minor_state) (mh: MH.major_heap)
  : Lemma
      (requires
        (forall (obj:U64.t) (j:nat).
          Seq.mem obj (minor_objects minor) /\
          j < minor_wosize minor obj ==>
          ~(is_pointer_field (minor_read_field minor obj j))))
      (ensures chunked_minor_major_fields_no_blue minor mh)
  = reveal_opaque (`%chunked_minor_major_fields_no_blue)
      (chunked_minor_major_fields_no_blue minor mh)

let chunked_minor_major_fields_no_blue_elim
  (minor: minor_state) (mh: MH.major_heap)
  (obj: U64.t) (j: nat)
  : Lemma
      (requires chunked_minor_major_fields_no_blue minor mh /\
                Seq.mem obj (minor_objects minor) /\
                j < minor_wosize minor obj /\
                is_pointer_field (minor_read_field minor obj j))
      (ensures
        Seq.mem ((minor_read_field minor obj j) <: obj_addr)
                (MH.major_objects mh) /\
        ~(chunked_is_blue mh
            ((minor_read_field minor obj j) <: obj_addr)))
  = reveal_opaque (`%chunked_minor_major_fields_no_blue)
      (chunked_minor_major_fields_no_blue minor mh)

let chunked_no_black_objects_intro (mh: MH.major_heap)
  : Lemma
      (requires
        (forall (obj: obj_addr).
          Seq.mem obj (MH.major_objects mh) ==>
          ~(chunked_is_black mh obj)))
      (ensures chunked_no_black_objects mh)
  =
  reveal_opaque (`%chunked_no_black_objects)
    (chunked_no_black_objects mh)

let chunked_no_black_objects_elim (mh: MH.major_heap) (obj: obj_addr)
  : Lemma
      (requires chunked_no_black_objects mh /\
                Seq.mem obj (MH.major_objects mh))
      (ensures ~(chunked_is_black mh obj))
  =
  reveal_opaque (`%chunked_no_black_objects)
    (chunked_no_black_objects mh)

let chunked_is_black_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                Seq.mem obj (MH.major_objects mh))
      (ensures
        chunked_is_black
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        chunked_is_black mh obj)
  =
  MH.major_object_header_disjoint_from_chunk mh fresh obj;
  SpecMajorAlloc.expand_major_heap_old_read mh fresh fp (hd_address obj)

private let chunked_fresh_object_not_black
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (ensures
        ~(chunked_is_black
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out
          (SpecMajorAlloc.fresh_chunk_object fresh)))
  =
  SpecMajorAlloc.fresh_chunk_has_block fresh;
  SpecMajorAlloc.expand_major_heap_header_fields mh fresh fp;
  hd_f_roundtrip fresh.base;
  assert (hd_address (SpecMajorAlloc.fresh_chunk_object fresh) == fresh.base)

let chunked_no_black_objects_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires chunked_no_black_objects mh /\
                MH.chunk_disjoint_from_all fresh mh)
      (ensures
        chunked_no_black_objects
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  =
  let expanded = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
  let fresh_obj = SpecMajorAlloc.fresh_chunk_object fresh in
  let aux_obj (obj: obj_addr)
    : Lemma
        (ensures
          Seq.mem obj (MH.major_objects expanded) ==>
          ~(chunked_is_black expanded obj))
    =
    if Seq.mem obj (MH.major_objects expanded) then begin
      SpecMajorAlloc.expand_major_heap_objects mh fresh fp;
      if obj == fresh_obj then
        chunked_fresh_object_not_black mh fresh fp
      else begin
        if ~(Seq.mem obj (MH.major_objects mh)) then begin
          GC.Spec.SeqMemLemmas.seq_mem_cons_not_mem_implies_eq
            fresh_obj obj (MH.major_objects mh);
          assert False
        end;
        assert (Seq.mem obj (MH.major_objects mh));
        chunked_no_black_objects_elim mh obj;
        chunked_is_black_preserved_by_expansion mh fresh fp obj;
        assert (~(chunked_is_black expanded obj))
      end
    end
  in
  FStar.Classical.forall_intro aux_obj;
  chunked_no_black_objects_intro expanded

let chunked_no_black_objects_ensure_capacity
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_no_black_objects mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh))
      (ensures
        chunked_no_black_objects
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  =
  if SpecMajorAlloc.major_fl_capacity mh fp fuel >= needed then ()
  else
    chunked_no_black_objects_preserved_by_expansion mh fresh fp

let chunked_major_minor_fields_no_infix_targets_intro
  (minor: minor_state) (mh: MH.major_heap)
  : Lemma
      (requires
        (forall (obj: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t).
          Seq.mem obj (MH.major_objects mh) /\
          ~(chunked_is_blue mh obj) /\
          ~(CG.chunked_is_no_scan mh obj) /\
          j < CG.chunked_wosize_nat_of_object mh obj /\
          CG.chunked_major_field_slot obj j == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw /\
          is_minor_pointer (to_minor_offset raw) ==>
          ~(is_infix_in_minor minor (to_minor_offset raw))))
      (ensures chunked_major_minor_fields_no_infix_targets minor mh)
  =
  reveal_opaque (`%chunked_major_minor_fields_no_infix_targets)
    (chunked_major_minor_fields_no_infix_targets minor mh)

let chunked_major_minor_fields_no_infix_targets_elim
  (minor: minor_state) (mh: MH.major_heap)
  (obj: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t)
  : Lemma
      (requires
        chunked_major_minor_fields_no_infix_targets minor mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ~(chunked_is_blue mh obj) /\
        ~(CG.chunked_is_no_scan mh obj) /\
        j < CG.chunked_wosize_nat_of_object mh obj /\
        CG.chunked_major_field_slot obj j == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw /\
        is_minor_pointer (to_minor_offset raw))
      (ensures ~(is_infix_in_minor minor (to_minor_offset raw)))
  =
  reveal_opaque (`%chunked_major_minor_fields_no_infix_targets)
    (chunked_major_minor_fields_no_infix_targets minor mh)

let chunked_is_blue_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                Seq.mem obj (MH.major_objects mh))
      (ensures
        chunked_is_blue
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        chunked_is_blue mh obj)
  =
  MH.major_object_header_disjoint_from_chunk mh fresh obj;
  SpecMajorAlloc.expand_major_heap_old_read mh fresh fp (hd_address obj)

let chunked_minor_major_fields_no_blue_preserved_by_expansion
  (minor: minor_state) (mh: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires chunked_minor_major_fields_no_blue minor mh /\
                MH.chunk_disjoint_from_all fresh mh)
      (ensures
        chunked_minor_major_fields_no_blue minor
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  =
  let expanded = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
  let aux_obj (obj: U64.t)
    : Lemma
        (ensures
          forall (j:nat).
            Seq.mem obj (minor_objects minor) /\
            j < minor_wosize minor obj /\
            is_pointer_field (minor_read_field minor obj j) ==>
            Seq.mem ((minor_read_field minor obj j) <: obj_addr)
                    (MH.major_objects expanded) /\
            ~(chunked_is_blue expanded
                ((minor_read_field minor obj j) <: obj_addr)))
    =
    let aux_j (j: nat)
      : Lemma
          (ensures
            Seq.mem obj (minor_objects minor) /\
            j < minor_wosize minor obj /\
            is_pointer_field (minor_read_field minor obj j) ==>
            Seq.mem ((minor_read_field minor obj j) <: obj_addr)
                    (MH.major_objects expanded) /\
            ~(chunked_is_blue expanded
                ((minor_read_field minor obj j) <: obj_addr)))
      =
      if Seq.mem obj (minor_objects minor) &&
         j < minor_wosize minor obj &&
         is_pointer_field (minor_read_field minor obj j)
      then begin
        let v = minor_read_field minor obj j in
        let target = (v <: obj_addr) in
        chunked_minor_major_fields_no_blue_elim minor mh obj j;
        assert (Seq.mem target (MH.major_objects mh));
        SpecMajorAlloc.expand_major_heap_old_object mh fresh fp target;
        chunked_is_blue_preserved_by_expansion mh fresh fp target;
        assert (~(chunked_is_blue expanded target))
      end
    in
    FStar.Classical.forall_intro aux_j
  in
  FStar.Classical.forall_intro aux_obj;
  chunked_minor_major_fields_no_blue_intro minor expanded

private let chunked_fresh_object_is_blue
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (ensures
        chunked_is_blue
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out
          (SpecMajorAlloc.fresh_chunk_object fresh))
  =
  SpecMajorAlloc.fresh_chunk_has_block fresh;
  SpecMajorAlloc.expand_major_heap_header_fields mh fresh fp;
  hd_f_roundtrip fresh.base;
  assert (hd_address (SpecMajorAlloc.fresh_chunk_object fresh) == fresh.base)

let chunked_major_minor_fields_no_infix_targets_preserved_by_expansion
  (minor: minor_state) (mh: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires chunked_major_minor_fields_no_infix_targets minor mh /\
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures
        chunked_major_minor_fields_no_infix_targets minor
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  =
  let expanded = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
  let fresh_obj = SpecMajorAlloc.fresh_chunk_object fresh in
  let aux_obj (obj: obj_addr)
    : Lemma
        (ensures
          forall (j:nat) (field_addr:hp_addr) (raw:U64.t).
            Seq.mem obj (MH.major_objects expanded) /\
            ~(chunked_is_blue expanded obj) /\
            ~(CG.chunked_is_no_scan expanded obj) /\
            j < CG.chunked_wosize_nat_of_object expanded obj /\
            CG.chunked_major_field_slot obj j == Some field_addr /\
            MH.read_word_in_major expanded field_addr == Some raw /\
            is_minor_pointer (to_minor_offset raw) ==>
            ~(is_infix_in_minor minor (to_minor_offset raw)))
    =
    let aux_j (j: nat)
      : Lemma
          (ensures
            forall (field_addr:hp_addr) (raw:U64.t).
              Seq.mem obj (MH.major_objects expanded) /\
              ~(chunked_is_blue expanded obj) /\
              ~(CG.chunked_is_no_scan expanded obj) /\
              j < CG.chunked_wosize_nat_of_object expanded obj /\
              CG.chunked_major_field_slot obj j == Some field_addr /\
              MH.read_word_in_major expanded field_addr == Some raw /\
              is_minor_pointer (to_minor_offset raw) ==>
              ~(is_infix_in_minor minor (to_minor_offset raw)))
      =
      let aux_field_addr (field_addr: hp_addr)
        : Lemma
            (ensures
              forall (raw:U64.t).
                Seq.mem obj (MH.major_objects expanded) /\
                ~(chunked_is_blue expanded obj) /\
                ~(CG.chunked_is_no_scan expanded obj) /\
                j < CG.chunked_wosize_nat_of_object expanded obj /\
                CG.chunked_major_field_slot obj j == Some field_addr /\
                MH.read_word_in_major expanded field_addr == Some raw /\
                is_minor_pointer (to_minor_offset raw) ==>
                ~(is_infix_in_minor minor (to_minor_offset raw)))
        =
        let aux_raw (raw: U64.t)
          : Lemma
              (ensures
                Seq.mem obj (MH.major_objects expanded) /\
                ~(chunked_is_blue expanded obj) /\
                ~(CG.chunked_is_no_scan expanded obj) /\
                j < CG.chunked_wosize_nat_of_object expanded obj /\
                CG.chunked_major_field_slot obj j == Some field_addr /\
                MH.read_word_in_major expanded field_addr == Some raw /\
                is_minor_pointer (to_minor_offset raw) ==>
                ~(is_infix_in_minor minor (to_minor_offset raw)))
          =
          if Seq.mem obj (MH.major_objects expanded) &&
             ~(chunked_is_blue expanded obj) &&
             ~(CG.chunked_is_no_scan expanded obj) &&
             j < CG.chunked_wosize_nat_of_object expanded obj &&
             CG.chunked_major_field_slot obj j == Some field_addr &&
             MH.read_word_in_major expanded field_addr == Some raw &&
             is_minor_pointer (to_minor_offset raw)
          then begin
            if obj == fresh_obj then begin
              chunked_fresh_object_is_blue mh fresh fp;
              assert False
            end else begin
              SpecMajorAlloc.expand_major_heap_objects mh fresh fp;
              if ~(Seq.mem obj (MH.major_objects mh)) then begin
                GC.Spec.SeqMemLemmas.seq_mem_cons_not_mem_implies_eq
                  fresh_obj obj (MH.major_objects mh);
                assert False
              end;
              assert (Seq.mem obj (MH.major_objects mh));
              let k = seq_mem_to_index obj (MH.major_objects mh) in
              CG.chunked_all_major_object_expansion_safe_at
                mh fresh (MH.major_objects mh) 0 k;
              CG.chunked_major_object_expansion_safe_header mh fresh obj;
              CG.chunked_major_object_expansion_safe_fields mh fresh obj;
              MH.major_object_header_disjoint_from_chunk mh fresh obj;
              chunked_is_blue_preserved_by_expansion mh fresh fp obj;
              CG.chunked_is_no_scan_preserved_by_expansion mh fresh fp obj;
              CG.chunked_wosize_nat_of_object_preserved_by_expansion
                mh fresh fp obj;
              CG.chunked_major_field_expansion_safe_at
                mh fresh obj (CG.chunked_wosize_nat_of_object mh obj)
                0 j field_addr raw;
              SpecMajorAlloc.expand_major_heap_old_read
                mh fresh fp field_addr;
              chunked_major_minor_fields_no_infix_targets_elim
                minor mh obj j field_addr raw
            end
          end
        in
        FStar.Classical.forall_intro aux_raw
      in
      FStar.Classical.forall_intro aux_field_addr
    in
    FStar.Classical.forall_intro aux_j
  in
  FStar.Classical.forall_intro aux_obj;
  chunked_major_minor_fields_no_infix_targets_intro minor expanded

let chunked_minor_major_fields_no_blue_ensure_capacity
  (minor: minor_state) (mh: MH.major_heap)
  (fp: obj_addr) (fuel needed: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_minor_major_fields_no_blue minor mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh))
      (ensures
        chunked_minor_major_fields_no_blue minor
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  =
  if SpecMajorAlloc.major_fl_capacity mh fp fuel >= needed then ()
  else
    chunked_minor_major_fields_no_blue_preserved_by_expansion
      minor mh fresh fp

let chunked_major_minor_fields_no_infix_targets_ensure_capacity
  (minor: minor_state) (mh: MH.major_heap)
  (fp: obj_addr) (fuel needed: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_major_minor_fields_no_infix_targets minor mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        chunked_major_minor_fields_no_infix_targets minor
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  =
  if SpecMajorAlloc.major_fl_capacity mh fp fuel >= needed then ()
  else
    chunked_major_minor_fields_no_infix_targets_preserved_by_expansion
      minor mh fresh fp

let chunked_no_scan_invariant_intro (mh: MH.major_heap)
  : Lemma
      (requires
        (forall (src: obj_addr) (idx: nat) (field_addr: hp_addr) (raw: U64.t).
          Seq.mem src (MH.major_objects mh) /\
          CG.chunked_is_no_scan mh src /\
          ~(chunked_is_blue mh src) /\
          idx < CG.chunked_wosize_nat_of_object mh src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw ==>
          ~(is_pointer_field raw)))
      (ensures chunked_no_scan_invariant mh)
  =
  reveal_opaque (`%chunked_no_scan_invariant)
    (chunked_no_scan_invariant mh)

let chunked_no_scan_invariant_elim
  (mh: MH.major_heap) (src: obj_addr) (idx: nat)
  (field_addr: hp_addr) (raw: U64.t)
  : Lemma
      (requires chunked_no_scan_invariant mh /\
                Seq.mem src (MH.major_objects mh) /\
                CG.chunked_is_no_scan mh src /\
                ~(chunked_is_blue mh src) /\
                idx < CG.chunked_wosize_nat_of_object mh src /\
                CG.chunked_major_field_slot src idx == Some field_addr /\
                MH.read_word_in_major mh field_addr == Some raw)
      (ensures ~(is_pointer_field raw))
  =
  reveal_opaque (`%chunked_no_scan_invariant)
    (chunked_no_scan_invariant mh)

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_no_scan_invariant_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires chunked_no_scan_invariant mh /\
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures
        chunked_no_scan_invariant
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  =
  let expanded = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
  let fresh_obj = SpecMajorAlloc.fresh_chunk_object fresh in
  let aux_src (src: obj_addr)
    : Lemma
        (ensures
          forall (idx:nat) (field_addr:hp_addr) (raw:U64.t).
            Seq.mem src (MH.major_objects expanded) /\
            CG.chunked_is_no_scan expanded src /\
            ~(chunked_is_blue expanded src) /\
            idx < CG.chunked_wosize_nat_of_object expanded src /\
            CG.chunked_major_field_slot src idx == Some field_addr /\
            MH.read_word_in_major expanded field_addr == Some raw ==>
            ~(is_pointer_field raw))
    =
    let aux_idx (idx: nat)
      : Lemma
          (ensures
            forall (field_addr:hp_addr) (raw:U64.t).
              Seq.mem src (MH.major_objects expanded) /\
              CG.chunked_is_no_scan expanded src /\
              ~(chunked_is_blue expanded src) /\
              idx < CG.chunked_wosize_nat_of_object expanded src /\
              CG.chunked_major_field_slot src idx == Some field_addr /\
              MH.read_word_in_major expanded field_addr == Some raw ==>
              ~(is_pointer_field raw))
      =
      let aux_field_addr (field_addr: hp_addr)
        : Lemma
            (ensures
              forall (raw:U64.t).
                Seq.mem src (MH.major_objects expanded) /\
                CG.chunked_is_no_scan expanded src /\
                ~(chunked_is_blue expanded src) /\
                idx < CG.chunked_wosize_nat_of_object expanded src /\
                CG.chunked_major_field_slot src idx == Some field_addr /\
                MH.read_word_in_major expanded field_addr == Some raw ==>
                ~(is_pointer_field raw))
        =
        let aux_raw (raw: U64.t)
          : Lemma
              (ensures
                Seq.mem src (MH.major_objects expanded) /\
                CG.chunked_is_no_scan expanded src /\
                ~(chunked_is_blue expanded src) /\
                idx < CG.chunked_wosize_nat_of_object expanded src /\
                CG.chunked_major_field_slot src idx == Some field_addr /\
                MH.read_word_in_major expanded field_addr == Some raw ==>
                ~(is_pointer_field raw))
          =
          if Seq.mem src (MH.major_objects expanded) &&
             CG.chunked_is_no_scan expanded src &&
             ~(chunked_is_blue expanded src) &&
             idx < CG.chunked_wosize_nat_of_object expanded src &&
             CG.chunked_major_field_slot src idx == Some field_addr &&
             MH.read_word_in_major expanded field_addr == Some raw
          then begin
            if src == fresh_obj then begin
              chunked_fresh_object_is_blue mh fresh fp;
              assert False
            end else begin
              SpecMajorAlloc.expand_major_heap_objects mh fresh fp;
              if ~(Seq.mem src (MH.major_objects mh)) then begin
                GC.Spec.SeqMemLemmas.seq_mem_cons_not_mem_implies_eq
                  fresh_obj src (MH.major_objects mh);
                assert False
              end;
              assert (Seq.mem src (MH.major_objects mh));
              let k = seq_mem_to_index src (MH.major_objects mh) in
              CG.chunked_all_major_object_expansion_safe_at
                mh fresh (MH.major_objects mh) 0 k;
              CG.chunked_major_object_expansion_safe_header mh fresh src;
              CG.chunked_major_object_expansion_safe_fields mh fresh src;
              MH.major_object_header_disjoint_from_chunk mh fresh src;
              chunked_is_blue_preserved_by_expansion mh fresh fp src;
              CG.chunked_is_no_scan_preserved_by_expansion mh fresh fp src;
              CG.chunked_wosize_nat_of_object_preserved_by_expansion
                mh fresh fp src;
              CG.chunked_major_field_expansion_safe_at
                mh fresh src (CG.chunked_wosize_nat_of_object mh src)
                0 idx field_addr raw;
              SpecMajorAlloc.expand_major_heap_old_read
                mh fresh fp field_addr;
              chunked_no_scan_invariant_elim mh src idx field_addr raw
            end
          end
        in
        FStar.Classical.forall_intro aux_raw
      in
      FStar.Classical.forall_intro aux_field_addr
    in
    FStar.Classical.forall_intro aux_idx
  in
  FStar.Classical.forall_intro aux_src;
  chunked_no_scan_invariant_intro expanded
#pop-options

let chunked_no_scan_invariant_ensure_capacity
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_no_scan_invariant mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        chunked_no_scan_invariant
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  =
  if SpecMajorAlloc.major_fl_capacity mh fp fuel >= needed then ()
  else
    chunked_no_scan_invariant_preserved_by_expansion mh fresh fp

let chunked_no_pointer_to_blue_intro (mh: MH.major_heap)
  : Lemma
      (requires
        (forall (src: obj_addr) (dst: obj_addr) (idx: nat)
                (field_addr: hp_addr) (raw: U64.t).
          Seq.mem src (MH.major_objects mh) /\
          ~(chunked_is_blue mh src) /\
          idx < CG.chunked_wosize_nat_of_object mh src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw /\
          Seq.mem dst (MH.major_objects mh) /\
          is_pointer_to raw dst ==>
          ~(chunked_is_blue mh dst)))
      (ensures chunked_no_pointer_to_blue mh)
  =
  reveal_opaque (`%chunked_no_pointer_to_blue)
    (chunked_no_pointer_to_blue mh)

let chunked_no_pointer_to_blue_elim
  (mh: MH.major_heap) (src: obj_addr) (dst: obj_addr) (idx: nat)
  (field_addr: hp_addr) (raw: U64.t)
  : Lemma
      (requires chunked_no_pointer_to_blue mh /\
                Seq.mem src (MH.major_objects mh) /\
                ~(chunked_is_blue mh src) /\
                idx < CG.chunked_wosize_nat_of_object mh src /\
                CG.chunked_major_field_slot src idx == Some field_addr /\
                MH.read_word_in_major mh field_addr == Some raw /\
                Seq.mem dst (MH.major_objects mh) /\
                is_pointer_to raw dst)
      (ensures ~(chunked_is_blue mh dst))
  =
  reveal_opaque (`%chunked_no_pointer_to_blue)
    (chunked_no_pointer_to_blue mh)

let chunked_chain_objects_blue_intro
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Lemma
      (requires
        (forall (obj: obj_addr).
          Seq.mem obj (MH.major_objects mh) /\
          ~(chunked_is_blue mh obj) ==>
          SpecMajorAlloc.major_fl_chain_avoids mh fp obj fuel = true))
      (ensures chunked_chain_objects_blue mh fp fuel)
  =
  reveal_opaque (`%chunked_chain_objects_blue)
    (chunked_chain_objects_blue mh fp fuel)

let chunked_chain_objects_blue_elim
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat) (obj: obj_addr)
  : Lemma
      (requires chunked_chain_objects_blue mh fp fuel /\
                Seq.mem obj (MH.major_objects mh) /\
                ~(chunked_is_blue mh obj))
      (ensures
        SpecMajorAlloc.major_fl_chain_avoids mh fp obj fuel = true)
  =
  reveal_opaque (`%chunked_chain_objects_blue)
    (chunked_chain_objects_blue mh fp fuel)

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_chain_objects_blue_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires chunked_chain_objects_blue mh fp fuel /\
                MH.well_formed_major_heap mh /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                MH.chunk_disjoint_from_all fresh mh)
      (ensures
        (let r = SpecMajorAlloc.expand_major_heap mh fresh fp in
         chunked_chain_objects_blue r.major_out r.fp_out (fuel + 1)))
  =
  let r = SpecMajorAlloc.expand_major_heap mh fresh fp in
  let expanded = r.major_out in
  let fresh_obj = SpecMajorAlloc.fresh_chunk_object fresh in
  let aux (obj: obj_addr)
    : Lemma
        (requires Seq.mem obj (MH.major_objects expanded) /\
                  ~(chunked_is_blue expanded obj))
        (ensures
          SpecMajorAlloc.major_fl_chain_avoids
            expanded r.fp_out obj (fuel + 1) = true)
    =
    SpecMajorAlloc.expand_major_heap_objects mh fresh fp;
    if obj = fresh_obj then begin
      chunked_fresh_object_is_blue mh fresh fp;
      assert False
    end else begin
      if ~(Seq.mem obj (MH.major_objects mh)) then begin
        GC.Spec.SeqMemLemmas.seq_mem_cons_not_mem_implies_eq
          fresh_obj obj (MH.major_objects mh);
        assert False
      end;
      assert (Seq.mem obj (MH.major_objects mh));
      chunked_is_blue_preserved_by_expansion mh fresh fp obj;
      assert (~(chunked_is_blue mh obj));
      chunked_chain_objects_blue_elim mh fp fuel obj;
      let old_link_frame (src: obj_addr)
        : Lemma
            (requires
              Seq.mem src (MH.major_objects mh) /\
              src <> obj /\
              (match MH.read_word_in_major mh (hd_address src) with
               | Some hdr -> U64.v (getWosize hdr) >= 1
               | None -> False))
            (ensures
              MH.read_word_in_major expanded src ==
              MH.read_word_in_major mh src)
        =
        match MH.read_word_in_major mh (hd_address src) with
        | None -> assert False
        | Some hdr ->
          MH.major_objects_member_field0_read_some mh src hdr;
          match MH.read_word_in_major mh src with
          | None -> assert False
          | Some old ->
            MH.read_word_in_major_lookup_index mh src old;
            let idx = MH.lookup_chunk_index_value mh src in
            assert (idx < Seq.length mh);
            assert (MH.lookup_chunk_index mh src == Some idx);
            MH.lookup_chunk_index_some mh src idx;
            assert (MH.lookup_chunk mh src == Some (Seq.index mh idx));
            MH.lookup_chunk_some_disjoint_miss
              mh (Seq.index mh idx) fresh src;
            SpecMajorAlloc.expand_major_heap_old_read mh fresh fp src
      in
      FStar.Classical.forall_intro
        (FStar.Classical.move_requires old_link_frame);
      SpecMajorAlloc.major_fl_chain_avoids_transfer
        mh expanded fp obj fuel;
      SpecMajorAlloc.expand_major_heap_link mh fresh fp;
      SpecMajorAlloc.fresh_chunk_object_in_chunk fresh;
      assert (r.fp_out == fresh_obj);
      assert (r.fp_out <> obj);
      assert (fuel + 1 > 0);
      assert (U64.v r.fp_out >= U64.v mword);
      assert (U64.v r.fp_out < heap_size);
      assert (U64.v r.fp_out % U64.v mword == 0);
      assert (MH.read_word_in_major expanded (r.fp_out <: obj_addr) ==
              Some fp);
      assert
        (match MH.read_word_in_major expanded (r.fp_out <: obj_addr) with
         | Some next ->
           SpecMajorAlloc.major_fl_chain_avoids expanded next obj fuel = true
         | None -> True);
      SpecMajorAlloc.major_fl_chain_avoids_step
        expanded r.fp_out obj (fuel + 1)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  chunked_chain_objects_blue_intro expanded r.fp_out (fuel + 1)
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_chain_objects_blue_ensure_head_capacity
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_chain_objects_blue mh fp fuel /\
                MH.well_formed_major_heap mh /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh))
      (ensures
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
         chunked_chain_objects_blue
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))
  =
  if SpecMajorAlloc.major_fl_head_wosize mh fp >= needed then
    ()
  else
    chunked_chain_objects_blue_preserved_by_expansion
      mh fresh fp fuel
#pop-options

private let pointer_to_fresh_object_in_fresh_chunk
  (fresh: MH.heap_chunk) (raw: U64.t)
  : Lemma
      (requires is_pointer_to raw (SpecMajorAlloc.fresh_chunk_object fresh))
      (ensures MH.pointer_in_chunk fresh raw)
  =
  let fresh_obj = SpecMajorAlloc.fresh_chunk_object fresh in
  if is_pointer_field raw then begin
    SpecMajorAlloc.fresh_chunk_object_in_chunk fresh;
    hd_address_bounds (raw <: obj_addr);
    f_hd_roundtrip (raw <: obj_addr);
    hd_f_roundtrip fresh.base;
    assert (hd_address raw == hd_address fresh_obj);
    assert (hd_address fresh_obj == fresh.base);
    assert (f_address (hd_address raw) == (raw <: obj_addr));
    assert (f_address (hd_address fresh_obj) == fresh_obj);
    assert ((raw <: obj_addr) == fresh_obj);
    assert (raw == fresh_obj);
    assert (MH.pointer_in_chunk fresh raw)
  end else
    assert False

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_no_pointer_to_blue_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires chunked_no_pointer_to_blue mh /\
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures
        chunked_no_pointer_to_blue
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  =
  let expanded = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
  let fresh_obj = SpecMajorAlloc.fresh_chunk_object fresh in
  let aux_src (src: obj_addr)
    : Lemma
        (ensures
          forall (dst:obj_addr) (idx:nat) (field_addr:hp_addr) (raw:U64.t).
            Seq.mem src (MH.major_objects expanded) /\
            ~(chunked_is_blue expanded src) /\
            idx < CG.chunked_wosize_nat_of_object expanded src /\
            CG.chunked_major_field_slot src idx == Some field_addr /\
            MH.read_word_in_major expanded field_addr == Some raw /\
            Seq.mem dst (MH.major_objects expanded) /\
            is_pointer_to raw dst ==>
            ~(chunked_is_blue expanded dst))
    =
    let aux_dst (dst: obj_addr)
      : Lemma
          (ensures
            forall (idx:nat) (field_addr:hp_addr) (raw:U64.t).
              Seq.mem src (MH.major_objects expanded) /\
              ~(chunked_is_blue expanded src) /\
              idx < CG.chunked_wosize_nat_of_object expanded src /\
              CG.chunked_major_field_slot src idx == Some field_addr /\
              MH.read_word_in_major expanded field_addr == Some raw /\
              Seq.mem dst (MH.major_objects expanded) /\
              is_pointer_to raw dst ==>
              ~(chunked_is_blue expanded dst))
      =
      let aux_idx (idx: nat)
        : Lemma
            (ensures
              forall (field_addr:hp_addr) (raw:U64.t).
                Seq.mem src (MH.major_objects expanded) /\
                ~(chunked_is_blue expanded src) /\
                idx < CG.chunked_wosize_nat_of_object expanded src /\
                CG.chunked_major_field_slot src idx == Some field_addr /\
                MH.read_word_in_major expanded field_addr == Some raw /\
                Seq.mem dst (MH.major_objects expanded) /\
                is_pointer_to raw dst ==>
                ~(chunked_is_blue expanded dst))
        =
        let aux_field_addr (field_addr: hp_addr)
          : Lemma
              (ensures
                forall (raw:U64.t).
                  Seq.mem src (MH.major_objects expanded) /\
                  ~(chunked_is_blue expanded src) /\
                  idx < CG.chunked_wosize_nat_of_object expanded src /\
                  CG.chunked_major_field_slot src idx == Some field_addr /\
                  MH.read_word_in_major expanded field_addr == Some raw /\
                  Seq.mem dst (MH.major_objects expanded) /\
                  is_pointer_to raw dst ==>
                  ~(chunked_is_blue expanded dst))
          =
          let aux_raw (raw: U64.t)
            : Lemma
                (ensures
                  Seq.mem src (MH.major_objects expanded) /\
                  ~(chunked_is_blue expanded src) /\
                  idx < CG.chunked_wosize_nat_of_object expanded src /\
                  CG.chunked_major_field_slot src idx == Some field_addr /\
                  MH.read_word_in_major expanded field_addr == Some raw /\
                  Seq.mem dst (MH.major_objects expanded) /\
                  is_pointer_to raw dst ==>
                  ~(chunked_is_blue expanded dst))
            =
            if Seq.mem src (MH.major_objects expanded) &&
               ~(chunked_is_blue expanded src) &&
               idx < CG.chunked_wosize_nat_of_object expanded src &&
               CG.chunked_major_field_slot src idx == Some field_addr &&
               MH.read_word_in_major expanded field_addr == Some raw &&
               Seq.mem dst (MH.major_objects expanded) &&
               is_pointer_to raw dst
            then begin
              if src == fresh_obj then begin
                chunked_fresh_object_is_blue mh fresh fp;
                assert False
              end else begin
                SpecMajorAlloc.expand_major_heap_objects mh fresh fp;
                if ~(Seq.mem src (MH.major_objects mh)) then begin
                  GC.Spec.SeqMemLemmas.seq_mem_cons_not_mem_implies_eq
                    fresh_obj src (MH.major_objects mh);
                  assert False
                end;
                assert (Seq.mem src (MH.major_objects mh));
                let k = seq_mem_to_index src (MH.major_objects mh) in
                CG.chunked_all_major_object_expansion_safe_at
                  mh fresh (MH.major_objects mh) 0 k;
                CG.chunked_major_object_expansion_safe_header mh fresh src;
                CG.chunked_major_object_expansion_safe_fields mh fresh src;
                MH.major_object_header_disjoint_from_chunk mh fresh src;
                chunked_is_blue_preserved_by_expansion mh fresh fp src;
                CG.chunked_wosize_nat_of_object_preserved_by_expansion
                  mh fresh fp src;
                CG.chunked_major_field_expansion_safe_at
                  mh fresh src (CG.chunked_wosize_nat_of_object mh src)
                  0 idx field_addr raw;
                SpecMajorAlloc.expand_major_heap_old_read
                  mh fresh fp field_addr;
                assert (MH.read_word_in_major mh field_addr == Some raw);
                if dst == fresh_obj then begin
                  pointer_to_fresh_object_in_fresh_chunk fresh raw;
                  assert False
                end else begin
                  if ~(Seq.mem dst (MH.major_objects mh)) then begin
                    GC.Spec.SeqMemLemmas.seq_mem_cons_not_mem_implies_eq
                      fresh_obj dst (MH.major_objects mh);
                    assert False
                  end;
                  assert (Seq.mem dst (MH.major_objects mh));
                  chunked_no_pointer_to_blue_elim
                    mh src dst idx field_addr raw;
                  chunked_is_blue_preserved_by_expansion mh fresh fp dst;
                  assert (~(chunked_is_blue expanded dst))
                end
              end
            end
          in
          FStar.Classical.forall_intro aux_raw
        in
        FStar.Classical.forall_intro aux_field_addr
      in
      FStar.Classical.forall_intro aux_idx
    in
    FStar.Classical.forall_intro aux_dst
  in
  FStar.Classical.forall_intro aux_src;
  chunked_no_pointer_to_blue_intro expanded
#pop-options

let chunked_no_pointer_to_blue_ensure_capacity
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_no_pointer_to_blue mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        chunked_no_pointer_to_blue
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  =
  if SpecMajorAlloc.major_fl_capacity mh fp fuel >= needed then ()
  else
    chunked_no_pointer_to_blue_preserved_by_expansion mh fresh fp

let chunked_collection_heap_shape_intro
  (minor: minor_state) (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Lemma
      (requires chunked_major_alloc_shape mh fp fuel /\
                chunked_no_black_objects mh /\
                chunked_no_scan_invariant mh /\
                chunked_no_pointer_to_blue mh /\
                minor_heap_shape minor /\
                chunked_minor_major_fields_no_blue minor mh /\
                chunked_major_minor_fields_no_infix_targets minor mh)
      (ensures chunked_collection_heap_shape minor mh fp fuel)
  =
  reveal_opaque (`%chunked_collection_heap_shape)
    (chunked_collection_heap_shape minor mh fp fuel)

let chunked_collection_heap_shape_elim
  (minor: minor_state) (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Lemma
      (requires chunked_collection_heap_shape minor mh fp fuel)
      (ensures chunked_major_alloc_shape mh fp fuel /\
               chunked_no_black_objects mh /\
               chunked_no_scan_invariant mh /\
               chunked_no_pointer_to_blue mh /\
               minor_heap_shape minor /\
               chunked_minor_major_fields_no_blue minor mh /\
               chunked_major_minor_fields_no_infix_targets minor mh)
  =
  reveal_opaque (`%chunked_collection_heap_shape)
    (chunked_collection_heap_shape minor mh fp fuel)

let chunked_collection_heap_shape_preserved_by_expansion
  (minor: minor_state) (mh: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: obj_addr) (fuel: nat)
  : Lemma
      (requires chunked_collection_heap_shape minor mh fp fuel /\
                MH.chunk_disjoint_from_all fresh mh /\
                fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                U64.v fresh.base >= U64.v zero_addr /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures (
        let r = SpecMajorAlloc.expand_major_heap mh fresh fp in
        chunked_collection_heap_shape minor r.major_out r.fp_out (fuel + 1)))
  =
  chunked_collection_heap_shape_elim minor mh fp fuel;
  chunked_major_alloc_shape_preserved_by_expansion mh fresh fp fuel;
  chunked_no_black_objects_preserved_by_expansion mh fresh fp;
  chunked_no_scan_invariant_preserved_by_expansion mh fresh fp;
  chunked_no_pointer_to_blue_preserved_by_expansion mh fresh fp;
  chunked_minor_major_fields_no_blue_preserved_by_expansion
    minor mh fresh fp;
  chunked_major_minor_fields_no_infix_targets_preserved_by_expansion
    minor mh fresh fp;
  let r = SpecMajorAlloc.expand_major_heap mh fresh fp in
  chunked_collection_heap_shape_intro minor r.major_out r.fp_out (fuel + 1)

let chunked_collection_heap_shape_ensure_capacity
  (minor: minor_state) (mh: MH.major_heap)
  (fp: obj_addr) (fuel needed: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_collection_heap_shape minor mh fp fuel /\
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
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_capacity
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out >= needed))
  =
  chunked_collection_heap_shape_elim minor mh fp fuel;
  chunked_major_alloc_shape_ensure_capacity mh fp fuel needed fresh;
  chunked_no_black_objects_ensure_capacity mh fp fuel needed fresh;
  chunked_no_scan_invariant_ensure_capacity mh fp fuel needed fresh;
  chunked_no_pointer_to_blue_ensure_capacity mh fp fuel needed fresh;
  chunked_minor_major_fields_no_blue_ensure_capacity
    minor mh fp fuel needed fresh;
  chunked_major_minor_fields_no_infix_targets_ensure_capacity
    minor mh fp fuel needed fresh;
  let r = SpecMajorAlloc.ensure_major_capacity_spec mh fp fuel needed fresh in
  chunked_collection_heap_shape_intro
    minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out

private let chunked_no_black_objects_ensure_head_capacity
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_no_black_objects mh /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh))
      (ensures
        chunked_no_black_objects
          (SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  =
  if SpecMajorAlloc.major_fl_head_wosize mh fp >= needed then ()
  else
    chunked_no_black_objects_preserved_by_expansion mh fresh fp

private let chunked_minor_major_fields_no_blue_ensure_head_capacity
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_minor_major_fields_no_blue minor mh /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh))
      (ensures
        chunked_minor_major_fields_no_blue minor
          (SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  =
  if SpecMajorAlloc.major_fl_head_wosize mh fp >= needed then ()
  else
    chunked_minor_major_fields_no_blue_preserved_by_expansion
      minor mh fresh fp

private let chunked_major_minor_fields_no_infix_targets_ensure_head_capacity
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_major_minor_fields_no_infix_targets minor mh /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        chunked_major_minor_fields_no_infix_targets minor
          (SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  =
  if SpecMajorAlloc.major_fl_head_wosize mh fp >= needed then ()
  else
    chunked_major_minor_fields_no_infix_targets_preserved_by_expansion
      minor mh fresh fp

private let chunked_no_scan_invariant_ensure_head_capacity
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_no_scan_invariant mh /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        chunked_no_scan_invariant
          (SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  =
  if SpecMajorAlloc.major_fl_head_wosize mh fp >= needed then ()
  else
    chunked_no_scan_invariant_preserved_by_expansion mh fresh fp

private let chunked_no_pointer_to_blue_ensure_head_capacity
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_no_pointer_to_blue mh /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        chunked_no_pointer_to_blue
          (SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  =
  if SpecMajorAlloc.major_fl_head_wosize mh fp >= needed then ()
  else
    chunked_no_pointer_to_blue_preserved_by_expansion mh fresh fp

let chunked_collection_heap_shape_ensure_head_capacity
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_collection_heap_shape minor mh fp fuel /\
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
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed))
  =
  chunked_collection_heap_shape_elim minor mh fp fuel;
  chunked_major_alloc_shape_ensure_head_capacity mh fp fuel needed fresh;
  chunked_no_black_objects_ensure_head_capacity mh fp fuel needed fresh;
  chunked_no_scan_invariant_ensure_head_capacity mh fp fuel needed fresh;
  chunked_no_pointer_to_blue_ensure_head_capacity mh fp fuel needed fresh;
  chunked_minor_major_fields_no_blue_ensure_head_capacity
    minor mh fp fuel needed fresh;
  chunked_major_minor_fields_no_infix_targets_ensure_head_capacity
    minor mh fp fuel needed fresh;
  let r = SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
  chunked_collection_heap_shape_intro
    minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out

let chunked_collection_heap_shape_ensure_head_capacity_with_chain
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires chunked_collection_heap_shape minor mh fp fuel /\
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
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        SpecMajorAlloc.major_fl_chain_terminates
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out = true))
  =
  chunked_collection_heap_shape_ensure_head_capacity
    minor mh fp fuel needed fresh;
  chunked_collection_heap_shape_elim minor mh fp fuel;
  chunked_major_alloc_shape_elim mh fp fuel;
  assert (SpecMajorAlloc.major_fl_chain_terminates mh fp fuel);
  SpecMajorAlloc.ensure_major_head_capacity_fl_chain_terminates
    mh fp fuel needed fresh

let chunked_collection_heap_shape_ensure_head_capacity_alloc_no_oom
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (requested_wz: nat)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires fuel > 0 /\
                chunked_collection_heap_shape minor mh fp fuel /\
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
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.major_obj_out == r.capacity_fp_out /\
        a.major_obj_out <> 0UL))
  =
  let needed = SpecMajorAlloc.major_alloc_demand_wosize requested_wz in
  chunked_collection_heap_shape_ensure_head_capacity
    minor mh fp fuel needed fresh;
  chunked_collection_heap_shape_elim minor mh fp fuel;
  chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAlloc.ensure_major_head_capacity_alloc_no_oom
    mh fp fuel requested_wz fresh

let chunked_collection_heap_shape_ensure_head_capacity_alloc_list_with_budget
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (fresh: MH.heap_chunk)
  (requests: list nat) (budget: nat)
  : Lemma
      (requires fuel > 1 /\
                chunked_collection_heap_shape minor mh fp fuel /\
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
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))
  =
  let needed = budget + 1 in
  assert (needed > 0);
  chunked_collection_heap_shape_ensure_head_capacity
    minor mh fp fuel needed fresh;
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      mh fp fuel needed fresh in
  assert (SpecMajorAlloc.major_fl_head_wosize
            r.capacity_major_out r.capacity_fp_out >= needed);
  assert (SpecMajorAlloc.major_fl_head_wosize
            r.capacity_major_out r.capacity_fp_out > 0);
  if r.capacity_fp_out = 0UL then
    assert (SpecMajorAlloc.major_fl_head_wosize
              r.capacity_major_out r.capacity_fp_out == 0);
  assert (r.capacity_fp_out <> 0UL);
  assert (r.capacity_fuel_out > 1);
  chunked_collection_heap_shape_elim
    minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out;
  chunked_major_alloc_shape_alloc_list_head_split_with_budget
    r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
    requests budget

let chunked_collection_heap_shape_ensure_minor_promotion_budget_alloc_list
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (fresh: MH.heap_chunk)
  (requests: list nat)
  : Lemma
      (requires fuel > 1 /\
                chunked_collection_heap_shape minor mh fp fuel /\
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
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))
  =
  chunked_collection_heap_shape_ensure_head_capacity_alloc_list_with_budget
    minor mh fp fuel fresh requests
    (PromotionDemand.minor_promotion_demand minor)

let chunked_collection_heap_shape_ensure_minor_promotion_head_capacity_allocs
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires fuel > 1 /\
                chunked_collection_heap_shape minor mh fp fuel /\
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
        chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))
  =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  assert (needed > 0);
  chunked_collection_heap_shape_ensure_head_capacity
    minor mh fp fuel needed fresh;
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      mh fp fuel needed fresh in
  assert (SpecMajorAlloc.major_fl_head_wosize
            r.capacity_major_out r.capacity_fp_out >= needed);
  assert (SpecMajorAlloc.major_fl_head_wosize
            r.capacity_major_out r.capacity_fp_out > 0);
  if r.capacity_fp_out = 0UL then
    assert (SpecMajorAlloc.major_fl_head_wosize
              r.capacity_major_out r.capacity_fp_out == 0);
  assert (r.capacity_fp_out <> 0UL);
  assert (r.capacity_fuel_out > 1);
  chunked_collection_heap_shape_elim
    minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out;
  reveal_opaque (`%minor_heap_shape) (minor_heap_shape minor);
  assert (minor_wf minor);
  chunked_major_alloc_shape_alloc_minor_objects_head_split
    minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out

let minor_heap_shape_elim (minor: minor_state)
  : Lemma (requires minor_heap_shape minor)
          (ensures minor_wf minor /\
                   minor_guards_complete minor /\
                   minor_infix_wf minor /\
                   minor_no_scan_invariant minor /\
                   minor_fields_no_infix_targets minor)
  = reveal_opaque (`%minor_heap_shape) (minor_heap_shape minor)

let minor_fields_no_infix_targets_intro (minor: minor_state)
  : Lemma (requires
            (forall (obj: U64.t) (j: nat).
              Seq.mem obj (minor_objects minor) /\
              j < minor_wosize minor obj /\
              is_minor_pointer (to_minor_offset (minor_read_field minor obj j)) ==>
              ~(is_infix_in_minor minor
                  (to_minor_offset (minor_read_field minor obj j)))))
          (ensures minor_fields_no_infix_targets minor)
  = reveal_opaque (`%minor_fields_no_infix_targets)
      (minor_fields_no_infix_targets minor)

let minor_heap_shape_intro (minor: minor_state)
  : Lemma (requires minor_wf minor /\
                   minor_guards_complete minor /\
                   minor_infix_wf minor /\
                   minor_no_scan_invariant minor /\
                   minor_fields_no_infix_targets minor)
          (ensures minor_heap_shape minor)
  = reveal_opaque (`%minor_heap_shape) (minor_heap_shape minor)

let minor_major_fields_no_blue_intro (minor: minor_state) (major: heap)
  : Lemma (requires
            (forall (obj: U64.t) (j: nat).
              Seq.mem obj (minor_objects minor) /\
              j < minor_wosize minor obj /\
              is_pointer_field (minor_read_field minor obj j) ==>
              Seq.mem ((minor_read_field minor obj j) <: obj_addr)
                     (objects zero_addr major) /\
              ~(is_blue ((minor_read_field minor obj j) <: obj_addr) major)))
          (ensures minor_major_fields_no_blue minor major)
  = reveal_opaque (`%minor_major_fields_no_blue)
      (minor_major_fields_no_blue minor major)

let minor_major_fields_no_blue_no_pointer_fields
  (minor: minor_state) (major: heap)
  : Lemma
      (requires
        (forall (obj:U64.t) (j:nat).
          Seq.mem obj (minor_objects minor) /\
          j < minor_wosize minor obj ==>
          ~(is_pointer_field (minor_read_field minor obj j))))
      (ensures minor_major_fields_no_blue minor major)
  =
  reveal_opaque (`%minor_major_fields_no_blue)
    (minor_major_fields_no_blue minor major)

let minor_major_fields_no_blue_elim (minor: minor_state) (major: heap)
  (obj: U64.t) (j: nat)
  : Lemma (requires minor_major_fields_no_blue minor major /\
                     Seq.mem obj (minor_objects minor) /\
                     j < minor_wosize minor obj /\
                     is_pointer_field (minor_read_field minor obj j))
          (ensures Seq.mem ((minor_read_field minor obj j) <: obj_addr)
                            (objects zero_addr major) /\
                   ~(is_blue ((minor_read_field minor obj j) <: obj_addr) major))
  = reveal_opaque (`%minor_major_fields_no_blue)
      (minor_major_fields_no_blue minor major)

let minor_fields_no_infix_targets_elim (minor: minor_state)
  (obj: U64.t) (j: nat)
  : Lemma (requires minor_fields_no_infix_targets minor /\
                     Seq.mem obj (minor_objects minor) /\
                     j < minor_wosize minor obj /\
                     is_minor_pointer (to_minor_offset (minor_read_field minor obj j)))
          (ensures ~(is_infix_in_minor minor
                      (to_minor_offset (minor_read_field minor obj j))))
  = reveal_opaque (`%minor_fields_no_infix_targets)
      (minor_fields_no_infix_targets minor)

let major_minor_fields_no_infix_targets_elim
  (minor: minor_state) (major: heap) (obj: obj_addr) (j: nat)
  : Lemma (requires major_minor_fields_no_infix_targets minor major /\
                     Seq.mem obj (objects zero_addr major) /\
                     ~(is_blue obj major) /\
                     ~(is_no_scan obj major) /\
                     j < U64.v (wosize_of_object obj major) /\
                     U64.v obj + j * 8 + 8 <= heap_size /\
                     (U64.v obj + j * 8) % 8 == 0 /\
                     (let v = to_minor_offset
                        (read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
                      is_minor_pointer v))
          (ensures (let v = to_minor_offset
                        (read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
                    ~(is_infix_in_minor minor v)))
  = reveal_opaque (`%major_minor_fields_no_infix_targets)
      (major_minor_fields_no_infix_targets minor major)

let major_minor_fields_no_infix_targets_intro
  (minor: minor_state) (major: heap)
  : Lemma (requires
            (forall (obj: obj_addr) (j: nat).
              Seq.mem obj (objects zero_addr major) /\
              ~(is_blue obj major) /\
              ~(is_no_scan obj major) /\
              j < U64.v (wosize_of_object obj major) /\
              U64.v obj + j * 8 + 8 <= heap_size /\
              (U64.v obj + j * 8) % 8 == 0 ==>
              (let v = to_minor_offset
                 (read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
               is_minor_pointer v ==> ~(is_infix_in_minor minor v))))
          (ensures major_minor_fields_no_infix_targets minor major)
  = reveal_opaque (`%major_minor_fields_no_infix_targets)
      (major_minor_fields_no_infix_targets minor major)

let major_stack_shape_elim (major: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires major_stack_shape major st cap)
          (ensures MarkBoundedInv.bounded_mark_inv major st cap /\
                   Mark.root_props major st /\
                   gray_black_objects_on_stack major st /\
                   (let graph = HeapModel.create_graph major in
                    let roots' = HeapGraph.coerce_to_vertex_list st in
                     Graph.graph_wf graph /\ Graph.is_vertex_set roots' /\
                     Graph.subset_vertices roots' graph.vertices))
  = reveal_opaque (`%major_stack_shape) (major_stack_shape major st cap)

let major_stack_shape_intro (major: heap) (st: seq obj_addr) (cap: nat)
  : Lemma (requires MarkBoundedInv.bounded_mark_inv major st cap /\
                    Mark.root_props major st /\
                    gray_black_objects_on_stack major st /\
                    (let graph = HeapModel.create_graph major in
                     let roots' = HeapGraph.coerce_to_vertex_list st in
                     Graph.graph_wf graph /\ Graph.is_vertex_set roots' /\
                     Graph.subset_vertices roots' graph.vertices))
          (ensures major_stack_shape major st cap)
  = reveal_opaque (`%major_stack_shape) (major_stack_shape major st cap)

let collection_heap_shape_elim (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires collection_heap_shape minor major fp)
          (ensures major_heap_shape major fp /\
                   minor_heap_shape minor /\
                   minor_major_fields_no_blue minor major /\
                   major_minor_fields_no_infix_targets minor major)
  = reveal_opaque (`%collection_heap_shape)
      (collection_heap_shape minor major fp)

let collection_heap_shape_intro (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires major_heap_shape major fp /\
                    minor_heap_shape minor /\
                    minor_major_fields_no_blue minor major /\
                    major_minor_fields_no_infix_targets minor major)
          (ensures collection_heap_shape minor major fp)
  = reveal_opaque (`%collection_heap_shape)
      (collection_heap_shape minor major fp)

let full_heap_shape_elim (minor: minor_state) (major: heap) (fp: U64.t)
                         (st: seq obj_addr) (cap: nat)
  : Lemma (requires full_heap_shape minor major fp st cap)
           (ensures collection_heap_shape minor major fp /\
                    major_stack_shape major st cap)
  = reveal_opaque (`%full_heap_shape)
      (full_heap_shape minor major fp st cap)

let full_heap_shape_intro (minor: minor_state) (major: heap) (fp: U64.t)
                          (st: seq obj_addr) (cap: nat)
  : Lemma (requires collection_heap_shape minor major fp /\
                    major_stack_shape major st cap)
          (ensures full_heap_shape minor major fp st cap)
  = reveal_opaque (`%full_heap_shape)
      (full_heap_shape minor major fp st cap)

/// ---------------------------------------------------------------------------
/// Minor reset shape
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --split_queries always"
private let minor_reset_guards_complete (minor: minor_state)
  : Lemma (ensures minor_guards_complete (minor_reset minor))
  =
  let reset = minor_reset minor in
  let aux (addr: U64.t)
    : Lemma (requires U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\
                      U64.v addr % 8 == 0 /\
                      minor_wosize reset addr > 0 /\
                      U64.v addr + minor_wosize reset addr * 8 <= minor_heap_size /\
                      minor_tag reset addr <> 249)
            (ensures Seq.mem addr (minor_objects reset))
    =
    minor_reset_wosize_zero minor addr;
    assert False
  in
  reveal_opaque (`%minor_guards_complete) (minor_guards_complete reset);
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

private let minor_reset_infix_wf (minor: minor_state)
  : Lemma (ensures minor_infix_wf (minor_reset minor))
  =
  let reset = minor_reset minor in
  let aux (addr: U64.t)
    : Lemma (requires is_infix_in_minor reset addr)
            (ensures (let wz = minor_wosize reset addr in
                      let parent = infix_parent reset addr in
                      wz > 0 /\
                      wz * 8 <= U64.v addr - 8 /\
                      U64.v parent >= 8 /\
                      U64.v parent % 8 == 0 /\
                      Seq.mem parent (minor_objects reset) /\
                      U64.v addr - U64.v parent < minor_wosize reset parent * 8))
    =
    minor_reset_no_infix minor addr;
    assert False
  in
  reveal_opaque (`%minor_infix_wf) (minor_infix_wf reset);
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

private let minor_reset_no_scan_invariant (minor: minor_state)
  : Lemma (ensures minor_no_scan_invariant (minor_reset minor))
  =
  let reset = minor_reset minor in
  minor_reset_objects_empty minor;
  assert (minor_objects reset == Seq.empty);
  let aux (obj: U64.t) (j: nat)
    : Lemma (ensures (Seq.mem obj (minor_objects reset) /\
                      minor_tag reset obj >= 251 /\
                      j < minor_wosize reset obj ==>
                      ~(is_pointer_field (minor_read_field reset obj j)) /\
                      ~(is_minor_pointer (to_minor_offset (minor_read_field reset obj j)))))
    =
    minor_reset_objects_not_mem minor obj
  in
  FStar.Classical.forall_intro_2 aux

private let minor_reset_fields_no_infix_targets (minor: minor_state)
  : Lemma (ensures minor_fields_no_infix_targets (minor_reset minor))
  =
  let reset = minor_reset minor in
  minor_reset_objects_empty minor;
  assert (minor_objects reset == Seq.empty);
  let aux (obj: U64.t) (j: nat)
    : Lemma (ensures (Seq.mem obj (minor_objects reset) /\
                      j < minor_wosize reset obj /\
                      is_minor_pointer (to_minor_offset (minor_read_field reset obj j)) ==>
                      ~(is_infix_in_minor reset
                        (to_minor_offset (minor_read_field reset obj j)))))
    =
    minor_reset_objects_not_mem minor obj
  in
  reveal_opaque (`%minor_fields_no_infix_targets)
    (minor_fields_no_infix_targets reset);
  FStar.Classical.forall_intro_2 aux

let minor_reset_heap_shape (minor: minor_state)
  : Lemma (ensures minor_heap_shape (minor_reset minor))
  =
  let reset = minor_reset minor in
  minor_reset_guards_complete minor;
  minor_reset_infix_wf minor;
  minor_reset_no_scan_invariant minor;
  minor_reset_fields_no_infix_targets minor;
  reveal_opaque (`%minor_heap_shape) (minor_heap_shape reset)

let minor_reset_minor_major_fields_no_blue (minor: minor_state) (major: heap)
  : Lemma (ensures minor_major_fields_no_blue (minor_reset minor) major)
  =
  let reset = minor_reset minor in
  minor_reset_objects_empty minor;
  assert (minor_objects reset == Seq.empty);
  let aux (obj: U64.t) (j: nat)
    : Lemma (ensures (Seq.mem obj (minor_objects reset) /\
                      j < minor_wosize reset obj /\
                      is_pointer_field (minor_read_field reset obj j) ==>
                      Seq.mem ((minor_read_field reset obj j) <: obj_addr)
                              (objects zero_addr major) /\
                      ~(is_blue ((minor_read_field reset obj j) <: obj_addr) major)))
    =
    minor_reset_objects_not_mem minor obj
  in
  reveal_opaque (`%minor_major_fields_no_blue)
    (minor_major_fields_no_blue reset major);
  FStar.Classical.forall_intro_2 aux

let minor_reset_major_minor_fields_no_infix_targets
  (minor: minor_state) (major: heap)
  : Lemma (ensures major_minor_fields_no_infix_targets (minor_reset minor) major)
  =
  let reset = minor_reset minor in
  let aux (obj: obj_addr) (j: nat)
    : Lemma (ensures (Seq.mem obj (objects zero_addr major) /\
                      ~(is_blue obj major) /\
                      ~(is_no_scan obj major) /\
                      j < U64.v (wosize_of_object obj major) /\
                      U64.v obj + j * 8 + 8 <= heap_size /\
                      (U64.v obj + j * 8) % 8 == 0 ==>
                      (let v = to_minor_offset
                         (read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
                       is_minor_pointer v ==> ~(is_infix_in_minor reset v))))
    =
    if Seq.mem obj (objects zero_addr major) &&
       not (is_blue obj major) &&
       not (is_no_scan obj major) &&
       j < U64.v (wosize_of_object obj major) &&
       U64.v obj + j * 8 + 8 <= heap_size &&
       (U64.v obj + j * 8) % 8 = 0 then begin
      let field_nat = U64.v obj + j * 8 in
      assert_norm (pow2 57 < pow2 64);
      assert (field_nat < heap_size);
      assert (field_nat < pow2 64);
      let field_addr : hp_addr = U64.uint_to_t field_nat in
      assert (U64.v field_addr == field_nat);
      let v = to_minor_offset (read_word major field_addr) in
      minor_reset_no_infix minor v
    end
  in
  reveal_opaque (`%major_minor_fields_no_infix_targets)
    (major_minor_fields_no_infix_targets reset major);
  FStar.Classical.forall_intro_2 aux

let collection_heap_shape_after_minor_reset
  (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma (requires major_heap_shape major fp)
          (ensures collection_heap_shape (minor_reset minor) major fp)
  =
  let reset = minor_reset minor in
  minor_reset_heap_shape minor;
  minor_reset_minor_major_fields_no_blue minor major;
  minor_reset_major_minor_fields_no_infix_targets minor major;
  reveal_opaque (`%collection_heap_shape)
    (collection_heap_shape reset major fp)
#pop-options

/// ---------------------------------------------------------------------------
/// Helper Lemmas for SPOT (Empty Minor Heap)
/// ---------------------------------------------------------------------------

/// When there are no minor objects, minor_major_fields_no_blue is vacuously true
let minor_major_fields_no_blue_empty (minor: minor_state) (major: heap)
  : Lemma (requires minor_objects minor == Seq.empty)
          (ensures minor_major_fields_no_blue minor major)
  = reveal_opaque (`%minor_major_fields_no_blue) (minor_major_fields_no_blue minor major)
    // Forall is over (obj in minor_objects minor), which is empty
