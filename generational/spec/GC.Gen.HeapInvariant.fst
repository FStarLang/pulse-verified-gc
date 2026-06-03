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
module Header = GC.Lib.Header

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
