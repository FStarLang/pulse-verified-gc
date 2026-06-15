module GC.Gen.ChunkedMajorGCBridge

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap

module MH = GC.Spec.MajorHeap
module Header = GC.Lib.Header
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module ChunkedMark = GC.Spec.ChunkedMarkBounded.Defs
module ChunkedMarkPres = GC.Spec.ChunkedMarkBounded.Preservation
module ChunkedMarkLive = GC.Spec.ChunkedMajorGC.MarkLiveness
module ChunkedMarkEdge = GC.Spec.ChunkedMarkBounded.EdgeInvariant
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph
module ChunkedMajorGC = GC.Spec.ChunkedMajorGC.Defs
module ChunkedMajorGCCorr = GC.Spec.ChunkedMajorGC.Correctness
module ChunkedMarkNoBlack = GC.Spec.ChunkedMarkBounded.NoBlackToWhite
module GenInv = GC.Gen.HeapInvariant
module CG = GC.Gen.CombinedGraph

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

let chunked_sweep_black_implies_gen_black
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires SweepDefs.chunked_is_black mh obj)
      (ensures GenInv.chunked_is_black mh obj)
  =
  SweepDefs.chunked_is_black_read_header mh obj;
  match SweepDefs.chunked_read_header mh obj with
  | None -> assert False
  | Some hdr ->
    SweepDefs.chunked_read_header_step mh obj;
    assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
    assert (getColor hdr == Header.Black);
    GenInv.chunked_is_black_header mh obj hdr;
    assert (GenInv.chunked_is_black mh obj == true)

let chunked_no_black_objects_implies_no_black_to_white_vertex_targets
  (mh: MH.major_heap)
  : Lemma
      (requires GenInv.chunked_no_black_objects mh)
      (ensures
        ChunkedMarkNoBlack.chunked_no_black_to_white_vertex_targets mh)
  =
  let no_black_src (src: obj_addr)
    : Lemma
        (ensures
          forall (dst: obj_addr).
          ChunkedMajorGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGraph.chunked_major_vertex mh dst /\
          SweepDefs.chunked_is_black mh src ==>
          ~(SweepDefs.chunked_is_white mh dst))
    =
    let no_black_dst (dst: obj_addr)
      : Lemma
          (requires
            ChunkedMajorGraph.chunked_major_edge mh src dst /\
            ChunkedMajorGraph.chunked_major_vertex mh dst /\
            SweepDefs.chunked_is_black mh src)
          (ensures ~(SweepDefs.chunked_is_white mh dst))
      =
      ChunkedMajorGraph.chunked_major_edge_source_vertex mh src dst;
      ChunkedMajorGraph.chunked_major_vertex_elim mh src;
      chunked_sweep_black_implies_gen_black mh src;
      assert (Seq.mem src (MH.major_objects mh));
      assert (GenInv.chunked_is_black mh src);
      GenInv.chunked_no_black_objects_elim mh src;
      assert False
    in
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires no_black_dst)
  in
  FStar.Classical.forall_intro no_black_src;
  ChunkedMarkNoBlack.chunked_no_black_to_white_vertex_targets_intro mh

let chunked_collection_heap_shape_implies_no_black_to_white_vertex_targets
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape minor mh fp fuel)
      (ensures
        ChunkedMarkNoBlack.chunked_no_black_to_white_vertex_targets mh)
  =
  GenInv.chunked_collection_heap_shape_elim minor mh fp fuel;
  chunked_no_black_objects_implies_no_black_to_white_vertex_targets mh

let chunked_major_edge_gen_field_witness
  (mh: MH.major_heap)
  : prop
  =
  forall (src dst: obj_addr).
    ChunkedMajorGraph.chunked_major_edge mh src dst /\
    ChunkedMajorGraph.chunked_major_vertex mh dst ==>
    exists (idx: nat) (field_addr: hp_addr) (raw: U64.t).
      Seq.mem src (MH.major_objects mh) /\
      idx < CG.chunked_wosize_nat_of_object mh src /\
      CG.chunked_major_field_slot src idx == Some field_addr /\
      MH.read_word_in_major mh field_addr == Some raw /\
      Seq.mem dst (MH.major_objects mh) /\
      is_pointer_to raw dst

let chunked_major_edge_gen_field_witness_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr).
          ChunkedMajorGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGraph.chunked_major_vertex mh dst ==>
          exists (idx: nat) (field_addr: hp_addr) (raw: U64.t).
            Seq.mem src (MH.major_objects mh) /\
            idx < CG.chunked_wosize_nat_of_object mh src /\
            CG.chunked_major_field_slot src idx == Some field_addr /\
            MH.read_word_in_major mh field_addr == Some raw /\
            Seq.mem dst (MH.major_objects mh) /\
            is_pointer_to raw dst)
      (ensures chunked_major_edge_gen_field_witness mh)
  =
  let aux (src dst: obj_addr)
    : Lemma
        (requires
          ChunkedMajorGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGraph.chunked_major_vertex mh dst)
        (ensures
          exists (idx: nat) (field_addr: hp_addr) (raw: U64.t).
            Seq.mem src (MH.major_objects mh) /\
            idx < CG.chunked_wosize_nat_of_object mh src /\
            CG.chunked_major_field_slot src idx == Some field_addr /\
            MH.read_word_in_major mh field_addr == Some raw /\
            Seq.mem dst (MH.major_objects mh) /\
            is_pointer_to raw dst)
    =
    ()
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 aux)

let chunked_major_edge_gen_field_witness_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        chunked_major_edge_gen_field_witness mh /\
        ChunkedMajorGraph.chunked_major_edge mh src dst /\
        ChunkedMajorGraph.chunked_major_vertex mh dst)
      (ensures
        exists (idx: nat) (field_addr: hp_addr) (raw: U64.t).
          Seq.mem src (MH.major_objects mh) /\
          idx < CG.chunked_wosize_nat_of_object mh src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw /\
          Seq.mem dst (MH.major_objects mh) /\
          is_pointer_to raw dst)
  =
  ()

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_sweep_not_blue_vertex_implies_gen_not_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMajorGraph.chunked_major_vertex mh obj /\
        ~(SweepDefs.chunked_is_blue mh obj))
      (ensures ~(GenInv.chunked_is_blue mh obj))
  =
  ChunkedMajorGraph.chunked_major_vertex_elim mh obj;
  MH.major_objects_member_header_read_some mh obj;
  let hdr = Some?.v (MH.read_word_in_major mh (hd_address obj)) in
  assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
  GenInv.chunked_is_blue_header mh obj hdr;
  SweepDefs.chunked_read_header_step mh obj;
  assert (SweepDefs.chunked_read_header mh obj == Some hdr);
  SweepDefs.chunked_color_of_object_some mh obj hdr;
  if GenInv.chunked_is_blue mh obj then begin
    assert (getColor hdr = Header.Blue);
    SweepDefs.chunked_is_blue_from_color mh obj;
    assert False
  end

let chunked_gen_not_blue_vertex_implies_sweep_not_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMajorGraph.chunked_major_vertex mh obj /\
        ~(GenInv.chunked_is_blue mh obj))
      (ensures ~(SweepDefs.chunked_is_blue mh obj))
  =
  if SweepDefs.chunked_is_blue mh obj then begin
    ChunkedMajorGraph.chunked_major_vertex_elim mh obj;
    SweepDefs.chunked_is_blue_read_header mh obj;
    SweepDefs.chunked_read_header_step mh obj;
    let hdr = Some?.v (SweepDefs.chunked_read_header mh obj) in
    assert (SweepDefs.chunked_read_header mh obj == Some hdr);
    assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
    assert (getColor hdr == Header.Blue);
    GenInv.chunked_is_blue_header mh obj hdr;
    assert (GenInv.chunked_is_blue mh obj);
    assert False
  end
#pop-options

let chunked_no_pointer_to_blue_implies_mark_vertex_targets
  (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenInv.chunked_no_pointer_to_blue mh /\
        chunked_major_edge_gen_field_witness mh)
      (ensures
        ChunkedMarkLive.chunked_no_pointer_to_blue_vertex_targets mh)
  =
  let no_blue (src dst: obj_addr)
    : Lemma
        (requires
          ChunkedMajorGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGraph.chunked_major_vertex mh dst /\
          ~(SweepDefs.chunked_is_blue mh src))
        (ensures ~(SweepDefs.chunked_is_blue mh dst))
    =
    ChunkedMajorGraph.chunked_major_edge_source_vertex mh src dst;
    chunked_sweep_not_blue_vertex_implies_gen_not_blue mh src;
    chunked_major_edge_gen_field_witness_elim mh src dst;
    assert (
      exists (idx: nat) (field_addr: hp_addr) (raw: U64.t).
        Seq.mem src (MH.major_objects mh) /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw /\
        Seq.mem dst (MH.major_objects mh) /\
        is_pointer_to raw dst);
    let idx = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun (idx: nat) ->
       exists (field_addr: hp_addr) (raw: U64.t).
        Seq.mem src (MH.major_objects mh) /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw /\
        Seq.mem dst (MH.major_objects mh) /\
        is_pointer_to raw dst) in
    assert (
      exists (field_addr: hp_addr) (raw: U64.t).
        Seq.mem src (MH.major_objects mh) /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw /\
        Seq.mem dst (MH.major_objects mh) /\
        is_pointer_to raw dst);
    let field_addr = FStar.IndefiniteDescription.indefinite_description_ghost hp_addr
      (fun (field_addr: hp_addr) ->
       exists (raw: U64.t).
        Seq.mem src (MH.major_objects mh) /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw /\
        Seq.mem dst (MH.major_objects mh) /\
        is_pointer_to raw dst) in
    assert (
      exists (raw: U64.t).
        Seq.mem src (MH.major_objects mh) /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw /\
        Seq.mem dst (MH.major_objects mh) /\
        is_pointer_to raw dst);
    let raw = FStar.IndefiniteDescription.indefinite_description_ghost U64.t
      (fun (raw: U64.t) ->
        Seq.mem src (MH.major_objects mh) /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw /\
        Seq.mem dst (MH.major_objects mh) /\
        is_pointer_to raw dst) in
    assert (Seq.mem src (MH.major_objects mh));
    assert (idx < CG.chunked_wosize_nat_of_object mh src);
    assert (CG.chunked_major_field_slot src idx == Some field_addr);
    assert (MH.read_word_in_major mh field_addr == Some raw);
    assert (Seq.mem dst (MH.major_objects mh));
    assert (is_pointer_to raw dst);
    GenInv.chunked_no_pointer_to_blue_elim mh src dst idx field_addr raw;
    ChunkedMajorGraph.chunked_major_vertex_elim mh dst;
    chunked_gen_not_blue_vertex_implies_sweep_not_blue mh dst
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 no_blue);
  ChunkedMarkLive.chunked_no_pointer_to_blue_vertex_targets_intro mh

let chunked_collection_heap_shape_implies_mark_vertex_targets_no_pointer_to_blue
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp fuel /\
        chunked_major_edge_gen_field_witness mh)
      (ensures
        ChunkedMarkLive.chunked_no_pointer_to_blue_vertex_targets mh)
  =
  GenInv.chunked_collection_heap_shape_elim minor mh fp fuel;
  GenInv.chunked_major_alloc_shape_elim mh fp fuel;
  chunked_no_pointer_to_blue_implies_mark_vertex_targets mh

let chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        mark_fuel > 0 /\
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMark.chunked_count_non_black mh /\
        ChunkedMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMarkLive.chunked_no_pointer_to_blue mh /\
        ChunkedMarkEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  GenInv.chunked_collection_heap_shape_elim minor mh fp shape_fuel;
  GenInv.chunked_major_alloc_shape_elim mh fp shape_fuel;
  chunked_collection_heap_shape_implies_no_black_to_white_vertex_targets
    minor mh fp shape_fuel;
  ChunkedMajorGCCorr.chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved
    mh roots cap mark_fuel

let chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_vertex_targets
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        mark_fuel > 0 /\
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        chunked_major_edge_gen_field_witness mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMark.chunked_count_non_black mh /\
        ChunkedMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMarkEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  GenInv.chunked_collection_heap_shape_elim minor mh fp shape_fuel;
  GenInv.chunked_major_alloc_shape_elim mh fp shape_fuel;
  chunked_no_black_objects_implies_no_black_to_white_vertex_targets mh;
  chunked_no_pointer_to_blue_implies_mark_vertex_targets mh;
  ChunkedMajorGCCorr.chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_vertex_targets
    mh roots cap mark_fuel
