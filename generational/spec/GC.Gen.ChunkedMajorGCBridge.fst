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
module MarkDefs = GC.Spec.ChunkedMark.Defs
module ChunkedMark = GC.Spec.ChunkedMarkBounded.Defs
module ChunkedMarkPres = GC.Spec.ChunkedMarkBounded.Preservation
module ChunkedMarkReadiness = GC.Spec.ChunkedMarkBounded.Readiness
module ChunkedMarkTargetMembership = GC.Spec.ChunkedMarkBounded.TargetMembership
module ChunkedMarkTargetReady = GC.Spec.ChunkedMarkBounded.TargetReady
module ChunkedMarkLive = GC.Spec.ChunkedMajorGC.MarkLiveness
module ChunkedMajorGCRoots = GC.Spec.ChunkedMajorGC.Roots
module RangePres = GC.Spec.ChunkedSweepCoalesce.RangePreservation
module ChunkedMarkEdge = GC.Spec.ChunkedMarkBounded.EdgeInvariant
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph
module ChunkedMajorGC = GC.Spec.ChunkedMajorGC.Defs
module ChunkedMajorGCCorr = GC.Spec.ChunkedMajorGC.Correctness
module ChunkedMajorReach = GC.Spec.ChunkedMajorGC.Reachability
module ChunkedMarkNoBlack = GC.Spec.ChunkedMarkBounded.NoBlackToWhite
module GenInv = GC.Gen.HeapInvariant
module SpecMajorAlloc = GC.Spec.MajorAllocator
module Promote = GC.Gen.Promote
module CG = GC.Gen.CombinedGraph

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

let chunked_major_roots_nonblue
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : prop =
  forall (root: obj_addr).
    Seq.mem root roots /\
    Seq.mem root (MH.major_objects mh) ==>
    ~(GenInv.chunked_is_blue mh root)

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

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"
let chunked_major_edge_gen_field_witness_from_pointer_fields
  (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        (forall (obj: obj_addr).
          Seq.mem obj (MH.major_objects mh) ==> is_pointer_field obj))
      (ensures chunked_major_edge_gen_field_witness mh)
  =
  let witness (src dst: obj_addr)
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
    ChunkedMajorGraph.chunked_major_edge_elim mh src dst;
    assert (exists (i: U64.t{U64.v i >= 1}).
      ChunkedMajorGraph.chunked_major_field_points_to mh src i dst);
    assert (exists (i: U64.t).
      U64.v i >= 1 /\
      ChunkedMajorGraph.chunked_major_field_points_to mh src i dst);
    let i =
      FStar.IndefiniteDescription.indefinite_description_ghost
        U64.t
        (fun (i: U64.t) ->
          U64.v i >= 1 /\
          ChunkedMajorGraph.chunked_major_field_points_to mh src i dst) in
    assert (U64.v i >= 1);
    assert (ChunkedMajorGraph.chunked_major_field_points_to mh src i dst);
    ChunkedMajorGraph.chunked_major_field_points_to_elim mh src i dst;
    ChunkedMajorGraph.chunked_major_vertex_elim mh src;
    ChunkedMajorGraph.chunked_major_vertex_elim mh dst;
    assert (Seq.mem src (MH.major_objects mh));
    assert (Seq.mem dst (MH.major_objects mh));
    MH.major_objects_member_header_read_some mh src;
    let hdr = Some?.v (MH.read_word_in_major mh (hd_address src)) in
    assert (MH.read_word_in_major mh (hd_address src) == Some hdr);
    SweepDefs.chunked_read_header_step mh src;
    assert (SweepDefs.chunked_read_header mh src == Some hdr);
    SweepDefs.chunked_wosize_of_object_some mh src hdr;
    CG.chunked_wosize_nat_header mh src hdr;
    assert (U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh src));
    assert (U64.v i <= U64.v (getWosize hdr));
    let idx = U64.v i - 1 in
    assert (idx < U64.v (getWosize hdr));
    assert (idx < CG.chunked_wosize_nat_of_object mh src);
    CG.chunked_major_field_slot_of_object_header mh src hdr idx;
    match CG.chunked_major_field_slot src idx with
    | None -> assert False
    | Some field_addr ->
      CG.chunked_major_field_slot_elim src idx field_addr;
      assert (CG.chunked_major_field_slot src idx == Some field_addr);
      MH.read_word_in_major_lookup_index mh (hd_address src) hdr;
      let hidx = MH.lookup_chunk_index_value mh (hd_address src) in
      assert (MH.lookup_chunk_index mh (hd_address src) == Some hidx);
      assert (hidx < Seq.length mh);
      assert (MH.word_in_chunk (Seq.index mh hidx) (hd_address src));
      MH.major_objects_member_in_lookup_chunk mh hidx src;
      MH.objects_in_chunk_member_header_fits (Seq.index mh hidx) src;
      assert (MH.object_wosize_in_chunk (Seq.index mh hidx) src ==
              U64.v (getWosize hdr));
      assert (U64.v field_addr == U64.v src + idx * U64.v mword);
      assert (idx + 1 == U64.v i);
      assert_norm (U64.v mword == 8);
      FStar.Math.Lemmas.distributivity_add_left
        idx 1 (U64.v mword);
      assert (idx * U64.v mword + U64.v mword ==
              (idx + 1) * U64.v mword);
      assert (U64.v src <= U64.v field_addr);
      assert (U64.v field_addr + U64.v mword <=
              U64.v src + U64.v (getWosize hdr) * U64.v mword);
      hd_address_spec src;
      assert (U64.v (hd_address src) + U64.v mword == U64.v src);
      assert (U64.v field_addr ==
              U64.v (hd_address src) + U64.v mword +
                idx * U64.v mword);
      assert (U64.v mword + idx * U64.v mword ==
              idx * U64.v mword + U64.v mword);
      FStar.Math.Lemmas.paren_add_right
        (U64.v (hd_address src)) (U64.v mword)
        (idx * U64.v mword);
      assert (U64.v field_addr ==
              U64.v (hd_address src) +
                (idx * U64.v mword + U64.v mword));
      assert ((idx + 1) * U64.v mword ==
              U64.v i * U64.v mword);
      assert (U64.v i * U64.v mword ==
              U64.v mword * U64.v i);
      assert (U64.v field_addr ==
              U64.v (hd_address src) + U64.v mword * U64.v i);
      assert (U64.v field_addr < heap_size);
      assert (U64.v (hd_address src) + U64.v mword * U64.v i < heap_size);
      assert (U64.v (hd_address src) + U64.v mword * U64.v i < pow2 64);
      assert (U64.v mword * U64.v i <=
              U64.v (hd_address src) + U64.v mword * U64.v i);
      assert (U64.v mword * U64.v i < pow2 64);
      MH.major_object_payload_word_in_lookup_chunk mh hidx src field_addr;
      let raw = MH.read_word_in_chunk (Seq.index mh hidx) field_addr in
      MH.read_word_in_major_at_lookup_index mh field_addr hidx;
      assert (MH.read_word_in_major mh field_addr == Some raw);
      let get_field_addr = U64.add (hd_address src) (U64.mul mword i) in
      assert (U64.v (U64.mul mword i) == U64.v mword * U64.v i);
      assert (U64.v get_field_addr ==
              U64.v (hd_address src) + U64.v mword * U64.v i);
      U64.v_inj get_field_addr field_addr;
      assert (get_field_addr == field_addr);
      MarkDefs.chunked_get_field_read_some mh src i raw;
      assert (MarkDefs.chunked_get_field mh src i == raw);
      assert (MarkDefs.chunked_is_pointer_field mh raw);
      MarkDefs.chunked_pointer_field_as_obj_addr_step mh raw;
      assert (raw == dst);
      assert (is_pointer_field dst);
      assert (is_pointer_field raw);
      assert (is_pointer_to raw dst);
      FStar.Classical.exists_intro
        (fun (idx: nat) ->
          exists (field_addr: hp_addr) (raw: U64.t).
            Seq.mem src (MH.major_objects mh) /\
            idx < CG.chunked_wosize_nat_of_object mh src /\
            CG.chunked_major_field_slot src idx == Some field_addr /\
            MH.read_word_in_major mh field_addr == Some raw /\
            Seq.mem dst (MH.major_objects mh) /\
            is_pointer_to raw dst)
        idx
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 witness);
  chunked_major_edge_gen_field_witness_intro mh
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
private let chunked_wosize_nat_agrees_with_sweep
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        CG.chunked_wosize_nat_of_object mh obj ==
        U64.v (SweepDefs.chunked_wosize_of_object mh obj))
  =
  MH.major_objects_member_header_read_some mh obj;
  let hdr = Some?.v (MH.read_word_in_major mh (hd_address obj)) in
  assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
  CG.chunked_wosize_nat_header mh obj hdr;
  SweepDefs.chunked_read_header_step mh obj;
  assert (SweepDefs.chunked_read_header mh obj == Some hdr);
  SweepDefs.chunked_wosize_of_object_some mh obj hdr
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
private let chunked_field_slot_mark_index_facts
  (mh: MH.major_heap)
  (src: obj_addr)
  (idx: nat)
  (field_addr: hp_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem src (MH.major_objects mh) /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr)
      (ensures
        idx + 1 < pow2 64 /\
        U64.v field_addr ==
          U64.v (hd_address src) + U64.v mword * (idx + 1) /\
        idx + 1 <= U64.v (SweepDefs.chunked_wosize_of_object mh src))
  =
  chunked_wosize_nat_agrees_with_sweep mh src;
  CG.chunked_major_field_slot_elim src idx field_addr;
  assert (U64.v field_addr == U64.v src + idx * U64.v mword);
  assert (idx + 1 <= U64.v (SweepDefs.chunked_wosize_of_object mh src));
  assert (U64.v (SweepDefs.chunked_wosize_of_object mh src) < pow2 64);
  assert (idx + 1 < pow2 64);
  hd_address_spec src;
  assert_norm (U64.v mword == 8);
  FStar.Math.Lemmas.distributivity_add_left idx 1 (U64.v mword);
  assert (idx * U64.v mword + U64.v mword ==
          (idx + 1) * U64.v mword);
  assert (U64.v (hd_address src) + U64.v mword == U64.v src);
  assert (U64.v field_addr ==
          U64.v (hd_address src) + U64.v mword + idx * U64.v mword);
  assert (U64.v mword + idx * U64.v mword ==
          idx * U64.v mword + U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v (hd_address src)) (U64.v mword)
    (idx * U64.v mword);
  assert (U64.v field_addr ==
          U64.v (hd_address src) +
          (idx * U64.v mword + U64.v mword));
  assert ((idx + 1) * U64.v mword ==
          U64.v mword * (idx + 1));
  assert (U64.v field_addr ==
          U64.v (hd_address src) + U64.v mword * (idx + 1))
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_edge_gen_field_witness_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_major_edge_gen_field_witness mh)
      (ensures
        chunked_major_edge_gen_field_witness
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed mh roots;
  let all_vertices (v: obj_addr) =
    ChunkedMajorGraph.chunked_major_vertex mh v in
  let all_vertices_mem (v: obj_addr)
    : Lemma
        (requires all_vertices v)
        (ensures Seq.mem v (MH.major_objects mh))
    =
    ChunkedMajorGraph.chunked_major_vertex_elim mh v
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires all_vertices_mem);
  ChunkedMajorGCRoots.chunked_gray_roots_live_subgraph_preserved
    mh roots all_vertices;
  ChunkedMajorGraph.chunked_major_live_subgraph_edges_elim
    mh grayed all_vertices;
  let witness (src dst: obj_addr)
    : Lemma
        (requires
          ChunkedMajorGraph.chunked_major_edge grayed src dst /\
          ChunkedMajorGraph.chunked_major_vertex grayed dst)
        (ensures
          exists (idx: nat) (field_addr: hp_addr) (raw: U64.t).
            Seq.mem src (MH.major_objects grayed) /\
            idx < CG.chunked_wosize_nat_of_object grayed src /\
            CG.chunked_major_field_slot src idx == Some field_addr /\
            MH.read_word_in_major grayed field_addr == Some raw /\
            Seq.mem dst (MH.major_objects grayed) /\
            is_pointer_to raw dst)
    =
    ChunkedMajorGraph.chunked_major_edge_source_vertex grayed src dst;
    ChunkedMajorGraph.chunked_major_vertex_elim grayed src;
    ChunkedMajorGraph.chunked_major_vertex_elim grayed dst;
    assert (Seq.mem src (MH.major_objects mh));
    assert (Seq.mem dst (MH.major_objects mh));
    ChunkedMajorGraph.chunked_major_vertex_intro mh src;
    ChunkedMajorGraph.chunked_major_vertex_intro mh dst;
    assert (all_vertices src);
    assert (forall (y: obj_addr).
      ChunkedMajorGraph.chunked_major_edge mh src y <==>
      ChunkedMajorGraph.chunked_major_edge grayed src y);
    assert (ChunkedMajorGraph.chunked_major_edge mh src dst);
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
    chunked_field_slot_mark_index_facts mh src idx field_addr;
    let field_i: (i: U64.t{U64.v i >= 1}) =
      U64.uint_to_t (idx + 1) in
    U64.vu_inv (idx + 1);
    assert (U64.v field_i == idx + 1);
    assert (U64.v field_i <=
            U64.v (SweepDefs.chunked_wosize_of_object mh src));
    assert (U64.v field_addr ==
            U64.v (hd_address src) + U64.v mword * U64.v field_i);
    ChunkedMajorGCRoots.chunked_gray_roots_preserves_field_read
      mh roots src field_i field_addr raw;
    ChunkedMajorGCRoots.chunked_gray_roots_preserves_wosize_of_object
      mh roots src;
    chunked_wosize_nat_agrees_with_sweep mh src;
    chunked_wosize_nat_agrees_with_sweep grayed src;
    assert (idx < CG.chunked_wosize_nat_of_object grayed src);
    FStar.Classical.exists_intro
      (fun (idx: nat) ->
        exists (field_addr: hp_addr) (raw: U64.t).
          Seq.mem src (MH.major_objects grayed) /\
          idx < CG.chunked_wosize_nat_of_object grayed src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major grayed field_addr == Some raw /\
          Seq.mem dst (MH.major_objects grayed) /\
          is_pointer_to raw dst)
      idx
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 witness);
  chunked_major_edge_gen_field_witness_intro grayed
#pop-options

let chunked_major_field_targets_non_infix
  (mh: MH.major_heap)
  : prop
  =
  forall (src dst: obj_addr) (idx: nat)
         (field_addr: hp_addr) (raw: U64.t).
    Seq.mem src (MH.major_objects mh) /\
    idx < CG.chunked_wosize_nat_of_object mh src /\
    CG.chunked_major_field_slot src idx == Some field_addr /\
    MH.read_word_in_major mh field_addr == Some raw /\
    Seq.mem dst (MH.major_objects mh) /\
    is_pointer_to raw dst ==>
    ~(SweepDefs.chunked_is_infix mh dst)

let chunked_major_field_targets_non_infix_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr) (idx: nat)
               (field_addr: hp_addr) (raw: U64.t).
          Seq.mem src (MH.major_objects mh) /\
          idx < CG.chunked_wosize_nat_of_object mh src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw /\
          Seq.mem dst (MH.major_objects mh) /\
          is_pointer_to raw dst ==>
          ~(SweepDefs.chunked_is_infix mh dst))
      (ensures chunked_major_field_targets_non_infix mh)
  =
  ()

let chunked_major_field_targets_non_infix_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  (idx: nat)
  (field_addr: hp_addr)
  (raw: U64.t)
  : Lemma
      (requires
        chunked_major_field_targets_non_infix mh /\
        Seq.mem src (MH.major_objects mh) /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw /\
        Seq.mem dst (MH.major_objects mh) /\
        is_pointer_to raw dst)
      (ensures ~(SweepDefs.chunked_is_infix mh dst))
  =
  ()

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_field_targets_non_infix_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_major_field_targets_non_infix mh)
      (ensures
        chunked_major_field_targets_non_infix
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed mh roots;
  let non_infix
    (src dst: obj_addr)
    (idx: nat)
    (field_addr: hp_addr)
    (raw: U64.t)
    : Lemma
        (requires
          Seq.mem src (MH.major_objects grayed) /\
          idx < CG.chunked_wosize_nat_of_object grayed src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major grayed field_addr == Some raw /\
          Seq.mem dst (MH.major_objects grayed) /\
          is_pointer_to raw dst)
        (ensures ~(SweepDefs.chunked_is_infix grayed dst))
    =
    assert (Seq.mem src (MH.major_objects mh));
    assert (Seq.mem dst (MH.major_objects mh));
    ChunkedMajorGCRoots.chunked_gray_roots_preserves_wosize_of_object
      mh roots src;
    chunked_wosize_nat_agrees_with_sweep mh src;
    chunked_wosize_nat_agrees_with_sweep grayed src;
    assert (idx < CG.chunked_wosize_nat_of_object mh src);
    chunked_field_slot_mark_index_facts mh src idx field_addr;
    let field_i: (i: U64.t{U64.v i >= 1}) =
      U64.uint_to_t (idx + 1) in
    U64.vu_inv (idx + 1);
    assert (U64.v field_i == idx + 1);
    assert (U64.v field_i <=
            U64.v (SweepDefs.chunked_wosize_of_object mh src));
    assert (U64.v field_addr ==
            U64.v (hd_address src) + U64.v mword * U64.v field_i);
    ChunkedMajorGCRoots.chunked_gray_roots_preserves_field_read_back
      mh roots src field_i field_addr raw;
    chunked_major_field_targets_non_infix_elim
      mh src dst idx field_addr raw;
    ChunkedMajorGCRoots.chunked_gray_roots_preserves_infix_status
      mh roots dst;
    assert (SweepDefs.chunked_is_infix grayed dst ==
            SweepDefs.chunked_is_infix mh dst)
  in
  let non_infix_for_quantifiers
    (src dst: obj_addr)
    (idx: nat)
    (field_addr: hp_addr)
    : Lemma
        (ensures
          forall (raw: U64.t).
            Seq.mem src (MH.major_objects grayed) /\
            idx < CG.chunked_wosize_nat_of_object grayed src /\
            CG.chunked_major_field_slot src idx == Some field_addr /\
            MH.read_word_in_major grayed field_addr == Some raw /\
            Seq.mem dst (MH.major_objects grayed) /\
            is_pointer_to raw dst ==>
            ~(SweepDefs.chunked_is_infix grayed dst))
    =
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires
        (non_infix src dst idx field_addr))
  in
  FStar.Classical.forall_intro_4 non_infix_for_quantifiers;
  chunked_major_field_targets_non_infix_intro grayed
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_field_targets_non_infix_implies_vertex_edge_targets_non_infix
  (mh: MH.major_heap)
  : Lemma
      (requires
        chunked_major_edge_gen_field_witness mh /\
        chunked_major_field_targets_non_infix mh)
      (ensures ChunkedMarkEdge.chunked_vertex_edge_targets_non_infix mh)
  =
  let non_infix (src dst: obj_addr)
    : Lemma
        (requires
          ChunkedMajorGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGraph.chunked_major_vertex mh dst)
        (ensures ~(SweepDefs.chunked_is_infix mh dst))
    =
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
    chunked_major_field_targets_non_infix_elim
      mh src dst idx field_addr raw
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 non_infix);
  ChunkedMarkEdge.chunked_vertex_edge_targets_non_infix_intro mh
#pop-options

let chunked_major_raw_field_targets_in_major
  (mh: MH.major_heap)
  : prop
  =
  forall (src: obj_addr) (idx: nat) (field_addr: hp_addr) (raw: U64.t).
    Seq.mem src (MH.major_objects mh) /\
    idx < CG.chunked_wosize_nat_of_object mh src /\
    CG.chunked_major_field_slot src idx == Some field_addr /\
    MH.read_word_in_major mh field_addr == Some raw /\
    MarkDefs.chunked_is_pointer_field mh raw ==>
    Seq.mem (MarkDefs.chunked_pointer_field_as_obj_addr mh raw)
      (MH.major_objects mh)

let chunked_major_raw_field_targets_in_major_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src: obj_addr) (idx: nat) (field_addr: hp_addr) (raw: U64.t).
          Seq.mem src (MH.major_objects mh) /\
          idx < CG.chunked_wosize_nat_of_object mh src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw /\
          MarkDefs.chunked_is_pointer_field mh raw ==>
          Seq.mem (MarkDefs.chunked_pointer_field_as_obj_addr mh raw)
            (MH.major_objects mh))
      (ensures chunked_major_raw_field_targets_in_major mh)
  =
  ()

let chunked_major_raw_field_targets_in_major_elim
  (mh: MH.major_heap)
  (src: obj_addr)
  (idx: nat)
  (field_addr: hp_addr)
  (raw: U64.t)
  : Lemma
      (requires
        chunked_major_raw_field_targets_in_major mh /\
        Seq.mem src (MH.major_objects mh) /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw /\
        MarkDefs.chunked_is_pointer_field mh raw)
      (ensures
        Seq.mem (MarkDefs.chunked_pointer_field_as_obj_addr mh raw)
          (MH.major_objects mh))
  =
  ()

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
private let chunked_get_field_from_major_field_slot
  (mh: MH.major_heap)
  (src: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (idx: nat)
  (field_addr: hp_addr)
  (raw: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem src (MH.major_objects mh) /\
        idx + 1 == U64.v i /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw)
      (ensures MarkDefs.chunked_get_field mh src i == raw)
  =
  chunked_field_slot_mark_index_facts mh src idx field_addr;
  CG.chunked_major_field_slot_elim src idx field_addr;
  assert (U64.v field_addr ==
          U64.v (hd_address src) + U64.v mword * U64.v i);
  assert (U64.v field_addr + U64.v mword <= heap_size);
  let get_field_addr = U64.add (hd_address src) (U64.mul mword i) in
  assert (U64.v (U64.mul mword i) == U64.v mword * U64.v i);
  assert (U64.v get_field_addr ==
          U64.v (hd_address src) + U64.v mword * U64.v i);
  U64.v_inj get_field_addr field_addr;
  assert (get_field_addr == field_addr);
  MarkDefs.chunked_get_field_read_some mh src i raw

let chunked_scanned_raw_targets_in_major_from_major_raw_field_targets
  (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_major_raw_field_targets_in_major mh /\
        (forall (target: obj_addr).
          Seq.mem target (MH.major_objects mh) ==> is_pointer_field target) /\
        chunked_major_field_targets_non_infix mh)
      (ensures
        ChunkedMarkTargetMembership.chunked_scanned_raw_targets_in_major mh)
  =
  let one (obj: obj_addr) (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          Seq.mem obj (MH.major_objects mh) /\
          ~(MarkDefs.chunked_is_no_scan mh obj) /\
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj))
        (ensures
          (let v = MarkDefs.chunked_get_field mh obj i in
           if MarkDefs.chunked_is_pointer_field mh v then
             let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
             Seq.mem child_raw (MH.major_objects mh) /\
             ~(SweepDefs.chunked_is_infix mh child_raw)
           else
             True))
    =
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      MH.major_objects_member_header_read_some mh obj;
      let hdr = Some?.v (MH.read_word_in_major mh (hd_address obj)) in
      assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
      CG.chunked_wosize_nat_header mh obj hdr;
      SweepDefs.chunked_read_header_step mh obj;
      assert (SweepDefs.chunked_read_header mh obj == Some hdr);
      SweepDefs.chunked_wosize_of_object_some mh obj hdr;
      assert (CG.chunked_wosize_nat_of_object mh obj ==
              U64.v (SweepDefs.chunked_wosize_of_object mh obj));
      let idx = U64.v i - 1 in
      assert (idx + 1 == U64.v i);
      assert (idx < CG.chunked_wosize_nat_of_object mh obj);
      CG.chunked_major_field_slot_of_object_header mh obj hdr idx;
      match CG.chunked_major_field_slot obj idx with
      | None -> assert False
      | Some field_addr ->
        CG.chunked_major_field_slot_elim obj idx field_addr;
        chunked_field_slot_mark_index_facts mh obj idx field_addr;
        MH.read_word_in_major_lookup_index mh (hd_address obj) hdr;
        let hidx = MH.lookup_chunk_index_value mh (hd_address obj) in
        assert (MH.lookup_chunk_index mh (hd_address obj) == Some hidx);
        assert (hidx < Seq.length mh);
        MH.major_objects_member_in_lookup_chunk mh hidx obj;
        MH.objects_in_chunk_member_header_fits (Seq.index mh hidx) obj;
        assert (MH.object_wosize_in_chunk (Seq.index mh hidx) obj ==
                U64.v (getWosize hdr));
        assert (U64.v obj <= U64.v field_addr);
        assert (U64.v field_addr + U64.v mword <=
                U64.v obj + U64.v (getWosize hdr) * U64.v mword);
        MH.major_object_payload_word_in_lookup_chunk mh hidx obj field_addr;
        let raw_v = MH.read_word_in_chunk (Seq.index mh hidx) field_addr in
        MH.read_word_in_major_at_lookup_index mh field_addr hidx;
        assert (MH.read_word_in_major mh field_addr == Some raw_v);
        chunked_get_field_from_major_field_slot
          mh obj i idx field_addr raw_v;
        assert (v == raw_v);
        assert (MarkDefs.chunked_is_pointer_field mh raw_v);
        chunked_major_raw_field_targets_in_major_elim
          mh obj idx field_addr raw_v;
        MarkDefs.chunked_pointer_field_as_obj_addr_step mh raw_v;
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        assert (child_raw ==
                MarkDefs.chunked_pointer_field_as_obj_addr mh raw_v);
        assert (Seq.mem child_raw (MH.major_objects mh));
        assert (is_pointer_field child_raw);
        assert (raw_v == child_raw);
        assert (is_pointer_to raw_v child_raw);
        chunked_major_field_targets_non_infix_elim
          mh obj child_raw idx field_addr raw_v
    end
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 one);
  ChunkedMarkTargetMembership.chunked_scanned_raw_targets_in_major_intro mh
#pop-options

let chunked_major_gc_bounded_liveness_policy
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : prop
  =
  mark_fuel > 0 /\
  ChunkedMarkPres.chunked_mark_bounded_preservation_ready
    mh cap mark_fuel /\
  Seq.length (MH.major_objects mh) <= cap /\
  mark_fuel >= ChunkedMark.chunked_count_non_black mh /\
  ChunkedMarkLive.chunked_roots_gray_or_black mh roots

let chunked_major_gc_bounded_liveness_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        mark_fuel > 0 /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMark.chunked_count_non_black mh /\
        ChunkedMarkLive.chunked_roots_gray_or_black mh roots)
      (ensures
        chunked_major_gc_bounded_liveness_policy
          mh roots cap mark_fuel)
  =
  ()

let chunked_major_gc_bounded_liveness_policy_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_liveness_policy
          mh roots cap mark_fuel)
      (ensures
        mark_fuel > 0 /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMark.chunked_count_non_black mh /\
        ChunkedMarkLive.chunked_roots_gray_or_black mh roots)
  =
  ()

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_liveness_policy_after_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        chunked_major_gc_bounded_liveness_policy
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          roots cap mark_fuel)
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  assert (MH.major_objects grayed == MH.major_objects mh);
  assert (Seq.length (MH.major_objects grayed) ==
          Seq.length (MH.major_objects mh));
  assert (Seq.length (MH.major_objects grayed) <= cap);
  ChunkedMarkTargetReady.chunked_count_non_black_bound grayed;
  assert (ChunkedMark.chunked_count_non_black grayed <=
          Seq.length (MH.major_objects grayed));
  assert (mark_fuel >= ChunkedMark.chunked_count_non_black grayed);
  ChunkedMajorGCRoots.chunked_gray_roots_roots_gray_or_black mh roots;
  chunked_major_gc_bounded_liveness_policy_intro
    grayed roots cap mark_fuel
#pop-options

let chunked_major_gc_bounded_after_gray_roots_policy
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : prop
  =
  MH.well_formed_major_heap mh /\
  mark_fuel > 0 /\
  ChunkedMarkPres.chunked_mark_bounded_preservation_ready
    (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
  Seq.length (MH.major_objects mh) <= cap /\
  mark_fuel >= Seq.length (MH.major_objects mh)

let chunked_major_gc_bounded_after_gray_roots_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
  =
  ()

let chunked_major_gc_bounded_after_gray_roots_policy_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
      (ensures
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
  =
  ()

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_after_gray_roots_target_membership_policy
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : prop
  =
  MH.well_formed_major_heap mh /\
  mark_fuel > 0 /\
  ChunkedMarkReadiness.chunked_mark_bounded_target_membership_policy
    (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
  Seq.length (MH.major_objects mh) <= cap /\
  mark_fuel >= Seq.length (MH.major_objects mh)

let chunked_major_gc_bounded_after_gray_roots_target_membership_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkReadiness.chunked_mark_bounded_target_membership_policy
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        chunked_major_gc_bounded_after_gray_roots_target_membership_policy
          mh roots cap mark_fuel)
  =
  ()

let chunked_major_gc_bounded_after_gray_roots_policy_from_target_membership
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_target_membership_policy
          mh roots cap mark_fuel)
      (ensures
        chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  ChunkedMarkReadiness.chunked_mark_bounded_preservation_ready_from_target_membership
    grayed cap mark_fuel;
  chunked_major_gc_bounded_after_gray_roots_policy_intro
    mh roots cap mark_fuel
#pop-options

#push-options "--z3rlimit 1 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_after_gray_roots_raw_target_policy
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : prop
  =
  MH.well_formed_major_heap mh /\
  mark_fuel > 0 /\
  ChunkedMarkTargetMembership.chunked_mark_bounded_raw_targets_policy
    (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
  Seq.length (MH.major_objects mh) <= cap /\
  mark_fuel >= Seq.length (MH.major_objects mh)

let chunked_major_gc_bounded_after_gray_roots_raw_target_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkTargetMembership.chunked_mark_bounded_raw_targets_policy
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        chunked_major_gc_bounded_after_gray_roots_raw_target_policy
          mh roots cap mark_fuel)
  =
  ()

let chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : prop
  =
  MH.well_formed_major_heap mh /\
  mark_fuel > 0 /\
  ChunkedMarkTargetMembership.chunked_scanned_raw_targets_in_major
    (ChunkedMajorGCRoots.chunked_gray_roots mh roots) /\
  Seq.length (MH.major_objects mh) <= cap /\
  mark_fuel >= Seq.length (MH.major_objects mh)

let chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkTargetMembership.chunked_scanned_raw_targets_in_major
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
  =
  ()

let chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy_from_pre_gray
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkTargetMembership.chunked_scanned_raw_targets_in_major mh /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
  =
  ChunkedMarkTargetMembership.chunked_scanned_raw_targets_in_major_preserved_by_gray_roots
    mh roots;
  chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy_intro
    mh roots cap mark_fuel

let chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy_from_raw_field_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        chunked_major_raw_field_targets_in_major mh /\
        (forall (target: obj_addr).
          Seq.mem target (MH.major_objects mh) ==> is_pointer_field target) /\
        chunked_major_field_targets_non_infix mh /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
  =
  chunked_scanned_raw_targets_in_major_from_major_raw_field_targets mh;
  chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy_from_pre_gray
    mh roots cap mark_fuel

let chunked_major_gc_bounded_after_gray_roots_raw_target_policy_from_static
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        chunked_major_gc_bounded_after_gray_roots_raw_target_policy
          mh roots cap mark_fuel)
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed mh roots;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  assert (Seq.length (MH.major_objects grayed) ==
          Seq.length (MH.major_objects mh));
  ChunkedMarkTargetMembership.chunked_mark_bounded_raw_targets_policy_from_static
    grayed cap mark_fuel;
  chunked_major_gc_bounded_after_gray_roots_raw_target_policy_intro
    mh roots cap mark_fuel

let chunked_major_gc_bounded_after_gray_roots_target_membership_policy_from_raw_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        chunked_major_gc_bounded_after_gray_roots_target_membership_policy
          mh roots cap mark_fuel)
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed mh roots;
  ChunkedMarkTargetMembership.chunked_mark_bounded_target_membership_policy_from_raw_targets
    grayed cap mark_fuel;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  assert (Seq.length (MH.major_objects grayed) ==
          Seq.length (MH.major_objects mh));
  chunked_major_gc_bounded_after_gray_roots_target_membership_policy_intro
    mh roots cap mark_fuel

let chunked_major_gc_bounded_after_gray_roots_policy_from_raw_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
  =
  chunked_major_gc_bounded_after_gray_roots_target_membership_policy_from_raw_targets
    mh roots cap mark_fuel;
  chunked_major_gc_bounded_after_gray_roots_policy_from_target_membership
    mh roots cap mark_fuel

let chunked_major_gc_bounded_after_gray_roots_target_membership_policy_from_static_raw_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        chunked_major_gc_bounded_after_gray_roots_target_membership_policy
          mh roots cap mark_fuel)
  =
  chunked_major_gc_bounded_after_gray_roots_raw_target_policy_from_static
    mh roots cap mark_fuel;
  chunked_major_gc_bounded_after_gray_roots_target_membership_policy_from_raw_targets
    mh roots cap mark_fuel

let chunked_major_gc_bounded_after_gray_roots_policy_from_static_raw_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
  =
  chunked_major_gc_bounded_after_gray_roots_raw_target_policy_from_static
    mh roots cap mark_fuel;
  chunked_major_gc_bounded_after_gray_roots_policy_from_raw_targets
    mh roots cap mark_fuel
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_liveness_policy_after_gray_roots_from_policy
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
      (ensures
        chunked_major_gc_bounded_liveness_policy
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          roots cap mark_fuel)
  =
  chunked_major_gc_bounded_after_gray_roots_policy_elim
    mh roots cap mark_fuel;
  chunked_major_gc_bounded_liveness_policy_after_gray_roots
    mh roots cap mark_fuel
#pop-options

private let chunked_gen_black_implies_sweep_black
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        GenInv.chunked_is_black mh obj)
      (ensures SweepDefs.chunked_is_black mh obj)
  =
  MH.major_objects_member_header_read_some mh obj;
  let hdr = Some?.v (MH.read_word_in_major mh (hd_address obj)) in
  assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
  GenInv.chunked_is_black_header mh obj hdr;
  assert (getColor hdr == Header.Black);
  SweepDefs.chunked_read_header_step mh obj;
  assert (SweepDefs.chunked_read_header mh obj == Some hdr);
  SweepDefs.chunked_color_of_object_some mh obj hdr;
  SweepDefs.chunked_is_black_from_color mh obj

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_no_black_objects_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenInv.chunked_no_black_objects mh)
      (ensures
        GenInv.chunked_no_black_objects
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  let roots_nonblack (root: obj_addr)
    : Lemma
        (requires
          Seq.mem root roots /\
          Seq.mem root (MH.major_objects mh))
        (ensures ~(SweepDefs.chunked_is_black mh root))
    =
    if SweepDefs.chunked_is_black mh root then begin
      chunked_sweep_black_implies_gen_black mh root;
      GenInv.chunked_no_black_objects_elim mh root;
      assert False
    end
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires roots_nonblack);
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed mh roots;
  let grayed_no_black (obj: obj_addr)
    : Lemma
        (requires Seq.mem obj (MH.major_objects grayed))
        (ensures ~(GenInv.chunked_is_black grayed obj))
    =
    assert (Seq.mem obj (MH.major_objects mh));
    if GenInv.chunked_is_black grayed obj then begin
      chunked_gen_black_implies_sweep_black grayed obj;
      ChunkedMajorGCRoots.chunked_gray_roots_preserves_black_status
        mh roots obj;
      assert (SweepDefs.chunked_is_black mh obj);
      chunked_sweep_black_implies_gen_black mh obj;
      GenInv.chunked_no_black_objects_elim mh obj;
      assert False
    end
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires grayed_no_black);
  GenInv.chunked_no_black_objects_intro grayed
#pop-options

private let chunked_sweep_blue_implies_gen_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires SweepDefs.chunked_is_blue mh obj)
      (ensures GenInv.chunked_is_blue mh obj)
  =
  SweepDefs.chunked_is_blue_read_header mh obj;
  SweepDefs.chunked_read_header_step mh obj;
  let hdr = Some?.v (SweepDefs.chunked_read_header mh obj) in
  assert (SweepDefs.chunked_read_header mh obj == Some hdr);
  assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
  assert (getColor hdr == Header.Blue);
  GenInv.chunked_is_blue_header mh obj hdr

private let chunked_gen_blue_implies_sweep_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        GenInv.chunked_is_blue mh obj)
      (ensures SweepDefs.chunked_is_blue mh obj)
  =
  MH.major_objects_member_header_read_some mh obj;
  let hdr = Some?.v (MH.read_word_in_major mh (hd_address obj)) in
  assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
  GenInv.chunked_is_blue_header mh obj hdr;
  assert (getColor hdr == Header.Blue);
  SweepDefs.chunked_read_header_step mh obj;
  assert (SweepDefs.chunked_read_header mh obj == Some hdr);
  SweepDefs.chunked_color_of_object_some mh obj hdr;
  SweepDefs.chunked_is_blue_from_color mh obj

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_blue_status_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        chunked_major_roots_nonblue mh roots)
      (ensures
        GenInv.chunked_is_blue
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) target ==
        GenInv.chunked_is_blue mh target)
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  let roots_nonblue_sweep (root: obj_addr)
    : Lemma
        (requires
          Seq.mem root roots /\
          Seq.mem root (MH.major_objects mh))
        (ensures ~(SweepDefs.chunked_is_blue mh root))
    =
    if SweepDefs.chunked_is_blue mh root then begin
      chunked_sweep_blue_implies_gen_blue mh root;
      assert False
    end
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires roots_nonblue_sweep);
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed mh roots;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_blue_status
    mh roots target;
  assert (Seq.mem target (MH.major_objects grayed));
  if GenInv.chunked_is_blue grayed target then begin
    chunked_gen_blue_implies_sweep_blue grayed target;
    assert (SweepDefs.chunked_is_blue mh target);
    chunked_sweep_blue_implies_gen_blue mh target
  end;
  if GenInv.chunked_is_blue mh target then begin
    chunked_gen_blue_implies_sweep_blue mh target;
    assert (SweepDefs.chunked_is_blue grayed target);
    chunked_sweep_blue_implies_gen_blue grayed target
  end
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_minor_major_fields_no_blue_preserved_by_gray_roots
  (minor: minor_state)
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_major_roots_nonblue mh roots /\
        GenInv.chunked_minor_major_fields_no_blue minor mh)
      (ensures
        GenInv.chunked_minor_major_fields_no_blue minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  let preserved (obj: U64.t) (j: nat)
    : Lemma
        (ensures
          Seq.mem obj (minor_objects minor) /\
          j < minor_wosize minor obj /\
          is_pointer_field (minor_read_field minor obj j) ==>
          Seq.mem ((minor_read_field minor obj j) <: obj_addr)
                  (MH.major_objects grayed) /\
          ~(GenInv.chunked_is_blue grayed
              ((minor_read_field minor obj j) <: obj_addr)))
    =
    if Seq.mem obj (minor_objects minor) &&
       j < minor_wosize minor obj &&
       is_pointer_field (minor_read_field minor obj j)
    then begin
      let target = ((minor_read_field minor obj j) <: obj_addr) in
      GenInv.chunked_minor_major_fields_no_blue_elim minor mh obj j;
      assert (Seq.mem target (MH.major_objects mh));
      chunked_blue_status_preserved_by_gray_roots mh roots target;
      assert (Seq.mem target (MH.major_objects grayed));
      assert (~(GenInv.chunked_is_blue grayed target))
    end
  in
  FStar.Classical.forall_intro_2 preserved;
  GenInv.chunked_minor_major_fields_no_blue_intro minor grayed
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
private let chunked_cg_no_scan_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        CG.chunked_is_no_scan
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) target ==
        CG.chunked_is_no_scan mh target)
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed mh roots;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  MH.major_objects_member_header_read_some mh target;
  let hdr = Some?.v (MH.read_word_in_major mh (hd_address target)) in
  assert (MH.read_word_in_major mh (hd_address target) == Some hdr);
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_tag_of_object
    mh roots target;
  SweepDefs.chunked_read_header_step mh target;
  assert (SweepDefs.chunked_read_header mh target == Some hdr);
  SweepDefs.chunked_tag_of_object_some mh target hdr;
  CG.chunked_is_no_scan_header mh target hdr;
  assert (Seq.mem target (MH.major_objects grayed));
  MH.major_objects_member_header_read_some grayed target;
  let hdr' = Some?.v (MH.read_word_in_major grayed (hd_address target)) in
  assert (MH.read_word_in_major grayed (hd_address target) == Some hdr');
  SweepDefs.chunked_read_header_step grayed target;
  assert (SweepDefs.chunked_read_header grayed target == Some hdr');
  SweepDefs.chunked_tag_of_object_some grayed target hdr';
  CG.chunked_is_no_scan_header grayed target hdr';
  assert (SweepDefs.chunked_tag_of_object grayed target ==
          SweepDefs.chunked_tag_of_object mh target);
  assert (getTag hdr' == getTag hdr);
  assert (CG.chunked_is_no_scan grayed target ==
          CG.chunked_is_no_scan mh target)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_no_scan_invariant_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_major_roots_nonblue mh roots /\
        GenInv.chunked_no_scan_invariant mh)
      (ensures
        GenInv.chunked_no_scan_invariant
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed mh roots;
  let no_pointer (src: obj_addr) (idx: nat)
    (field_addr: hp_addr) (raw: U64.t)
    : Lemma
        (requires
          Seq.mem src (MH.major_objects grayed) /\
          CG.chunked_is_no_scan grayed src /\
          ~(GenInv.chunked_is_blue grayed src) /\
          idx < CG.chunked_wosize_nat_of_object grayed src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major grayed field_addr == Some raw)
        (ensures ~(is_pointer_field raw))
    =
    assert (Seq.mem src (MH.major_objects mh));
    chunked_blue_status_preserved_by_gray_roots mh roots src;
    assert (~(GenInv.chunked_is_blue mh src));
    chunked_cg_no_scan_preserved_by_gray_roots mh roots src;
    assert (CG.chunked_is_no_scan mh src);
    chunked_wosize_nat_agrees_with_sweep mh src;
    chunked_wosize_nat_agrees_with_sweep grayed src;
    ChunkedMajorGCRoots.chunked_gray_roots_preserves_wosize_of_object
      mh roots src;
    assert (idx < CG.chunked_wosize_nat_of_object mh src);
    chunked_field_slot_mark_index_facts grayed src idx field_addr;
    let field_i: (i: U64.t{U64.v i >= 1}) =
      U64.uint_to_t (idx + 1) in
    U64.vu_inv (idx + 1);
    assert (U64.v field_i == idx + 1);
    assert (U64.v field_i <=
            U64.v (SweepDefs.chunked_wosize_of_object mh src));
    assert (U64.v field_addr ==
            U64.v (hd_address src) + U64.v mword * U64.v field_i);
    ChunkedMajorGCRoots.chunked_gray_roots_preserves_field_read_back
      mh roots src field_i field_addr raw;
    GenInv.chunked_no_scan_invariant_elim
      mh src idx field_addr raw
  in
  FStar.Classical.forall_intro_4
    (FStar.Classical.move_requires_4 no_pointer);
  GenInv.chunked_no_scan_invariant_intro grayed
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_no_pointer_to_blue_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_major_roots_nonblue mh roots /\
        GenInv.chunked_no_pointer_to_blue mh)
      (ensures
        GenInv.chunked_no_pointer_to_blue
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed mh roots;
  let no_blue_raw (src dst: obj_addr) (idx: nat)
    (field_addr: hp_addr)
    : Lemma
        (ensures
          forall (raw: U64.t).
          Seq.mem src (MH.major_objects grayed) /\
          ~(GenInv.chunked_is_blue grayed src) /\
          idx < CG.chunked_wosize_nat_of_object grayed src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major grayed field_addr == Some raw /\
          Seq.mem dst (MH.major_objects grayed) /\
          is_pointer_to raw dst ==>
          ~(GenInv.chunked_is_blue grayed dst))
    =
    let no_blue_one (raw: U64.t)
      : Lemma
          (requires
            Seq.mem src (MH.major_objects grayed) /\
            ~(GenInv.chunked_is_blue grayed src) /\
            idx < CG.chunked_wosize_nat_of_object grayed src /\
            CG.chunked_major_field_slot src idx == Some field_addr /\
            MH.read_word_in_major grayed field_addr == Some raw /\
            Seq.mem dst (MH.major_objects grayed) /\
            is_pointer_to raw dst)
          (ensures ~(GenInv.chunked_is_blue grayed dst))
      =
      assert (Seq.mem src (MH.major_objects mh));
      assert (Seq.mem dst (MH.major_objects mh));
      chunked_blue_status_preserved_by_gray_roots mh roots src;
      assert (~(GenInv.chunked_is_blue mh src));
      chunked_wosize_nat_agrees_with_sweep mh src;
      chunked_wosize_nat_agrees_with_sweep grayed src;
      ChunkedMajorGCRoots.chunked_gray_roots_preserves_wosize_of_object
        mh roots src;
      assert (idx < CG.chunked_wosize_nat_of_object mh src);
      chunked_field_slot_mark_index_facts grayed src idx field_addr;
      let field_i: (i: U64.t{U64.v i >= 1}) =
        U64.uint_to_t (idx + 1) in
      U64.vu_inv (idx + 1);
      assert (U64.v field_i == idx + 1);
      assert (U64.v field_i <=
              U64.v (SweepDefs.chunked_wosize_of_object mh src));
      assert (U64.v field_addr ==
              U64.v (hd_address src) + U64.v mword * U64.v field_i);
      ChunkedMajorGCRoots.chunked_gray_roots_preserves_field_read_back
        mh roots src field_i field_addr raw;
      GenInv.chunked_no_pointer_to_blue_elim
        mh src dst idx field_addr raw;
      chunked_blue_status_preserved_by_gray_roots mh roots dst;
      assert (~(GenInv.chunked_is_blue grayed dst))
    in
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires no_blue_one)
  in
  FStar.Classical.forall_intro_4 no_blue_raw;
  GenInv.chunked_no_pointer_to_blue_intro grayed
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_minor_fields_no_infix_targets_preserved_by_gray_roots
  (minor: minor_state)
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_major_roots_nonblue mh roots /\
        GenInv.chunked_major_minor_fields_no_infix_targets minor mh)
      (ensures
        GenInv.chunked_major_minor_fields_no_infix_targets minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed mh roots;
  let no_infix (src: obj_addr) (idx: nat)
    (field_addr: hp_addr) (raw: U64.t)
    : Lemma
        (requires
          Seq.mem src (MH.major_objects grayed) /\
          ~(GenInv.chunked_is_blue grayed src) /\
          ~(CG.chunked_is_no_scan grayed src) /\
          idx < CG.chunked_wosize_nat_of_object grayed src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major grayed field_addr == Some raw /\
          Promote.is_minor_pointer (to_minor_offset raw))
        (ensures ~(is_infix_in_minor minor (to_minor_offset raw)))
    =
    assert (Seq.mem src (MH.major_objects mh));
    chunked_blue_status_preserved_by_gray_roots mh roots src;
    assert (~(GenInv.chunked_is_blue mh src));
    chunked_cg_no_scan_preserved_by_gray_roots mh roots src;
    assert (~(CG.chunked_is_no_scan mh src));
    chunked_wosize_nat_agrees_with_sweep mh src;
    chunked_wosize_nat_agrees_with_sweep grayed src;
    ChunkedMajorGCRoots.chunked_gray_roots_preserves_wosize_of_object
      mh roots src;
    assert (idx < CG.chunked_wosize_nat_of_object mh src);
    chunked_field_slot_mark_index_facts grayed src idx field_addr;
    let field_i: (i: U64.t{U64.v i >= 1}) =
      U64.uint_to_t (idx + 1) in
    U64.vu_inv (idx + 1);
    assert (U64.v field_i == idx + 1);
    assert (U64.v field_i <=
            U64.v (SweepDefs.chunked_wosize_of_object mh src));
    assert (U64.v field_addr ==
            U64.v (hd_address src) + U64.v mword * U64.v field_i);
    ChunkedMajorGCRoots.chunked_gray_roots_preserves_field_read_back
      mh roots src field_i field_addr raw;
    GenInv.chunked_major_minor_fields_no_infix_targets_elim
      minor mh src idx field_addr raw
  in
  FStar.Classical.forall_intro_4
    (FStar.Classical.move_requires_4 no_infix);
  GenInv.chunked_major_minor_fields_no_infix_targets_intro minor grayed
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
private let chunked_gray_roots_preserves_free_link_read
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (fp: obj_addr)
  (next: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem fp (MH.major_objects mh) /\
        (match MH.read_word_in_major mh (hd_address fp) with
         | Some hdr -> U64.v (getWosize hdr) >= 1
         | None -> False) /\
        MH.read_word_in_major mh fp == Some next)
      (ensures
        MH.read_word_in_major
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) fp == Some next)
  =
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed mh roots;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  let hdr = Some?.v (MH.read_word_in_major mh (hd_address fp)) in
  assert (MH.read_word_in_major mh (hd_address fp) == Some hdr);
  SweepDefs.chunked_read_header_step mh fp;
  assert (SweepDefs.chunked_read_header mh fp == Some hdr);
  SweepDefs.chunked_wosize_of_object_some mh fp hdr;
  assert (U64.v (SweepDefs.chunked_wosize_of_object mh fp) >= 1);
  let field_i: (i: U64.t{U64.v i >= 1}) = 1UL in
  assert (U64.v field_i == 1);
  assert (U64.v field_i <=
          U64.v (SweepDefs.chunked_wosize_of_object mh fp));
  hd_address_spec fp;
  assert_norm (U64.v mword == 8);
  assert (U64.v (U64.mul mword field_i) ==
          U64.v mword * U64.v field_i);
  assert (U64.v (hd_address fp) + U64.v mword == U64.v fp);
  assert (U64.v fp ==
          U64.v (hd_address fp) + U64.v mword * U64.v field_i);
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_field_read
    mh roots fp field_i fp next
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
private let chunked_gray_roots_preserves_free_header_wosize_ge_one
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (fp: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem fp (MH.major_objects mh) /\
        (match MH.read_word_in_major mh (hd_address fp) with
         | Some hdr -> U64.v (getWosize hdr) >= 1
         | None -> False))
      (ensures
        (match
          MH.read_word_in_major
            (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
            (hd_address fp)
         with
         | Some hdr -> U64.v (getWosize hdr) >= 1
         | None -> False))
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed mh roots;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  let hdr = Some?.v (MH.read_word_in_major mh (hd_address fp)) in
  assert (MH.read_word_in_major mh (hd_address fp) == Some hdr);
  SweepDefs.chunked_read_header_step mh fp;
  assert (SweepDefs.chunked_read_header mh fp == Some hdr);
  SweepDefs.chunked_wosize_of_object_some mh fp hdr;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_wosize_of_object
    mh roots fp;
  assert (Seq.mem fp (MH.major_objects grayed));
  MH.major_objects_member_header_read_some grayed fp;
  let hdr' = Some?.v (MH.read_word_in_major grayed (hd_address fp)) in
  assert (MH.read_word_in_major grayed (hd_address fp) == Some hdr');
  SweepDefs.chunked_read_header_step grayed fp;
  assert (SweepDefs.chunked_read_header grayed fp == Some hdr');
  SweepDefs.chunked_wosize_of_object_some grayed fp hdr';
  assert (U64.v (getWosize hdr') == U64.v (getWosize hdr));
  assert (U64.v (getWosize hdr') >= 1)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
private let chunked_gray_roots_preserves_free_block_fit_current
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (fp: obj_addr)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        fuel > 0 /\
        U64.v fp >= U64.v mword /\
        U64.v fp < heap_size /\
        U64.v fp % U64.v mword == 0 /\
        Seq.mem fp (MH.major_objects mh) /\
        SpecMajorAlloc.major_fl_blocks_fit mh fp fuel)
      (ensures
        (let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
         let base = hd_address fp in
         let idx = MH.lookup_chunk_index_value grayed base in
         MH.lookup_chunk_index grayed base == Some idx /\
         idx < Seq.length grayed /\
         MH.word_in_chunk (Seq.index grayed idx) base /\
         (match MH.read_word_in_major grayed base with
          | Some hdr ->
            U64.v base +
              (1 + U64.v (getWosize hdr)) * U64.v mword <=
              MH.chunk_end (Seq.index grayed idx)
          | None -> False)))
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  let base = hd_address fp in
  SpecMajorAlloc.major_fl_blocks_fit_current mh fp fuel;
  let idx = MH.lookup_chunk_index_value mh base in
  assert (MH.lookup_chunk_index mh base == Some idx);
  assert (idx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh idx) base);
  let hdr = Some?.v (MH.read_word_in_major mh base) in
  assert (MH.read_word_in_major mh base == Some hdr);
  assert (U64.v base + (1 + U64.v (getWosize hdr)) * U64.v mword <=
          MH.chunk_end (Seq.index mh idx));
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed mh roots;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_ranges mh roots;
  RangePres.same_chunk_ranges_word_in_chunk mh grayed idx base;
  MH.lookup_chunk_index_word_in_chunk grayed base idx;
  assert (MH.lookup_chunk_index grayed base == Some idx);
  assert (MH.lookup_chunk_index_value grayed base == idx);
  assert (Seq.mem fp (MH.major_objects mh));
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_wosize_of_object
    mh roots fp;
  SweepDefs.chunked_read_header_step mh fp;
  assert (SweepDefs.chunked_read_header mh fp == Some hdr);
  SweepDefs.chunked_wosize_of_object_some mh fp hdr;
  assert (Seq.mem fp (MH.major_objects grayed));
  MH.major_objects_member_header_read_some grayed fp;
  let hdr' = Some?.v (MH.read_word_in_major grayed base) in
  assert (MH.read_word_in_major grayed base == Some hdr');
  SweepDefs.chunked_read_header_step grayed fp;
  assert (SweepDefs.chunked_read_header grayed fp == Some hdr');
  SweepDefs.chunked_wosize_of_object_some grayed fp hdr';
  assert (U64.v (getWosize hdr') == U64.v (getWosize hdr));
  RangePres.same_chunk_ranges_index mh grayed idx;
  assert (MH.chunk_end (Seq.index grayed idx) ==
          MH.chunk_end (Seq.index mh idx));
  assert (U64.v base + (1 + U64.v (getWosize hdr')) * U64.v mword <=
          MH.chunk_end (Seq.index grayed idx))
#pop-options

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
private let major_fl_blocks_fit_fuel_0_any
  (mh: MH.major_heap)
  (fp: U64.t)
  : Lemma (ensures SpecMajorAlloc.major_fl_blocks_fit mh fp 0)
  = ()

private let major_fl_valid_current_pointer_mem
  (mh: MH.major_heap)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        fp <> 0UL /\
        U64.v fp >= U64.v mword /\
        U64.v fp < heap_size /\
        U64.v fp % U64.v mword == 0 /\
        SpecMajorAlloc.major_fl_valid mh fp fuel)
      (ensures
        (let obj: obj_addr = fp in
        MH.is_major_pointer mh fp /\
        Seq.mem obj (MH.major_objects mh)))
  =
    assert (fuel <> 0)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
private let rec chunked_free_list_shape_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        SpecMajorAlloc.major_fl_valid mh fp fuel /\
        SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
        SpecMajorAlloc.major_fl_blocks_fit mh fp fuel)
      (ensures
        (let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
        SpecMajorAlloc.major_fl_valid grayed fp fuel /\
        SpecMajorAlloc.major_fl_above_zero grayed fp fuel /\
        SpecMajorAlloc.major_fl_blocks_fit grayed fp fuel))
      (decreases fuel)
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  if fuel = 0 then begin
    SpecMajorAlloc.major_fl_valid_zero grayed fp;
    SpecMajorAlloc.major_fl_above_zero_fuel_0 grayed fp;
    major_fl_blocks_fit_fuel_0_any grayed fp
  end
  else if fp = 0UL then begin
    SpecMajorAlloc.major_fl_valid_null grayed fuel;
    SpecMajorAlloc.major_fl_above_zero_null grayed fuel;
    SpecMajorAlloc.major_fl_blocks_fit_null grayed fuel
  end
  else begin
    SpecMajorAlloc.major_fl_above_zero_current mh fp fuel;
    assert (U64.v fp >= U64.v zero_addr + U64.v mword);
    assert (U64.v fp >= U64.v mword);
    assert (U64.v fp < heap_size);
    assert (U64.v fp % U64.v mword == 0);
    let obj: obj_addr = fp in
    major_fl_valid_current_pointer_mem mh fp fuel;
    assert (MH.is_major_pointer mh fp);
    assert (Seq.mem obj (MH.major_objects mh));
    SpecMajorAlloc.major_fl_valid_gives_wosize mh fp fuel;
    assert (obj == fp);
    assert (hd_address obj == hd_address (fp <: obj_addr));
    assert (match MH.read_word_in_major mh (hd_address obj) with
            | Some hdr -> U64.v (getWosize hdr) >= 1
            | None -> False);
    chunked_gray_roots_preserves_free_header_wosize_ge_one
      mh roots obj;
    SpecMajorAlloc.major_fl_valid_next mh fp fuel;
    assert (Seq.mem obj (MH.major_objects mh));
    SpecMajorAlloc.major_fl_blocks_fit_current mh obj fuel;
    match MH.read_word_in_major mh obj with
    | None -> assert False
    | Some next ->
      assert (MH.read_word_in_major mh obj == Some next);
      assert (next <> fp);
      SpecMajorAlloc.major_fl_above_zero_next mh obj fuel next;
      SpecMajorAlloc.major_fl_blocks_fit_next mh obj fuel next;
      chunked_free_list_shape_preserved_by_gray_roots
        mh roots next (fuel - 1);
      chunked_gray_roots_preserves_free_link_read mh roots obj next;
      assert (MH.read_word_in_major grayed obj == Some next);
      ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects mh roots;
      ChunkedMajorGCRoots.chunked_gray_roots_preserves_ranges mh roots;
      assert (MH.is_major_pointer mh fp);
      RangePres.same_chunk_ranges_preserves_is_major_pointer mh grayed fp;
      assert (MH.is_major_pointer mh fp == MH.is_major_pointer grayed fp);
      assert (MH.is_major_pointer grayed fp);
      assert (Seq.mem obj (MH.major_objects grayed));
      match MH.read_word_in_major grayed (hd_address obj) with
      | None -> assert False
      | Some hdr' ->
        assert (MH.read_word_in_major grayed (hd_address obj) == Some hdr');
        assert (U64.v (getWosize hdr') >= 1);
        SpecMajorAlloc.major_fl_valid_step grayed fp fuel;
        SpecMajorAlloc.major_fl_above_zero_step grayed obj fuel next;
        chunked_gray_roots_preserves_free_block_fit_current
          mh roots obj fuel;
        SpecMajorAlloc.major_fl_blocks_fit_step grayed obj fuel hdr' next
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_alloc_shape_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires GenInv.chunked_major_alloc_shape mh fp fuel)
      (ensures
        GenInv.chunked_major_alloc_shape
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          fp fuel)
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  GenInv.chunked_major_alloc_shape_elim mh fp fuel;
  chunked_free_list_shape_preserved_by_gray_roots mh roots fp fuel;
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed mh roots;
  GenInv.chunked_major_alloc_shape_intro grayed fp fuel
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_collection_heap_shape_preserved_by_gray_roots
  (minor: minor_state)
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp fuel /\
        chunked_major_roots_nonblue mh roots)
      (ensures
        GenInv.chunked_collection_heap_shape minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          fp fuel)
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  GenInv.chunked_collection_heap_shape_elim minor mh fp fuel;
  GenInv.chunked_major_alloc_shape_elim mh fp fuel;
  assert (MH.well_formed_major_heap mh);
  chunked_major_alloc_shape_preserved_by_gray_roots mh roots fp fuel;
  chunked_no_black_objects_preserved_by_gray_roots mh roots;
  chunked_no_scan_invariant_preserved_by_gray_roots mh roots;
  chunked_no_pointer_to_blue_preserved_by_gray_roots mh roots;
  chunked_minor_major_fields_no_blue_preserved_by_gray_roots minor mh roots;
  chunked_major_minor_fields_no_infix_targets_preserved_by_gray_roots
    minor mh roots;
  GenInv.chunked_collection_heap_shape_intro minor grayed fp fuel
#pop-options

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

let chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_field_policies
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
        chunked_major_field_targets_non_infix mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMark.chunked_count_non_black mh /\
        ChunkedMarkLive.chunked_roots_gray_or_black mh roots)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  chunked_major_field_targets_non_infix_implies_vertex_edge_targets_non_infix mh;
  chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_vertex_targets
    minor mh fp shape_fuel roots cap mark_fuel

let chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_policy
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        chunked_major_edge_gen_field_witness mh /\
        chunked_major_field_targets_non_infix mh /\
        chunked_major_gc_bounded_liveness_policy
          mh roots cap mark_fuel)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  chunked_major_gc_bounded_liveness_policy_elim
    mh roots cap mark_fuel;
  chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_field_policies
    minor mh fp shape_fuel roots cap mark_fuel

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_grayed_collection_shape_policy
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenInv.chunked_collection_heap_shape minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          fp shape_fuel /\
        chunked_major_edge_gen_field_witness
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) /\
        chunked_major_field_targets_non_infix
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel > 0 /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
            cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  let grayed = ChunkedMajorGCRoots.chunked_gray_roots mh roots in
  let (mh_final, fp_final) =
    ChunkedMajorGC.chunked_major_gc_bounded grayed cap mark_fuel in
  let live0 =
    ChunkedMajorGCCorr.chunked_major_initial_reachable_live mh roots in
  let live1 =
    ChunkedMajorGCCorr.chunked_major_initial_reachable_live grayed roots in
  let all_vertices (v: obj_addr) =
    ChunkedMajorGraph.chunked_major_vertex mh v in
  let all_vertices_mem (v: obj_addr)
    : Lemma
        (requires all_vertices v)
        (ensures Seq.mem v (MH.major_objects mh))
    =
    ChunkedMajorGraph.chunked_major_vertex_elim mh v
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires all_vertices_mem);
  ChunkedMajorGCRoots.chunked_gray_roots_live_subgraph_preserved
    mh roots all_vertices;
  let all_vertices_cover (v: obj_addr)
    : Lemma
        (requires ChunkedMajorGraph.chunked_major_vertex mh v)
        (ensures all_vertices v)
    =
    ()
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires all_vertices_cover);
  let live0_mem (target: obj_addr)
    : Lemma
        (requires live0 target)
        (ensures Seq.mem target (MH.major_objects mh))
    =
    ChunkedMajorGCCorr.chunked_major_initial_reachable_live_elim
      mh roots target;
    ChunkedMajorReach.chunked_major_reachable_from_roots_vertex
      mh roots target;
    ChunkedMajorGraph.chunked_major_vertex_elim mh target
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires live0_mem);
  ChunkedMajorGCRoots.chunked_gray_roots_live_subgraph_preserved
    mh roots live0;
  let live0_to_live1 (target: obj_addr)
    : Lemma
        (requires live0 target)
        (ensures live1 target)
    =
    ChunkedMajorGCCorr.chunked_major_initial_reachable_live_elim
      mh roots target;
    ChunkedMajorReach.chunked_major_reachable_from_roots_preserved_by_live_subgraph
      mh grayed all_vertices roots target;
    ChunkedMajorGCCorr.chunked_major_initial_reachable_live_intro
      grayed roots target
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires live0_to_live1);
  chunked_major_gc_bounded_liveness_policy_after_gray_roots
    mh roots cap mark_fuel;
  chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_policy
    minor grayed fp shape_fuel roots cap mark_fuel;
  ChunkedMajorGraph.chunked_major_live_subgraph_preserved_subset
    grayed mh_final live1 live0;
  ChunkedMajorGraph.chunked_major_live_subgraph_preserved_trans
    mh grayed mh_final live0
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_original_field_policies
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenInv.chunked_collection_heap_shape minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          fp shape_fuel /\
        chunked_major_edge_gen_field_witness mh /\
        chunked_major_field_targets_non_infix mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel > 0 /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
            cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  chunked_major_edge_gen_field_witness_preserved_by_gray_roots mh roots;
  chunked_major_field_targets_non_infix_preserved_by_gray_roots mh roots;
  chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_grayed_collection_shape_policy
    minor mh fp shape_fuel roots cap mark_fuel
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_original_shape
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        chunked_major_roots_nonblue mh roots /\
        chunked_major_edge_gen_field_witness mh /\
        chunked_major_field_targets_non_infix mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel > 0 /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
            cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  chunked_collection_heap_shape_preserved_by_gray_roots
    minor mh roots fp shape_fuel;
  GenInv.chunked_collection_heap_shape_elim minor mh fp shape_fuel;
  GenInv.chunked_major_alloc_shape_elim mh fp shape_fuel;
  chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_original_field_policies
    minor mh fp shape_fuel roots cap mark_fuel
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_original_shape_policy
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        chunked_major_roots_nonblue mh roots /\
        chunked_major_edge_gen_field_witness mh /\
        chunked_major_field_targets_non_infix mh /\
        chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
            cap mark_fuel in
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  chunked_major_gc_bounded_after_gray_roots_policy_elim
    mh roots cap mark_fuel;
  chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_original_shape
    minor mh fp shape_fuel roots cap mark_fuel
#pop-options
