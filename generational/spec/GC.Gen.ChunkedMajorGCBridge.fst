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
module ChunkedMarkTargetReady = GC.Spec.ChunkedMarkBounded.TargetReady
module ChunkedMarkLive = GC.Spec.ChunkedMajorGC.MarkLiveness
module ChunkedMajorGCRoots = GC.Spec.ChunkedMajorGC.Roots
module ChunkedMarkEdge = GC.Spec.ChunkedMarkBounded.EdgeInvariant
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph
module ChunkedMajorGC = GC.Spec.ChunkedMajorGC.Defs
module ChunkedMajorGCCorr = GC.Spec.ChunkedMajorGC.Correctness
module ChunkedMajorReach = GC.Spec.ChunkedMajorGC.Reachability
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
