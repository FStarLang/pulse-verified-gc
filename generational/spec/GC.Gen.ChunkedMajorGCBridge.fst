module GC.Gen.ChunkedMajorGCBridge

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Gen.Base
open GC.Gen.MinorHeap

module MH = GC.Spec.MajorHeap
module Header = GC.Lib.Header
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph
module ChunkedMarkNoBlack = GC.Spec.ChunkedMarkBounded.NoBlackToWhite
module GenInv = GC.Gen.HeapInvariant

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
