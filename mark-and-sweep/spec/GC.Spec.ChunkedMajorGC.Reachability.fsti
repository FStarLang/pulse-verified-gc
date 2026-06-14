module GC.Spec.ChunkedMajorGC.Reachability

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph

val chunked_major_reachable
  (mh: MH.major_heap)
  (x: obj_addr)
  (y: obj_addr)
  : prop

val chunked_major_reachable_refl
  (mh: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires ChunkedMajorGraph.chunked_major_vertex mh x)
      (ensures chunked_major_reachable mh x x)

val chunked_major_edge_reachable
  (mh: MH.major_heap)
  (x: obj_addr)
  (y: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGraph.chunked_major_vertex mh x /\
        ChunkedMajorGraph.chunked_major_vertex mh y /\
        ChunkedMajorGraph.chunked_major_edge mh x y)
      (ensures chunked_major_reachable mh x y)

val chunked_major_reachable_extend_edge
  (mh: MH.major_heap)
  (x y z: obj_addr)
  : Lemma
      (requires
        chunked_major_reachable mh x y /\
        ChunkedMajorGraph.chunked_major_vertex mh z /\
        ChunkedMajorGraph.chunked_major_edge mh y z)
      (ensures chunked_major_reachable mh x z)

val chunked_major_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (x: obj_addr)
  : prop

val chunked_major_root_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (x: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGraph.chunked_major_vertex mh x /\
        Seq.mem x roots)
      (ensures chunked_major_reachable_from_roots mh roots x)

val chunked_major_reachable_from_roots_extend_edge
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (x y: obj_addr)
  : Lemma
      (requires
        chunked_major_reachable_from_roots mh roots x /\
        ChunkedMajorGraph.chunked_major_vertex mh y /\
        ChunkedMajorGraph.chunked_major_edge mh x y)
      (ensures chunked_major_reachable_from_roots mh roots y)

val chunked_gray_black_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : prop

val chunked_gray_black_reachable_init
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        (forall (x: obj_addr).
          ChunkedMajorGraph.chunked_major_vertex mh x /\
          (BDefs.chunked_is_gray mh x \/
           SweepDefs.chunked_is_black mh x) ==>
          Seq.mem x roots))
      (ensures chunked_gray_black_reachable mh roots)
