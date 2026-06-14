module GC.Spec.ChunkedMajorGC.MarkLiveness

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BStackReady = GC.Spec.ChunkedMarkBounded.StackReady
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph

val chunked_roots_gray_or_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : prop

val chunked_roots_gray_or_black_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (root: obj_addr)
  : Lemma
      (requires
        chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGraph.chunked_major_vertex mh root /\
        Seq.mem root roots)
      (ensures
        BDefs.chunked_is_gray mh root \/
        SweepDefs.chunked_is_black mh root)

val chunked_mark_bounded_root_ready
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  (root: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGraph.chunked_major_vertex mh root /\
        Seq.mem root roots)
      (ensures
        BPres.chunked_mark_bounded_marks_target_ready
          mh cap fuel root)
