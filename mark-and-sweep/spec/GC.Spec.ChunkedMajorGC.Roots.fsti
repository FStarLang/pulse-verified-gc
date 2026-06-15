module GC.Spec.ChunkedMajorGC.Roots

module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkLive = GC.Spec.ChunkedMajorGC.MarkLiveness
module RangePres = GC.Spec.ChunkedSweepCoalesce.RangePreservation
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph

val chunked_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : GTot MH.major_heap

val chunked_gray_roots_empty
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length roots = 0)
      (ensures chunked_gray_roots mh roots == mh)

val chunked_gray_roots_cons_mem
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length roots > 0 /\
        Seq.mem (Seq.head roots) (MH.major_objects mh))
      (ensures
        chunked_gray_roots mh roots ==
        chunked_gray_roots
          (MarkDefs.chunked_make_gray mh (Seq.head roots))
          (Seq.tail roots))

val chunked_gray_roots_cons_miss
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length roots > 0 /\
        ~(Seq.mem (Seq.head roots) (MH.major_objects mh)))
      (ensures
        chunked_gray_roots mh roots ==
        chunked_gray_roots mh (Seq.tail roots))

val chunked_gray_roots_preserves_major_objects
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires MH.well_formed_major_heap mh)
      (ensures
        MH.major_objects (chunked_gray_roots mh roots) ==
        MH.major_objects mh)

val chunked_gray_roots_preserves_well_formed
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires MH.well_formed_major_heap mh)
      (ensures MH.well_formed_major_heap (chunked_gray_roots mh roots))

val chunked_gray_roots_preserves_gray_or_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        (GC.Spec.ChunkedMarkBounded.Defs.chunked_is_gray mh target \/
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target))
      (ensures
        GC.Spec.ChunkedMarkBounded.Defs.chunked_is_gray
          (chunked_gray_roots mh roots) target \/
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black
          (chunked_gray_roots mh roots) target)

val chunked_gray_roots_preserves_blue_status
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        (forall (root: obj_addr).
          Seq.mem root roots /\
          Seq.mem root (MH.major_objects mh) ==>
          ~(GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_blue mh root)))
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_blue
          (chunked_gray_roots mh roots) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_blue mh target)

val chunked_gray_roots_preserves_black_status
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        (forall (root: obj_addr).
          Seq.mem root roots /\
          Seq.mem root (MH.major_objects mh) ==>
          ~(GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh root)))
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black
          (chunked_gray_roots mh roots) target ==
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target)

val chunked_gray_roots_preserves_ranges
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (ensures
        RangePres.same_chunk_ranges
          mh (chunked_gray_roots mh roots))

val chunked_gray_roots_pointer_classification_preserved
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (ensures
        ChunkedMajorGraph.chunked_major_pointer_classification_preserved
          mh (chunked_gray_roots mh roots))

val chunked_gray_roots_preserves_wosize_of_object
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        SweepDefs.chunked_wosize_of_object
          (chunked_gray_roots mh roots) target ==
        SweepDefs.chunked_wosize_of_object mh target)

val chunked_gray_roots_preserves_get_field
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  (i: FStar.UInt64.t{FStar.UInt64.v i >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        FStar.UInt64.v i <=
          FStar.UInt64.v (SweepDefs.chunked_wosize_of_object mh target))
      (ensures
        MarkDefs.chunked_get_field
          (chunked_gray_roots mh roots) target i ==
        MarkDefs.chunked_get_field mh target i)

val chunked_gray_roots_preserves_field_read
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  (i: FStar.UInt64.t{FStar.UInt64.v i >= 1})
  (field_addr: hp_addr)
  (old: FStar.UInt64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        FStar.UInt64.v i <=
          FStar.UInt64.v (SweepDefs.chunked_wosize_of_object mh target) /\
        FStar.UInt64.v field_addr ==
          FStar.UInt64.v (hd_address target) +
          FStar.UInt64.v mword * FStar.UInt64.v i /\
        MH.read_word_in_major mh field_addr == Some old)
      (ensures
        MH.read_word_in_major
          (chunked_gray_roots mh roots) field_addr == Some old)

val chunked_gray_roots_preserves_field_read_back
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  (i: FStar.UInt64.t{FStar.UInt64.v i >= 1})
  (field_addr: hp_addr)
  (old: FStar.UInt64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        FStar.UInt64.v i <=
          FStar.UInt64.v (SweepDefs.chunked_wosize_of_object mh target) /\
        FStar.UInt64.v field_addr ==
          FStar.UInt64.v (hd_address target) +
          FStar.UInt64.v mword * FStar.UInt64.v i /\
        MH.read_word_in_major
          (chunked_gray_roots mh roots) field_addr == Some old)
      (ensures MH.read_word_in_major mh field_addr == Some old)

val chunked_gray_roots_preserves_no_scan_status
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        MarkDefs.chunked_is_no_scan
          (chunked_gray_roots mh roots) target ==
        MarkDefs.chunked_is_no_scan mh target)

val chunked_gray_roots_preserves_tag_of_object
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        SweepDefs.chunked_tag_of_object
          (chunked_gray_roots mh roots) target ==
        SweepDefs.chunked_tag_of_object mh target)

val chunked_gray_roots_preserves_infix_status
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        SweepDefs.chunked_is_infix
          (chunked_gray_roots mh roots) target ==
        SweepDefs.chunked_is_infix mh target)

val chunked_gray_roots_field_preserved
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedMajorGraph.chunked_major_field_preserved
          mh (chunked_gray_roots mh roots) target)

val chunked_gray_roots_live_subgraph_preserved
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        (forall (target: obj_addr).
          live target ==> Seq.mem target (MH.major_objects mh)))
      (ensures
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh (chunked_gray_roots mh roots) live)

val chunked_gray_roots_roots_gray_or_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires MH.well_formed_major_heap mh)
      (ensures
        MarkLive.chunked_roots_gray_or_black
          (chunked_gray_roots mh roots) roots)
