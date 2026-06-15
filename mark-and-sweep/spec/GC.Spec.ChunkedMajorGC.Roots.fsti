module GC.Spec.ChunkedMajorGC.Roots

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs
module MarkLive = GC.Spec.ChunkedMajorGC.MarkLiveness

val chunked_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : GTot MH.major_heap

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

val chunked_gray_roots_roots_gray_or_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires MH.well_formed_major_heap mh)
      (ensures
        MarkLive.chunked_roots_gray_or_black
          (chunked_gray_roots mh roots) roots)
