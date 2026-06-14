module GC.Spec.ChunkedMarkBounded.TargetReady

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation

val chunked_count_non_black_in_has_nonblack
  (mh: MH.major_heap)
  (target: obj_addr)
  (objs: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.mem target objs /\
        ~ (SweepDefs.chunked_is_black mh target))
      (ensures
        BDefs.chunked_count_non_black_in mh objs > 0)

val chunked_count_non_black_has_nonblack
  (mh: MH.major_heap)
  (target: obj_addr)
  : Lemma
      (requires
        Seq.mem target (MH.major_objects mh) /\
        ~ (SweepDefs.chunked_is_black mh target))
      (ensures
        BDefs.chunked_count_non_black mh > 0)

val chunked_mark_bounded_marks_rescan_head_ready
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        (let st =
          BDefs.chunked_rescan_heap mh Seq.empty cap in
         Seq.length st > 0 /\
         target == Seq.head st /\
         Seq.mem target (MH.major_objects mh)))
      (ensures
        BPres.chunked_mark_bounded_marks_target_ready mh cap fuel target)
