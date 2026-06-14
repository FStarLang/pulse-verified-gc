module GC.Spec.ChunkedMarkBounded.StackReady

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady

val chunked_mark_inner_loop_marks_stack_member_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        fuel >= BDefs.chunked_count_non_black mh /\
        BPres.chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        BReady.chunked_bounded_stack_props mh st /\
        Seq.mem target st)
      (ensures
        BPres.chunked_mark_inner_loop_marks_target_ready
          mh st cap fuel target)

val chunked_mark_bounded_marks_rescan_member_ready
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.mem target (MH.major_objects mh) /\
        BDefs.chunked_is_gray mh target /\
        Seq.length (MH.major_objects mh) <= cap)
      (ensures
        BPres.chunked_mark_bounded_marks_target_ready mh cap fuel target)
