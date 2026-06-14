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

val chunked_count_non_black_in_bound
  (mh: MH.major_heap)
  (objs: Seq.seq obj_addr)
  : Lemma
      (ensures
        BDefs.chunked_count_non_black_in mh objs <= Seq.length objs)

val chunked_count_non_black_bound
  (mh: MH.major_heap)
  : Lemma
      (ensures
        BDefs.chunked_count_non_black mh <= Seq.length (MH.major_objects mh))

val chunked_push_children_bounded_preserves_stack_member
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: FStar.UInt64.t{FStar.UInt64.v i >= 1})
  (ws: FStar.UInt64.t)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires Seq.mem target st)
      (ensures
        (let (_, st') =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         Seq.mem target st'))

val chunked_mark_step_bounded_preserves_tail_member
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        Seq.mem target (Seq.tail st))
      (ensures
        (let (_, st') =
          BDefs.chunked_mark_step_bounded mh st cap in
         Seq.mem target st'))

val chunked_stack_points_to_gray
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : GTot prop

val chunked_stack_points_to_gray_elim
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        chunked_stack_points_to_gray mh st /\
        Seq.mem target st)
      (ensures BDefs.chunked_is_gray mh target)

val chunked_stack_points_to_gray_empty
  (mh: MH.major_heap)
  : Lemma
      (ensures chunked_stack_points_to_gray mh Seq.empty)

val chunked_stack_points_to_gray_cons
  (mh: MH.major_heap)
  (target: obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        BDefs.chunked_is_gray mh target /\
        chunked_stack_points_to_gray mh st)
      (ensures
        chunked_stack_points_to_gray mh (Seq.cons target st))

val chunked_rescan_objects_preserves_stack_member
  (mh: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires Seq.mem target st)
      (ensures
        Seq.mem target
          (BDefs.chunked_rescan_objects mh objs st cap))

val chunked_rescan_objects_preserves_stack_gray
  (mh: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires chunked_stack_points_to_gray mh st)
      (ensures
        chunked_stack_points_to_gray mh
          (BDefs.chunked_rescan_objects mh objs st cap))

val chunked_rescan_objects_preserves_stack_no_dups
  (mh: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires GC.Spec.Mark.stack_no_dups st)
      (ensures
        GC.Spec.Mark.stack_no_dups
          (BDefs.chunked_rescan_objects mh objs st cap))

val chunked_rescan_objects_adds_gray_with_capacity
  (mh: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        Seq.mem target objs /\
        BDefs.chunked_is_gray mh target /\
        Seq.length st + Seq.length objs <= cap)
      (ensures
        Seq.mem target
          (BDefs.chunked_rescan_objects mh objs st cap))

val chunked_rescan_heap_adds_gray_with_capacity
  (mh: MH.major_heap)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        Seq.mem target (MH.major_objects mh) /\
        BDefs.chunked_is_gray mh target /\
        Seq.length (MH.major_objects mh) <= cap)
      (ensures
        Seq.mem target
          (BDefs.chunked_rescan_heap mh Seq.empty cap))

val chunked_rescan_heap_stack_no_dups
  (mh: MH.major_heap)
  (cap: nat)
  : Lemma
      (ensures
        GC.Spec.Mark.stack_no_dups
          (BDefs.chunked_rescan_heap mh Seq.empty cap))

val chunked_rescan_heap_stack_gray
  (mh: MH.major_heap)
  (cap: nat)
  : Lemma
      (ensures
        chunked_stack_points_to_gray mh
          (BDefs.chunked_rescan_heap mh Seq.empty cap))

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
