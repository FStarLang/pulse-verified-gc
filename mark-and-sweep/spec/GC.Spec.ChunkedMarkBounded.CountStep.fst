module GC.Spec.ChunkedMarkBounded.CountStep

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BCount = GC.Spec.ChunkedMarkBounded.Count

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let chunked_mark_step_bounded_decreases_count
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        BDefs.chunked_is_gray mh (Seq.head st))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         BDefs.chunked_count_non_black mh' <
         BDefs.chunked_count_non_black mh))
  =
  let target = Seq.head st in
  let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
  BPres.chunked_mark_step_bounded_marks_head_black mh st cap;
  BCount.chunked_is_gray_not_black mh target;
  BPres.chunked_mark_step_bounded_preserves_major_objects mh st cap;
  let each_other (obj: obj_addr)
    : Lemma
        (requires Seq.mem obj (MH.major_objects mh) /\ obj <> target)
        (ensures
          SweepDefs.chunked_is_black mh' obj ==
          SweepDefs.chunked_is_black mh obj)
    =
    BPres.chunked_mark_step_bounded_preserves_other_black_status
      mh st cap obj
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_other);
  BCount.chunked_count_non_black_in_black_status_flip_decreases
    mh mh' (MH.major_objects mh) target;
  BDefs.chunked_count_non_black_equation mh;
  BDefs.chunked_count_non_black_equation mh';
  assert (MH.major_objects mh' == MH.major_objects mh)

