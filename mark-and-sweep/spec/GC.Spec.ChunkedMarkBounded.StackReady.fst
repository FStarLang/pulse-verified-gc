module GC.Spec.ChunkedMarkBounded.StackReady

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module Fields = GC.Spec.Fields
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkPres = GC.Spec.ChunkedMark.Preservation
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady
module BCountStep = GC.Spec.ChunkedMarkBounded.CountStep
module BStackStep = GC.Spec.ChunkedMarkBounded.StackStep

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

let nat_pred_ge_of_decrease
    (fuel count count': nat)
  : Lemma
      (requires
        fuel > 0 /\
        fuel >= count /\
        count' < count)
      (ensures fuel - 1 >= count')
  = ()

let seq_mem_tail_of_nonhead (#a:eqtype)
    (s: Seq.seq a)
    (x: a)
  : Lemma
      (requires
        Seq.length s > 0 /\
        Seq.mem x s /\
        x <> Seq.head s)
      (ensures Seq.mem x (Seq.tail s))
  =
  let hd = Seq.head s in
  let tl = Seq.tail s in
  assert (s == Seq.cons hd tl);
  Fields.mem_cons_lemma x hd tl;
  assert (Seq.mem x (Seq.cons hd tl));
  assert (x = hd \/ Seq.mem x tl)

let rec chunked_mark_inner_loop_marks_stack_member_ready
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
      (decreases BDefs.chunked_count_non_black mh)
  =
  if SweepDefs.chunked_is_black mh target then
    BPres.chunked_mark_inner_loop_marks_black_ready mh st cap fuel target
  else begin
    BReady.chunked_bounded_stack_props_objects mh st;
    MarkPres.stack_objects_in_major_elim mh st target;
    BReady.chunked_bounded_stack_props_gray mh st;
    BReady.chunked_stack_points_to_gray_elim mh st target;
    BReady.chunked_count_non_black_has_nonblack mh target;
    assert (BDefs.chunked_count_non_black mh > 0);
    assert (fuel > 0);
    if Seq.length st = 0 then
      assert False
    else begin
      nat_nonzero_pos (Seq.length st);
      BReady.chunked_bounded_stack_head mh st;
      BPres.chunked_mark_inner_loop_preservation_ready_step mh st cap fuel;
      if target = Seq.head st then
        BPres.chunked_mark_inner_loop_marks_head_ready
          mh st cap fuel target
      else begin
        let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
        seq_mem_tail_of_nonhead st target;
        BReady.chunked_mark_step_bounded_preserves_tail_member
          mh st cap target;
        assert (Seq.mem target st');
        BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
          mh st cap;
        BCountStep.chunked_mark_step_bounded_decreases_count mh st cap;
        BPres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
        assert (BDefs.chunked_count_non_black mh' <
                BDefs.chunked_count_non_black mh);
        nat_pred_ge_of_decrease
          fuel
          (BDefs.chunked_count_non_black mh)
          (BDefs.chunked_count_non_black mh');
        assert (fuel - 1 >= BDefs.chunked_count_non_black mh');
        chunked_mark_inner_loop_marks_stack_member_ready
          mh' st' cap (fuel - 1) target;
        BPres.chunked_mark_inner_loop_marks_tail_ready_from_step
          mh st cap fuel target
      end
    end
  end
