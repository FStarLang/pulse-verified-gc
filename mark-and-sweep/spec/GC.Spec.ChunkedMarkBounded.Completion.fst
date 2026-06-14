module GC.Spec.ChunkedMarkBounded.Completion

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BCount = GC.Spec.ChunkedMarkBounded.Count
module BCountStep = GC.Spec.ChunkedMarkBounded.CountStep
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady
module BStackStep = GC.Spec.ChunkedMarkBounded.StackStep

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

let nat_pred_ge_of_decrease
    (fuel count count': nat)
  : Lemma
      (requires
        fuel > 0 /\
        fuel >= count /\
        count' < count)
      (ensures fuel - 1 >= count')
  =
  ()

#push-options "--fuel 1 --ifuel 1"
let seq_mem_implies_nonempty (#a:eqtype)
    (s: Seq.seq a)
    (x: a)
  : Lemma
      (requires Seq.mem x s)
      (ensures Seq.length s > 0)
  =
  if Seq.length s = 0 then begin
    assert (s == Seq.empty);
    assert False
  end
#pop-options

#push-options "--z3rlimit 5"
let chunked_count_non_black_zero_no_gray
    (mh: MH.major_heap)
    (obj: obj_addr)
  : Lemma
      (requires
        BDefs.chunked_count_non_black mh == 0 /\
        Seq.mem obj (MH.major_objects mh))
      (ensures ~(BDefs.chunked_is_gray mh obj))
  =
  if BDefs.chunked_is_gray mh obj then begin
    BCount.chunked_is_gray_not_black mh obj;
    BReady.chunked_count_non_black_has_nonblack mh obj;
    assert False
  end
#pop-options

#push-options "--z3rlimit 5"
let chunked_rescan_heap_empty_no_gray
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (obj: obj_addr)
  : Lemma
      (requires
        Seq.length (MH.major_objects mh) <= cap /\
        Seq.length (BDefs.chunked_rescan_heap mh Seq.empty cap) = 0 /\
        Seq.mem obj (MH.major_objects mh))
      (ensures ~(BDefs.chunked_is_gray mh obj))
  =
  if BDefs.chunked_is_gray mh obj then begin
    BReady.chunked_rescan_heap_adds_gray_with_capacity mh cap obj;
    assert (Seq.mem obj (BDefs.chunked_rescan_heap mh Seq.empty cap));
    seq_mem_implies_nonempty
      (BDefs.chunked_rescan_heap mh Seq.empty cap) obj;
    assert False
  end
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_mark_inner_loop_count_nonincreasing
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        BReady.chunked_bounded_stack_props mh st)
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_inner_loop mh st cap fuel in
         BDefs.chunked_count_non_black mh' <=
         BDefs.chunked_count_non_black mh))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    BDefs.chunked_mark_inner_loop_base mh st cap fuel
  else begin
    BReady.chunked_bounded_stack_head mh st;
    BPres.chunked_mark_inner_loop_preservation_ready_step mh st cap fuel;
    BCountStep.chunked_mark_step_bounded_decreases_count mh st cap;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    BPres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    chunked_mark_inner_loop_count_nonincreasing
      mh' st' cap (fuel - 1);
    BDefs.chunked_mark_inner_loop_step mh st cap fuel
  end
#pop-options

#push-options "--z3rlimit 10"
let chunked_mark_inner_loop_count_decreases
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        BReady.chunked_bounded_stack_props mh st)
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_inner_loop mh st cap fuel in
         BDefs.chunked_count_non_black mh' <
         BDefs.chunked_count_non_black mh))
  =
  BReady.chunked_bounded_stack_head mh st;
  BPres.chunked_mark_inner_loop_preservation_ready_step mh st cap fuel;
  BCountStep.chunked_mark_step_bounded_decreases_count mh st cap;
  BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
    mh st cap;
  BPres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
  let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
  chunked_mark_inner_loop_count_nonincreasing
    mh' st' cap (fuel - 1);
  BDefs.chunked_mark_inner_loop_step mh st cap fuel
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_mark_bounded_completes
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        fuel >= BDefs.chunked_count_non_black mh)
      (ensures
        forall (obj: obj_addr).
          Seq.mem obj
            (MH.major_objects (BDefs.chunked_mark_bounded mh cap fuel)) ==>
          ~(BDefs.chunked_is_gray
            (BDefs.chunked_mark_bounded mh cap fuel) obj))
      (decreases fuel)
  =
  if fuel = 0 then begin
    BDefs.chunked_mark_bounded_base mh cap;
    let no_gray (obj: obj_addr)
      : Lemma
          (requires Seq.mem obj (MH.major_objects mh))
          (ensures ~(BDefs.chunked_is_gray mh obj))
      =
      chunked_count_non_black_zero_no_gray mh obj
    in
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires no_gray)
  end else begin
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then begin
      let no_gray (obj: obj_addr)
        : Lemma
            (requires Seq.mem obj (MH.major_objects mh))
            (ensures ~(BDefs.chunked_is_gray mh obj))
        =
        chunked_rescan_heap_empty_no_gray mh cap obj
      in
      FStar.Classical.forall_intro
        (FStar.Classical.move_requires no_gray)
    end else begin
      BReady.chunked_rescan_heap_bounded_stack_props mh cap;
      BReady.chunked_bounded_stack_head mh st;
      BCount.chunked_is_gray_not_black mh (Seq.head st);
      BReady.chunked_count_non_black_has_nonblack mh (Seq.head st);
      assert (BDefs.chunked_count_non_black mh > 0);
      let inner_fuel = BDefs.chunked_count_non_black mh in
      BPres.chunked_mark_bounded_preservation_ready_step mh cap fuel;
      chunked_mark_inner_loop_count_decreases mh st cap inner_fuel;
      BPres.chunked_mark_inner_loop_preserves_well_formed mh st cap inner_fuel;
      BPres.chunked_mark_inner_loop_preserves_major_objects mh st cap inner_fuel;
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      nat_pred_ge_of_decrease
        fuel
        (BDefs.chunked_count_non_black mh)
        (BDefs.chunked_count_non_black mh');
      assert (fuel - 1 >= BDefs.chunked_count_non_black mh');
      assert (Seq.length (MH.major_objects mh') <= cap);
      chunked_mark_bounded_completes mh' cap (fuel - 1)
    end
  end
#pop-options
