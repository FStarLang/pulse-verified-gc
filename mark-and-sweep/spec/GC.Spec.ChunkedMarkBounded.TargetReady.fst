module GC.Spec.ChunkedMarkBounded.TargetReady

module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module MarkDefs = GC.Spec.ChunkedMark.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module SeqMem = GC.Spec.SeqMemLemmas

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let rec chunked_count_non_black_in_has_nonblack
    (mh: MH.major_heap)
    (target: obj_addr)
    (objs: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.mem target objs /\
        ~ (SweepDefs.chunked_is_black mh target))
      (ensures
        BDefs.chunked_count_non_black_in mh objs > 0)
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then
    ()
  else begin
    BDefs.chunked_count_non_black_in_step mh objs;
    if Seq.head objs = target then
      ()
    else
      chunked_count_non_black_in_has_nonblack mh target (Seq.tail objs)
  end

let chunked_count_non_black_has_nonblack
    (mh: MH.major_heap)
    (target: obj_addr)
  : Lemma
      (requires
        Seq.mem target (MH.major_objects mh) /\
        ~ (SweepDefs.chunked_is_black mh target))
      (ensures
        BDefs.chunked_count_non_black mh > 0)
  =
  BDefs.chunked_count_non_black_equation mh;
  chunked_count_non_black_in_has_nonblack
    mh target (MH.major_objects mh)

let rec chunked_count_non_black_in_bound
    (mh: MH.major_heap)
    (objs: Seq.seq obj_addr)
  : Lemma
      (ensures
        BDefs.chunked_count_non_black_in mh objs <= Seq.length objs)
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then
    BDefs.chunked_count_non_black_in_empty mh objs
  else begin
    BDefs.chunked_count_non_black_in_step mh objs;
    chunked_count_non_black_in_bound mh (Seq.tail objs)
  end

let chunked_count_non_black_bound
    (mh: MH.major_heap)
  : Lemma
      (ensures
        BDefs.chunked_count_non_black mh <= Seq.length (MH.major_objects mh))
  =
  BDefs.chunked_count_non_black_equation mh;
  chunked_count_non_black_in_bound mh (MH.major_objects mh)

let rec chunked_push_children_bounded_preserves_stack_member
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
      (decreases (FStar.UInt64.v ws - FStar.UInt64.v i))
  =
  if FStar.UInt64.v i > FStar.UInt64.v ws then
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap
  else begin
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    let v = MarkDefs.chunked_get_field mh obj i in
    let (mh', st') =
      if MarkDefs.chunked_is_pointer_field mh v then
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then
          let mh' = MarkDefs.chunked_make_gray mh child in
          if Seq.length st < cap then begin
            SeqMem.seq_mem_cons_tail child target st;
            (mh', Seq.cons child st)
          end else
            (mh', st)
        else
          (mh, st)
      else
        (mh, st) in
    if FStar.UInt64.v i < FStar.UInt64.v ws then
      chunked_push_children_bounded_preserves_stack_member
        mh' st' obj (FStar.UInt64.add i 1UL) ws cap target
  end

let chunked_mark_step_bounded_preserves_tail_member
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
  =
  if MarkDefs.chunked_is_no_scan mh (Seq.head st) then
    BDefs.chunked_mark_step_bounded_no_scan mh st cap
  else begin
    BDefs.chunked_mark_step_bounded_scan mh st cap;
    let obj = Seq.head st in
    let st_tail = Seq.tail st in
    let mh' = MarkDefs.chunked_make_black mh obj in
    let ws = SweepDefs.chunked_wosize_of_object mh obj in
    chunked_push_children_bounded_preserves_stack_member
      mh' st_tail obj 1UL ws cap target
  end

let rec chunked_rescan_objects_preserves_stack_member
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
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then
    BDefs.chunked_rescan_objects_empty mh objs st cap
  else begin
    BDefs.chunked_rescan_objects_step mh objs st cap;
    let obj = Seq.head objs in
    let st' =
      if BDefs.chunked_is_gray mh obj && not (Seq.mem obj st) &&
         Seq.length st < cap then begin
        SeqMem.seq_mem_cons_tail obj target st;
        Seq.cons obj st
      end else
        st in
    chunked_rescan_objects_preserves_stack_member
      mh (Seq.tail objs) st' cap target
  end

let rec chunked_rescan_objects_adds_gray_with_capacity
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
      (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then
    ()
  else begin
    BDefs.chunked_rescan_objects_step mh objs st cap;
    let obj = Seq.head objs in
    let st' =
      if BDefs.chunked_is_gray mh obj && not (Seq.mem obj st) &&
         Seq.length st < cap then
        Seq.cons obj st
      else
        st in
    if obj = target then begin
      if Seq.mem target st then
        chunked_rescan_objects_preserves_stack_member
          mh (Seq.tail objs) st' cap target
      else begin
        assert (Seq.length st < cap);
        assert (BDefs.chunked_is_gray mh obj);
        assert (Seq.mem target st');
        chunked_rescan_objects_preserves_stack_member
          mh (Seq.tail objs) st' cap target
      end
    end else begin
      assert (Seq.mem target (Seq.tail objs));
      assert (Seq.length st' + Seq.length (Seq.tail objs) <= cap);
      chunked_rescan_objects_adds_gray_with_capacity
        mh (Seq.tail objs) st' cap target
    end
  end

let chunked_rescan_heap_adds_gray_with_capacity
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
  =
  BDefs.chunked_rescan_heap_equation mh Seq.empty cap;
  chunked_rescan_objects_adds_gray_with_capacity
    mh (MH.major_objects mh) Seq.empty cap target

let chunked_mark_bounded_marks_rescan_head_ready
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
    (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        (let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
         Seq.length st > 0 /\
         target == Seq.head st /\
         Seq.mem target (MH.major_objects mh)))
      (ensures
        BPres.chunked_mark_bounded_marks_target_ready mh cap fuel target)
  =
  if SweepDefs.chunked_is_black mh target then
    BPres.chunked_mark_bounded_marks_black_ready mh cap fuel target
  else begin
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    chunked_count_non_black_has_nonblack mh target;
    BPres.chunked_mark_bounded_marks_rescan_head_ready_from_inner_fuel
      mh cap fuel target
  end
