module GC.Spec.ChunkedMarkBounded.Metadata

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs
module MarkPres = GC.Spec.ChunkedMark.Preservation
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let rec chunked_push_children_bounded_preserves_wosize_of_object
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
    (cap: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         SweepDefs.chunked_wosize_of_object mh' target ==
         SweepDefs.chunked_wosize_of_object mh target))
      (decreases U64.v ws - U64.v i)
  =
  if U64.v i > U64.v ws then
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap
  else begin
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    let v = MarkDefs.chunked_get_field mh obj i in
    let mh1, st1 =
      if MarkDefs.chunked_is_pointer_field mh v then
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then
          let mh_gray = MarkDefs.chunked_make_gray mh child in
          if Seq.length st < cap then
            (mh_gray, Seq.cons child st)
          else
            (mh_gray, st)
        else
          (mh, st)
      else
        (mh, st)
    in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then begin
        BPres.chunked_push_children_bounded_preservation_ready_child
          mh obj i ws;
        assert (Seq.mem child (MH.major_objects mh));
        MarkPres.chunked_make_gray_preserves_wosize_of_object
          mh child target;
        MarkPres.chunked_make_gray_preserves_major_objects mh child;
        MarkPres.chunked_make_gray_preserves_well_formed mh child;
        assert (mh1 == MarkDefs.chunked_make_gray mh child);
        assert (MH.well_formed_major_heap mh1);
        assert (MH.major_objects mh1 == MH.major_objects mh);
        assert (Seq.mem target (MH.major_objects mh1))
      end
    end;
    if U64.v i < U64.v ws then begin
      BPres.chunked_push_children_bounded_preservation_ready_next
        mh obj i ws;
      assert (BPres.chunked_push_children_bounded_preservation_ready
        mh1 obj (U64.add i 1UL) ws);
      assert (U64.v (U64.add i 1UL) == U64.v i + 1);
      assert (U64.v ws - U64.v (U64.add i 1UL) <
              U64.v ws - U64.v i);
      chunked_push_children_bounded_preserves_wosize_of_object
        mh1 st1 obj (U64.add i 1UL) ws cap target;
      assert (SweepDefs.chunked_wosize_of_object mh1 target ==
              SweepDefs.chunked_wosize_of_object mh target)
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let chunked_mark_step_bounded_preserves_wosize_of_object
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         SweepDefs.chunked_wosize_of_object mh' target ==
         SweepDefs.chunked_wosize_of_object mh target))
  =
  if Seq.length st = 0 then
    BDefs.chunked_mark_step_bounded_empty mh st cap
  else begin
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    assert (Seq.length st > 0);
    BReady.chunked_bounded_stack_head mh st;
    let obj = Seq.head st in
    assert (Seq.mem obj (MH.major_objects mh));
    MarkPres.chunked_make_black_preserves_wosize_of_object mh obj target;
    MarkPres.chunked_make_black_preserves_major_objects mh obj;
    MarkPres.chunked_make_black_preserves_well_formed mh obj;
    let mh_black = MarkDefs.chunked_make_black mh obj in
    assert (MH.major_objects mh_black == MH.major_objects mh);
    assert (Seq.mem target (MH.major_objects mh_black));
    if MarkDefs.chunked_is_no_scan mh obj then begin
      assert (MarkDefs.chunked_is_no_scan mh (Seq.head st));
      BDefs.chunked_mark_step_bounded_no_scan mh st cap
    end else begin
      assert (~(MarkDefs.chunked_is_no_scan mh (Seq.head st)));
      BDefs.chunked_mark_step_bounded_scan mh st cap;
      BPres.chunked_mark_step_bounded_preservation_ready_scan mh st cap;
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_push_children_bounded_preserves_wosize_of_object
        mh_black (Seq.tail st) obj 1UL ws cap target;
      assert (SweepDefs.chunked_wosize_of_object mh_black target ==
              SweepDefs.chunked_wosize_of_object mh target)
    end
  end
#pop-options
