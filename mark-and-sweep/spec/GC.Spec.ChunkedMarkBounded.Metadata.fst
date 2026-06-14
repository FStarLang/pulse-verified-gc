module GC.Spec.ChunkedMarkBounded.Metadata

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs
module MarkPres = GC.Spec.ChunkedMark.Preservation
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module RangePres = GC.Spec.ChunkedSweepCoalesce.RangePreservation
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady
module BStackStep = GC.Spec.ChunkedMarkBounded.StackStep

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
let rec chunked_push_children_bounded_preserves_get_field
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
    (cap: nat)
    (target: obj_addr)
    (j: U64.t{U64.v j >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v j <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
      (ensures
        (let (mh', _) =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         MarkDefs.chunked_get_field mh' target j ==
         MarkDefs.chunked_get_field mh target j))
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
        MarkPres.chunked_make_gray_preserves_get_field
          mh child target j;
        MarkPres.chunked_make_gray_preserves_wosize_of_object
          mh child target;
        MarkPres.chunked_make_gray_preserves_major_objects mh child;
        MarkPres.chunked_make_gray_preserves_well_formed mh child;
        assert (mh1 == MarkDefs.chunked_make_gray mh child);
        assert (MH.well_formed_major_heap mh1);
        assert (MH.major_objects mh1 == MH.major_objects mh);
        assert (Seq.mem target (MH.major_objects mh1));
        assert (U64.v j <=
          U64.v (SweepDefs.chunked_wosize_of_object mh1 target))
      end
    end;
    if U64.v i < U64.v ws then begin
      BPres.chunked_push_children_bounded_preservation_ready_next
        mh obj i ws;
      assert (BPres.chunked_push_children_bounded_preservation_ready
        mh1 obj (U64.add i 1UL) ws);
      assert (U64.v j <=
        U64.v (SweepDefs.chunked_wosize_of_object mh1 target));
      assert (U64.v (U64.add i 1UL) == U64.v i + 1);
      assert (U64.v ws - U64.v (U64.add i 1UL) <
              U64.v ws - U64.v i);
      chunked_push_children_bounded_preserves_get_field
        mh1 st1 obj (U64.add i 1UL) ws cap target j;
      assert (MarkDefs.chunked_get_field mh1 target j ==
              MarkDefs.chunked_get_field mh target j)
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let rec chunked_push_children_bounded_preserves_no_scan_status
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
         MarkDefs.chunked_is_no_scan mh' target ==
         MarkDefs.chunked_is_no_scan mh target))
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
        MarkPres.chunked_make_gray_preserves_no_scan_status
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
      chunked_push_children_bounded_preserves_no_scan_status
        mh1 st1 obj (U64.add i 1UL) ws cap target;
      assert (MarkDefs.chunked_is_no_scan mh1 target ==
              MarkDefs.chunked_is_no_scan mh target)
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let rec chunked_push_children_bounded_preserves_ranges
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
    (cap: nat)
  : Lemma
      (ensures
        (let (mh', _) =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         RangePres.same_chunk_ranges mh mh'))
      (decreases U64.v ws - U64.v i)
  =
  if U64.v i > U64.v ws then begin
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap;
    RangePres.same_chunk_ranges_refl mh
  end else begin
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
        MarkPres.chunked_make_gray_preserves_ranges mh child;
        assert (mh1 == MarkDefs.chunked_make_gray mh child)
      end else begin
        assert (mh1 == mh);
        RangePres.same_chunk_ranges_refl mh
      end
    end else begin
      assert (mh1 == mh);
      RangePres.same_chunk_ranges_refl mh
    end;
    if U64.v i < U64.v ws then begin
      assert (U64.v (U64.add i 1UL) == U64.v i + 1);
      assert (U64.v ws - U64.v (U64.add i 1UL) <
              U64.v ws - U64.v i);
      chunked_push_children_bounded_preserves_ranges
        mh1 st1 obj (U64.add i 1UL) ws cap;
      RangePres.same_chunk_ranges_trans
        mh mh1
        (fst (BDefs.chunked_push_children_bounded
          mh1 st1 obj (U64.add i 1UL) ws cap))
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

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let chunked_mark_step_bounded_preserves_get_field
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (target: obj_addr)
    (j: U64.t{U64.v j >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v j <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         MarkDefs.chunked_get_field mh' target j ==
         MarkDefs.chunked_get_field mh target j))
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
    MarkPres.chunked_make_black_preserves_get_field
      mh obj target j;
    MarkPres.chunked_make_black_preserves_wosize_of_object
      mh obj target;
    MarkPres.chunked_make_black_preserves_major_objects mh obj;
    MarkPres.chunked_make_black_preserves_well_formed mh obj;
    let mh_black = MarkDefs.chunked_make_black mh obj in
    assert (MH.major_objects mh_black == MH.major_objects mh);
    assert (Seq.mem target (MH.major_objects mh_black));
    assert (U64.v j <=
      U64.v (SweepDefs.chunked_wosize_of_object mh_black target));
    if MarkDefs.chunked_is_no_scan mh obj then begin
      assert (MarkDefs.chunked_is_no_scan mh (Seq.head st));
      BDefs.chunked_mark_step_bounded_no_scan mh st cap
    end else begin
      assert (~(MarkDefs.chunked_is_no_scan mh (Seq.head st)));
      BDefs.chunked_mark_step_bounded_scan mh st cap;
      BPres.chunked_mark_step_bounded_preservation_ready_scan mh st cap;
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_push_children_bounded_preserves_get_field
        mh_black (Seq.tail st) obj 1UL ws cap target j;
      assert (MarkDefs.chunked_get_field mh_black target j ==
              MarkDefs.chunked_get_field mh target j)
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let chunked_mark_step_bounded_preserves_no_scan_status
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
         MarkDefs.chunked_is_no_scan mh' target ==
         MarkDefs.chunked_is_no_scan mh target))
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
    MarkPres.chunked_make_black_preserves_no_scan_status mh obj target;
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
      chunked_push_children_bounded_preserves_no_scan_status
        mh_black (Seq.tail st) obj 1UL ws cap target;
      assert (MarkDefs.chunked_is_no_scan mh_black target ==
              MarkDefs.chunked_is_no_scan mh target)
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let chunked_mark_step_bounded_preserves_ranges
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         RangePres.same_chunk_ranges mh mh'))
  =
  if Seq.length st = 0 then begin
    BDefs.chunked_mark_step_bounded_empty mh st cap;
    RangePres.same_chunk_ranges_refl mh
  end else begin
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    assert (Seq.length st > 0);
    let obj = Seq.head st in
    MarkPres.chunked_make_black_preserves_ranges mh obj;
    let mh_black = MarkDefs.chunked_make_black mh obj in
    if MarkDefs.chunked_is_no_scan mh obj then
      BDefs.chunked_mark_step_bounded_no_scan mh st cap
    else begin
      BDefs.chunked_mark_step_bounded_scan mh st cap;
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_push_children_bounded_preserves_ranges
        mh_black (Seq.tail st) obj 1UL ws cap;
      RangePres.same_chunk_ranges_trans
        mh mh_black
        (fst (BDefs.chunked_push_children_bounded
          mh_black (Seq.tail st) obj 1UL ws cap))
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let rec chunked_mark_inner_loop_preserves_wosize_of_object
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        BReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap fuel in
         SweepDefs.chunked_wosize_of_object mh' target ==
         SweepDefs.chunked_wosize_of_object mh target))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    BDefs.chunked_mark_inner_loop_base mh st cap fuel
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    assert (fuel > 0);
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    assert (Seq.length st > 0);
    BDefs.chunked_mark_inner_loop_step mh st cap fuel;
    BPres.chunked_mark_inner_loop_preservation_ready_step mh st cap fuel;
    let mh1, st1 = BDefs.chunked_mark_step_bounded mh st cap in
    chunked_mark_step_bounded_preserves_wosize_of_object
      mh st cap target;
    BPres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    BPres.chunked_mark_step_bounded_preserves_major_objects mh st cap;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    assert (MH.well_formed_major_heap mh1);
    assert (MH.major_objects mh1 == MH.major_objects mh);
    assert (Seq.mem target (MH.major_objects mh1));
    assert (BReady.chunked_bounded_stack_props mh1 st1);
    assert (BPres.chunked_mark_inner_loop_preservation_ready
      mh1 st1 cap (fuel - 1));
    chunked_mark_inner_loop_preserves_wosize_of_object
      mh1 st1 cap (fuel - 1) target;
    assert (SweepDefs.chunked_wosize_of_object mh1 target ==
            SweepDefs.chunked_wosize_of_object mh target)
  end

let rec chunked_mark_inner_loop_preserves_get_field
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
    (target: obj_addr)
    (j: U64.t{U64.v j >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        BReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v j <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap fuel in
         MarkDefs.chunked_get_field mh' target j ==
         MarkDefs.chunked_get_field mh target j))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    BDefs.chunked_mark_inner_loop_base mh st cap fuel
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    assert (fuel > 0);
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    assert (Seq.length st > 0);
    BDefs.chunked_mark_inner_loop_step mh st cap fuel;
    BPres.chunked_mark_inner_loop_preservation_ready_step mh st cap fuel;
    let mh1, st1 = BDefs.chunked_mark_step_bounded mh st cap in
    chunked_mark_step_bounded_preserves_get_field
      mh st cap target j;
    chunked_mark_step_bounded_preserves_wosize_of_object
      mh st cap target;
    BPres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    BPres.chunked_mark_step_bounded_preserves_major_objects mh st cap;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    assert (MH.well_formed_major_heap mh1);
    assert (MH.major_objects mh1 == MH.major_objects mh);
    assert (Seq.mem target (MH.major_objects mh1));
    assert (BReady.chunked_bounded_stack_props mh1 st1);
    assert (BPres.chunked_mark_inner_loop_preservation_ready
      mh1 st1 cap (fuel - 1));
    assert (U64.v j <=
      U64.v (SweepDefs.chunked_wosize_of_object mh1 target));
    chunked_mark_inner_loop_preserves_get_field
      mh1 st1 cap (fuel - 1) target j;
    assert (MarkDefs.chunked_get_field mh1 target j ==
            MarkDefs.chunked_get_field mh target j)
  end

let rec chunked_mark_inner_loop_preserves_no_scan_status
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        BReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap fuel in
         MarkDefs.chunked_is_no_scan mh' target ==
         MarkDefs.chunked_is_no_scan mh target))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    BDefs.chunked_mark_inner_loop_base mh st cap fuel
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    assert (fuel > 0);
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    assert (Seq.length st > 0);
    BDefs.chunked_mark_inner_loop_step mh st cap fuel;
    BPres.chunked_mark_inner_loop_preservation_ready_step mh st cap fuel;
    let mh1, st1 = BDefs.chunked_mark_step_bounded mh st cap in
    chunked_mark_step_bounded_preserves_no_scan_status
      mh st cap target;
    BPres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    BPres.chunked_mark_step_bounded_preserves_major_objects mh st cap;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    assert (MH.well_formed_major_heap mh1);
    assert (MH.major_objects mh1 == MH.major_objects mh);
    assert (Seq.mem target (MH.major_objects mh1));
    assert (BReady.chunked_bounded_stack_props mh1 st1);
    assert (BPres.chunked_mark_inner_loop_preservation_ready
      mh1 st1 cap (fuel - 1));
    chunked_mark_inner_loop_preserves_no_scan_status
      mh1 st1 cap (fuel - 1) target;
    assert (MarkDefs.chunked_is_no_scan mh1 target ==
            MarkDefs.chunked_is_no_scan mh target)
  end

let rec chunked_mark_inner_loop_preserves_ranges
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (ensures
        (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap fuel in
         RangePres.same_chunk_ranges mh mh'))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then begin
    BDefs.chunked_mark_inner_loop_base mh st cap fuel;
    RangePres.same_chunk_ranges_refl mh
  end else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    assert (fuel > 0);
    BDefs.chunked_mark_inner_loop_step mh st cap fuel;
    let mh1, st1 = BDefs.chunked_mark_step_bounded mh st cap in
    chunked_mark_step_bounded_preserves_ranges mh st cap;
    chunked_mark_inner_loop_preserves_ranges mh1 st1 cap (fuel - 1);
    RangePres.same_chunk_ranges_trans
      mh mh1
      (fst (BDefs.chunked_mark_inner_loop mh1 st1 cap (fuel - 1)))
  end

let rec chunked_mark_bounded_preserves_wosize_of_object
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        SweepDefs.chunked_wosize_of_object
          (BDefs.chunked_mark_bounded mh cap fuel) target ==
        SweepDefs.chunked_wosize_of_object mh target)
      (decreases fuel)
  =
  if fuel = 0 then
    BDefs.chunked_mark_bounded_base mh cap
  else begin
    assert (fuel > 0);
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      ()
    else begin
      assert (Seq.length st <> 0);
      nat_nonzero_pos (Seq.length st);
      assert (Seq.length st > 0);
      BReady.chunked_rescan_heap_bounded_stack_props mh cap;
      BPres.chunked_mark_bounded_preservation_ready_step mh cap fuel;
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let mh1, st1 = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      chunked_mark_inner_loop_preserves_wosize_of_object
        mh st cap inner_fuel target;
      BPres.chunked_mark_inner_loop_preserves_well_formed
        mh st cap inner_fuel;
      BPres.chunked_mark_inner_loop_preserves_major_objects
        mh st cap inner_fuel;
      assert (MH.well_formed_major_heap mh1);
      assert (MH.major_objects mh1 == MH.major_objects mh);
      assert (Seq.mem target (MH.major_objects mh1));
      assert (BPres.chunked_mark_bounded_preservation_ready
        mh1 cap (fuel - 1));
      chunked_mark_bounded_preserves_wosize_of_object
        mh1 cap (fuel - 1) target;
      assert (SweepDefs.chunked_wosize_of_object mh1 target ==
              SweepDefs.chunked_wosize_of_object mh target)
    end
  end

let rec chunked_mark_bounded_preserves_get_field
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
    (target: obj_addr)
    (j: U64.t{U64.v j >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v j <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
      (ensures
        MarkDefs.chunked_get_field
          (BDefs.chunked_mark_bounded mh cap fuel) target j ==
        MarkDefs.chunked_get_field mh target j)
      (decreases fuel)
  =
  if fuel = 0 then
    BDefs.chunked_mark_bounded_base mh cap
  else begin
    assert (fuel > 0);
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      ()
    else begin
      assert (Seq.length st <> 0);
      nat_nonzero_pos (Seq.length st);
      assert (Seq.length st > 0);
      BReady.chunked_rescan_heap_bounded_stack_props mh cap;
      BPres.chunked_mark_bounded_preservation_ready_step mh cap fuel;
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let mh1, st1 = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      chunked_mark_inner_loop_preserves_get_field
        mh st cap inner_fuel target j;
      chunked_mark_inner_loop_preserves_wosize_of_object
        mh st cap inner_fuel target;
      BPres.chunked_mark_inner_loop_preserves_well_formed
        mh st cap inner_fuel;
      BPres.chunked_mark_inner_loop_preserves_major_objects
        mh st cap inner_fuel;
      assert (MH.well_formed_major_heap mh1);
      assert (MH.major_objects mh1 == MH.major_objects mh);
      assert (Seq.mem target (MH.major_objects mh1));
      assert (BPres.chunked_mark_bounded_preservation_ready
        mh1 cap (fuel - 1));
      assert (U64.v j <=
        U64.v (SweepDefs.chunked_wosize_of_object mh1 target));
      chunked_mark_bounded_preserves_get_field
        mh1 cap (fuel - 1) target j;
      assert (MarkDefs.chunked_get_field mh1 target j ==
              MarkDefs.chunked_get_field mh target j)
    end
  end

let rec chunked_mark_bounded_preserves_no_scan_status
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        MarkDefs.chunked_is_no_scan
          (BDefs.chunked_mark_bounded mh cap fuel) target ==
        MarkDefs.chunked_is_no_scan mh target)
      (decreases fuel)
  =
  if fuel = 0 then
    BDefs.chunked_mark_bounded_base mh cap
  else begin
    assert (fuel > 0);
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      ()
    else begin
      assert (Seq.length st <> 0);
      nat_nonzero_pos (Seq.length st);
      assert (Seq.length st > 0);
      BReady.chunked_rescan_heap_bounded_stack_props mh cap;
      BPres.chunked_mark_bounded_preservation_ready_step mh cap fuel;
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let mh1, st1 = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      chunked_mark_inner_loop_preserves_no_scan_status
        mh st cap inner_fuel target;
      BPres.chunked_mark_inner_loop_preserves_well_formed
        mh st cap inner_fuel;
      BPres.chunked_mark_inner_loop_preserves_major_objects
        mh st cap inner_fuel;
      assert (MH.well_formed_major_heap mh1);
      assert (MH.major_objects mh1 == MH.major_objects mh);
      assert (Seq.mem target (MH.major_objects mh1));
      assert (BPres.chunked_mark_bounded_preservation_ready
        mh1 cap (fuel - 1));
      chunked_mark_bounded_preserves_no_scan_status
        mh1 cap (fuel - 1) target;
      assert (MarkDefs.chunked_is_no_scan mh1 target ==
              MarkDefs.chunked_is_no_scan mh target)
    end
  end

let rec chunked_mark_bounded_preserves_ranges
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (ensures
        RangePres.same_chunk_ranges mh
          (BDefs.chunked_mark_bounded mh cap fuel))
      (decreases fuel)
  =
  if fuel = 0 then begin
    BDefs.chunked_mark_bounded_base mh cap;
    RangePres.same_chunk_ranges_refl mh
  end else begin
    assert (fuel > 0);
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      RangePres.same_chunk_ranges_refl mh
    else begin
      assert (Seq.length st <> 0);
      nat_nonzero_pos (Seq.length st);
      assert (Seq.length st > 0);
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let mh1, st1 = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      chunked_mark_inner_loop_preserves_ranges mh st cap inner_fuel;
      chunked_mark_bounded_preserves_ranges mh1 cap (fuel - 1);
      RangePres.same_chunk_ranges_trans
        mh mh1 (BDefs.chunked_mark_bounded mh1 cap (fuel - 1))
    end
  end
#pop-options
