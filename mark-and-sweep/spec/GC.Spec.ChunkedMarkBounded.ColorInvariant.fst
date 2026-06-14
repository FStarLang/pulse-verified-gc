module GC.Spec.ChunkedMarkBounded.ColorInvariant

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs
module MarkPres = GC.Spec.ChunkedMark.Preservation
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module RangePres = GC.Spec.ChunkedSweepCoalesce.RangePreservation
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BMetadata = GC.Spec.ChunkedMarkBounded.Metadata
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady
module BStackStep = GC.Spec.ChunkedMarkBounded.StackStep
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph
module MarkLive = GC.Spec.ChunkedMajorGC.MarkLiveness

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

#push-options "--z3rlimit 10"
let rec chunked_push_children_bounded_no_new_blue
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
        ~(SweepDefs.chunked_is_blue mh target))
      (ensures
        (let (mh', _) =
           BDefs.chunked_push_children_bounded mh st obj i ws cap in
         ~(SweepDefs.chunked_is_blue mh' target)))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap
  else begin
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then begin
        BPres.chunked_push_children_bounded_preservation_ready_child
          mh obj i ws;
        assert (Seq.mem child (MH.major_objects mh));
        let mh_gray = MarkDefs.chunked_make_gray mh child in
        let st' =
          if Seq.length st < cap then Seq.cons child st else st in
        if target = child then
          MarkPres.chunked_make_gray_not_blue mh child
        else begin
          MarkPres.chunked_make_gray_preserves_other_blue_status
            mh child target;
          assert (~(SweepDefs.chunked_is_blue mh_gray target))
        end;
        if U64.v i < U64.v ws then begin
          MarkPres.chunked_make_gray_preserves_well_formed mh child;
          MarkPres.chunked_make_gray_preserves_major_objects mh child;
          BPres.chunked_push_children_bounded_preservation_ready_next
            mh obj i ws;
          chunked_push_children_bounded_no_new_blue
            mh_gray st' obj (U64.add i 1UL) ws cap target
        end
      end else if U64.v i < U64.v ws then begin
        BPres.chunked_push_children_bounded_preservation_ready_next
          mh obj i ws;
        chunked_push_children_bounded_no_new_blue
          mh st obj (U64.add i 1UL) ws cap target
      end
    end else if U64.v i < U64.v ws then begin
      BPres.chunked_push_children_bounded_preservation_ready_next
        mh obj i ws;
      chunked_push_children_bounded_no_new_blue
        mh st obj (U64.add i 1UL) ws cap target
    end
  end
#pop-options

#push-options "--z3rlimit 10"
let chunked_mark_step_bounded_no_new_blue
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        ~(SweepDefs.chunked_is_blue mh target))
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_step_bounded mh st cap in
         ~(SweepDefs.chunked_is_blue mh' target)))
  =
  if Seq.length st = 0 then
    BDefs.chunked_mark_step_bounded_empty mh st cap
  else begin
    BReady.chunked_bounded_stack_head mh st;
    let obj = Seq.head st in
    let mh_black = MarkDefs.chunked_make_black mh obj in
    let st_tail = Seq.tail st in
    if target = obj then
      MarkPres.chunked_make_black_not_blue mh obj
    else begin
      MarkPres.chunked_make_black_preserves_other_blue_status
        mh obj target;
      assert (~(SweepDefs.chunked_is_blue mh_black target))
    end;
    if MarkDefs.chunked_is_no_scan mh obj then
      BDefs.chunked_mark_step_bounded_no_scan mh st cap
    else begin
      BDefs.chunked_mark_step_bounded_scan mh st cap;
      BPres.chunked_mark_step_bounded_preservation_ready_scan mh st cap;
      MarkPres.chunked_make_black_preserves_well_formed mh obj;
      MarkPres.chunked_make_black_preserves_major_objects mh obj;
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_push_children_bounded_no_new_blue
        mh_black st_tail obj 1UL ws cap target
    end
  end
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_mark_inner_loop_no_new_blue
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
        ~(SweepDefs.chunked_is_blue mh target))
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_inner_loop mh st cap fuel in
         ~(SweepDefs.chunked_is_blue mh' target)))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    BDefs.chunked_mark_inner_loop_base mh st cap fuel
  else begin
    BPres.chunked_mark_inner_loop_preservation_ready_step mh st cap fuel;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    BPres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    BPres.chunked_mark_step_bounded_preserves_major_objects mh st cap;
    chunked_mark_step_bounded_no_new_blue mh st cap target;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    assert (~(SweepDefs.chunked_is_blue mh' target));
    chunked_mark_inner_loop_no_new_blue
      mh' st' cap (fuel - 1) target;
    BDefs.chunked_mark_inner_loop_step mh st cap fuel
  end
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_mark_bounded_no_new_blue
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        ~(SweepDefs.chunked_is_blue mh target))
      (ensures
        ~(SweepDefs.chunked_is_blue
          (BDefs.chunked_mark_bounded mh cap fuel) target))
      (decreases fuel)
  =
  if fuel = 0 then
    BDefs.chunked_mark_bounded_base mh cap
  else begin
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      ()
    else begin
      BReady.chunked_rescan_heap_bounded_stack_props mh cap;
      BPres.chunked_mark_bounded_preservation_ready_step mh cap fuel;
      let inner_fuel = BDefs.chunked_count_non_black mh in
      chunked_mark_inner_loop_no_new_blue
        mh st cap inner_fuel target;
      BPres.chunked_mark_inner_loop_preserves_well_formed
        mh st cap inner_fuel;
      BPres.chunked_mark_inner_loop_preserves_major_objects
        mh st cap inner_fuel;
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      assert (~(SweepDefs.chunked_is_blue mh' target));
      chunked_mark_bounded_no_new_blue mh' cap (fuel - 1) target
    end
  end
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_push_children_bounded_no_new_white
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
        ~(SweepDefs.chunked_is_white mh target))
      (ensures
        (let (mh', _) =
           BDefs.chunked_push_children_bounded mh st obj i ws cap in
         ~(SweepDefs.chunked_is_white mh' target)))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap
  else begin
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then begin
        BPres.chunked_push_children_bounded_preservation_ready_child
          mh obj i ws;
        assert (Seq.mem child (MH.major_objects mh));
        if target = child then
          assert False
        else begin
          MarkPres.chunked_make_gray_preserves_other_white_status
            mh child target;
          let mh_gray = MarkDefs.chunked_make_gray mh child in
          assert (~(SweepDefs.chunked_is_white mh_gray target));
          let st' =
            if Seq.length st < cap then Seq.cons child st else st in
          if U64.v i < U64.v ws then begin
            MarkPres.chunked_make_gray_preserves_well_formed mh child;
            MarkPres.chunked_make_gray_preserves_major_objects mh child;
            BPres.chunked_push_children_bounded_preservation_ready_next
              mh obj i ws;
            chunked_push_children_bounded_no_new_white
              mh_gray st' obj (U64.add i 1UL) ws cap target
          end
        end
      end else if U64.v i < U64.v ws then begin
        BPres.chunked_push_children_bounded_preservation_ready_next
          mh obj i ws;
        chunked_push_children_bounded_no_new_white
          mh st obj (U64.add i 1UL) ws cap target
      end
    end else if U64.v i < U64.v ws then begin
      BPres.chunked_push_children_bounded_preservation_ready_next
        mh obj i ws;
      chunked_push_children_bounded_no_new_white
        mh st obj (U64.add i 1UL) ws cap target
    end
  end
#pop-options

#push-options "--z3rlimit 10"
let chunked_mark_step_bounded_no_new_white
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        ~(SweepDefs.chunked_is_white mh target))
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_step_bounded mh st cap in
         ~(SweepDefs.chunked_is_white mh' target)))
  =
  if Seq.length st = 0 then
    BDefs.chunked_mark_step_bounded_empty mh st cap
  else begin
    BReady.chunked_bounded_stack_head mh st;
    let obj = Seq.head st in
    let mh_black = MarkDefs.chunked_make_black mh obj in
    let st_tail = Seq.tail st in
    if target = obj then
      MarkPres.chunked_make_black_not_white mh obj
    else begin
      MarkPres.chunked_make_black_preserves_other_white_status
        mh obj target;
      assert (~(SweepDefs.chunked_is_white mh_black target))
    end;
    if MarkDefs.chunked_is_no_scan mh obj then
      BDefs.chunked_mark_step_bounded_no_scan mh st cap
    else begin
      BDefs.chunked_mark_step_bounded_scan mh st cap;
      BPres.chunked_mark_step_bounded_preservation_ready_scan mh st cap;
      MarkPres.chunked_make_black_preserves_well_formed mh obj;
      MarkPres.chunked_make_black_preserves_major_objects mh obj;
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_push_children_bounded_no_new_white
        mh_black st_tail obj 1UL ws cap target
    end
  end
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_mark_inner_loop_no_new_white
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
        ~(SweepDefs.chunked_is_white mh target))
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_inner_loop mh st cap fuel in
         ~(SweepDefs.chunked_is_white mh' target)))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    BDefs.chunked_mark_inner_loop_base mh st cap fuel
  else begin
    BPres.chunked_mark_inner_loop_preservation_ready_step mh st cap fuel;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    BPres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    BPres.chunked_mark_step_bounded_preserves_major_objects mh st cap;
    chunked_mark_step_bounded_no_new_white mh st cap target;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    assert (~(SweepDefs.chunked_is_white mh' target));
    chunked_mark_inner_loop_no_new_white
      mh' st' cap (fuel - 1) target;
    BDefs.chunked_mark_inner_loop_step mh st cap fuel
  end
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_mark_bounded_no_new_white
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        ~(SweepDefs.chunked_is_white mh target))
      (ensures
        ~(SweepDefs.chunked_is_white
          (BDefs.chunked_mark_bounded mh cap fuel) target))
      (decreases fuel)
  =
  if fuel = 0 then
    BDefs.chunked_mark_bounded_base mh cap
  else begin
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      ()
    else begin
      BReady.chunked_rescan_heap_bounded_stack_props mh cap;
      BPres.chunked_mark_bounded_preservation_ready_step mh cap fuel;
      let inner_fuel = BDefs.chunked_count_non_black mh in
      chunked_mark_inner_loop_no_new_white
        mh st cap inner_fuel target;
      BPres.chunked_mark_inner_loop_preserves_well_formed
        mh st cap inner_fuel;
      BPres.chunked_mark_inner_loop_preserves_major_objects
        mh st cap inner_fuel;
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      assert (~(SweepDefs.chunked_is_white mh' target));
      chunked_mark_bounded_no_new_white mh' cap (fuel - 1) target
    end
  end
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_push_children_bounded_preserves_blue
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
        SweepDefs.chunked_is_blue mh target)
      (ensures
        (let (mh', _) =
           BDefs.chunked_push_children_bounded mh st obj i ws cap in
         SweepDefs.chunked_is_blue mh' target))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap
  else begin
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then begin
        BPres.chunked_push_children_bounded_preservation_ready_child
          mh obj i ws;
        assert (Seq.mem child (MH.major_objects mh));
        if target = child then begin
          SweepDefs.chunked_is_blue_read_header mh target;
          SweepDefs.chunked_is_white_read_header mh child;
          assert False
        end else
          MarkPres.chunked_make_gray_preserves_other_blue_status
            mh child target;
        let mh_gray = MarkDefs.chunked_make_gray mh child in
        let st' =
          if Seq.length st < cap then Seq.cons child st else st in
        if U64.v i < U64.v ws then begin
          MarkPres.chunked_make_gray_preserves_well_formed mh child;
          MarkPres.chunked_make_gray_preserves_major_objects mh child;
          BPres.chunked_push_children_bounded_preservation_ready_next
            mh obj i ws;
          chunked_push_children_bounded_preserves_blue
            mh_gray st' obj (U64.add i 1UL) ws cap target
        end
      end else if U64.v i < U64.v ws then begin
        BPres.chunked_push_children_bounded_preservation_ready_next
          mh obj i ws;
        chunked_push_children_bounded_preserves_blue
          mh st obj (U64.add i 1UL) ws cap target
      end
    end else if U64.v i < U64.v ws then begin
      BPres.chunked_push_children_bounded_preservation_ready_next
        mh obj i ws;
      chunked_push_children_bounded_preserves_blue
        mh st obj (U64.add i 1UL) ws cap target
    end
  end
#pop-options

#push-options "--z3rlimit 10"
let chunked_mark_step_bounded_preserves_blue
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        SweepDefs.chunked_is_blue mh target)
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_step_bounded mh st cap in
         SweepDefs.chunked_is_blue mh' target))
  =
  if Seq.length st = 0 then
    BDefs.chunked_mark_step_bounded_empty mh st cap
  else begin
    BReady.chunked_bounded_stack_head mh st;
    let obj = Seq.head st in
    if target = obj then begin
      BDefs.chunked_is_gray_read_header mh obj;
      SweepDefs.chunked_is_blue_read_header mh target;
      assert False
    end else
      MarkPres.chunked_make_black_preserves_other_blue_status mh obj target;
    let mh_black = MarkDefs.chunked_make_black mh obj in
    if MarkDefs.chunked_is_no_scan mh obj then
      BDefs.chunked_mark_step_bounded_no_scan mh st cap
    else begin
      BDefs.chunked_mark_step_bounded_scan mh st cap;
      BPres.chunked_mark_step_bounded_preservation_ready_scan mh st cap;
      MarkPres.chunked_make_black_preserves_well_formed mh obj;
      MarkPres.chunked_make_black_preserves_major_objects mh obj;
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_push_children_bounded_preserves_blue
        mh_black (Seq.tail st) obj 1UL ws cap target
    end
  end
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_mark_inner_loop_preserves_blue
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
        SweepDefs.chunked_is_blue mh target)
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_inner_loop mh st cap fuel in
         SweepDefs.chunked_is_blue mh' target))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    BDefs.chunked_mark_inner_loop_base mh st cap fuel
  else begin
    BPres.chunked_mark_inner_loop_preservation_ready_step mh st cap fuel;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    BPres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    chunked_mark_step_bounded_preserves_blue mh st cap target;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    assert (SweepDefs.chunked_is_blue mh' target);
    chunked_mark_inner_loop_preserves_blue
      mh' st' cap (fuel - 1) target;
    BDefs.chunked_mark_inner_loop_step mh st cap fuel
  end
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_mark_bounded_preserves_blue
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        SweepDefs.chunked_is_blue mh target)
      (ensures
        SweepDefs.chunked_is_blue
          (BDefs.chunked_mark_bounded mh cap fuel) target)
      (decreases fuel)
  =
  if fuel = 0 then
    BDefs.chunked_mark_bounded_base mh cap
  else begin
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      ()
    else begin
      BReady.chunked_rescan_heap_bounded_stack_props mh cap;
      BPres.chunked_mark_bounded_preservation_ready_step mh cap fuel;
      let inner_fuel = BDefs.chunked_count_non_black mh in
      chunked_mark_inner_loop_preserves_blue
        mh st cap inner_fuel target;
      BPres.chunked_mark_inner_loop_preserves_well_formed
        mh st cap inner_fuel;
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      assert (SweepDefs.chunked_is_blue mh' target);
      chunked_mark_bounded_preserves_blue mh' cap (fuel - 1) target
    end
  end
#pop-options

#push-options "--z3rlimit 5"
let chunked_major_field_preserved_refl
    (mh: MH.major_heap)
    (target: obj_addr)
  : Lemma
      (requires ChunkedMajorGraph.chunked_major_vertex mh target)
      (ensures ChunkedMajorGraph.chunked_major_field_preserved mh mh target)
  =
  let same_field (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
        (ensures
          MarkDefs.chunked_get_field mh target i ==
          MarkDefs.chunked_get_field mh target i)
    =
    ()
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires same_field);
  ChunkedMajorGraph.chunked_major_field_preserved_intro mh mh target

let chunked_major_field_preserved_trans
    (mh0 mh1 mh2: MH.major_heap)
    (target: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGraph.chunked_major_field_preserved mh0 mh1 target /\
        ChunkedMajorGraph.chunked_major_field_preserved mh1 mh2 target)
      (ensures
        ChunkedMajorGraph.chunked_major_field_preserved mh0 mh2 target)
  =
  ChunkedMajorGraph.chunked_major_field_preserved_elim mh0 mh1 target;
  ChunkedMajorGraph.chunked_major_field_preserved_elim mh1 mh2 target;
  let same_field (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh0 target))
        (ensures
          MarkDefs.chunked_get_field mh0 target i ==
          MarkDefs.chunked_get_field mh2 target i)
    =
    assert (SweepDefs.chunked_wosize_of_object mh0 target ==
            SweepDefs.chunked_wosize_of_object mh1 target);
    assert (MarkDefs.chunked_get_field mh0 target i ==
            MarkDefs.chunked_get_field mh1 target i);
    assert (MarkDefs.chunked_get_field mh1 target i ==
            MarkDefs.chunked_get_field mh2 target i)
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires same_field);
  ChunkedMajorGraph.chunked_major_field_preserved_intro mh0 mh2 target
#pop-options

#push-options "--z3rlimit 10"
let chunked_make_gray_field_preserved
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ChunkedMajorGraph.chunked_major_vertex mh target)
      (ensures
        ChunkedMajorGraph.chunked_major_field_preserved
          mh (MarkDefs.chunked_make_gray mh obj) target)
  =
  ChunkedMajorGraph.chunked_major_vertex_elim mh target;
  MarkPres.chunked_make_gray_preserves_major_objects mh obj;
  ChunkedMajorGraph.chunked_major_vertex_intro
    (MarkDefs.chunked_make_gray mh obj) target;
  MarkPres.chunked_make_gray_preserves_wosize_of_object mh obj target;
  let same_field (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
        (ensures
          MarkDefs.chunked_get_field mh target i ==
          MarkDefs.chunked_get_field
            (MarkDefs.chunked_make_gray mh obj) target i)
    =
    MarkPres.chunked_make_gray_preserves_get_field mh obj target i
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires same_field);
  ChunkedMajorGraph.chunked_major_field_preserved_intro
    mh (MarkDefs.chunked_make_gray mh obj) target

let chunked_make_black_field_preserved
    (mh: MH.major_heap)
    (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ChunkedMajorGraph.chunked_major_vertex mh target)
      (ensures
        ChunkedMajorGraph.chunked_major_field_preserved
          mh (MarkDefs.chunked_make_black mh obj) target)
  =
  ChunkedMajorGraph.chunked_major_vertex_elim mh target;
  MarkPres.chunked_make_black_preserves_major_objects mh obj;
  ChunkedMajorGraph.chunked_major_vertex_intro
    (MarkDefs.chunked_make_black mh obj) target;
  MarkPres.chunked_make_black_preserves_wosize_of_object mh obj target;
  let same_field (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
        (ensures
          MarkDefs.chunked_get_field mh target i ==
          MarkDefs.chunked_get_field
            (MarkDefs.chunked_make_black mh obj) target i)
    =
    MarkPres.chunked_make_black_preserves_get_field mh obj target i
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires same_field);
  ChunkedMajorGraph.chunked_major_field_preserved_intro
    mh (MarkDefs.chunked_make_black mh obj) target
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_push_children_bounded_preserves_ranges
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws)
      (ensures
        (let (mh', _) =
           BDefs.chunked_push_children_bounded mh st obj i ws cap in
         RangePres.same_chunk_ranges mh mh'))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then begin
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap;
    RangePres.same_chunk_ranges_refl mh
  end else begin
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then begin
        BPres.chunked_push_children_bounded_preservation_ready_child
          mh obj i ws;
        assert (Seq.mem child (MH.major_objects mh));
        let mh_gray = MarkDefs.chunked_make_gray mh child in
        MarkPres.chunked_make_gray_preserves_ranges mh child;
        if U64.v i < U64.v ws then begin
          MarkPres.chunked_make_gray_preserves_well_formed mh child;
          BPres.chunked_push_children_bounded_preservation_ready_next
            mh obj i ws;
          let st' =
            if Seq.length st < cap then Seq.cons child st else st in
          chunked_push_children_bounded_preserves_ranges
            mh_gray st' obj (U64.add i 1UL) ws cap;
          let (mh', _) =
            BDefs.chunked_push_children_bounded
              mh_gray st' obj (U64.add i 1UL) ws cap in
          RangePres.same_chunk_ranges_trans mh mh_gray mh'
        end
      end else if U64.v i < U64.v ws then begin
        BPres.chunked_push_children_bounded_preservation_ready_next
          mh obj i ws;
        chunked_push_children_bounded_preserves_ranges
          mh st obj (U64.add i 1UL) ws cap
      end else
        RangePres.same_chunk_ranges_refl mh
    end else if U64.v i < U64.v ws then begin
      BPres.chunked_push_children_bounded_preservation_ready_next
        mh obj i ws;
      chunked_push_children_bounded_preserves_ranges
        mh st obj (U64.add i 1UL) ws cap
    end else
      RangePres.same_chunk_ranges_refl mh
  end

let chunked_mark_step_bounded_preserves_ranges
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st)
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_step_bounded mh st cap in
         RangePres.same_chunk_ranges mh mh'))
  =
  if Seq.length st = 0 then begin
    BDefs.chunked_mark_step_bounded_empty mh st cap;
    RangePres.same_chunk_ranges_refl mh
  end else begin
    BReady.chunked_bounded_stack_head mh st;
    let obj = Seq.head st in
    let mh_black = MarkDefs.chunked_make_black mh obj in
    MarkPres.chunked_make_black_preserves_ranges mh obj;
    if MarkDefs.chunked_is_no_scan mh obj then
      BDefs.chunked_mark_step_bounded_no_scan mh st cap
    else begin
      BDefs.chunked_mark_step_bounded_scan mh st cap;
      BPres.chunked_mark_step_bounded_preservation_ready_scan mh st cap;
      MarkPres.chunked_make_black_preserves_well_formed mh obj;
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_push_children_bounded_preserves_ranges
        mh_black (Seq.tail st) obj 1UL ws cap;
      let (mh', _) =
        BDefs.chunked_push_children_bounded
          mh_black (Seq.tail st) obj 1UL ws cap in
      RangePres.same_chunk_ranges_trans mh mh_black mh'
    end
  end

let rec chunked_mark_inner_loop_preserves_ranges
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
         RangePres.same_chunk_ranges mh mh'))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then begin
    BDefs.chunked_mark_inner_loop_base mh st cap fuel;
    RangePres.same_chunk_ranges_refl mh
  end else begin
    BPres.chunked_mark_inner_loop_preservation_ready_step mh st cap fuel;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    BPres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    chunked_mark_step_bounded_preserves_ranges mh st cap;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    chunked_mark_inner_loop_preserves_ranges mh' st' cap (fuel - 1);
    let (mh_final, _) =
      BDefs.chunked_mark_inner_loop mh' st' cap (fuel - 1) in
    RangePres.same_chunk_ranges_trans mh mh' mh_final;
    BDefs.chunked_mark_inner_loop_step mh st cap fuel
  end

let rec chunked_mark_bounded_preserves_ranges
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel)
      (ensures
        RangePres.same_chunk_ranges
          mh (BDefs.chunked_mark_bounded mh cap fuel))
      (decreases fuel)
  =
  if fuel = 0 then begin
    BDefs.chunked_mark_bounded_base mh cap;
    RangePres.same_chunk_ranges_refl mh
  end else begin
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      RangePres.same_chunk_ranges_refl mh
    else begin
      BReady.chunked_rescan_heap_bounded_stack_props mh cap;
      BPres.chunked_mark_bounded_preservation_ready_step mh cap fuel;
      let inner_fuel = BDefs.chunked_count_non_black mh in
      chunked_mark_inner_loop_preserves_ranges mh st cap inner_fuel;
      BPres.chunked_mark_inner_loop_preserves_well_formed
        mh st cap inner_fuel;
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      chunked_mark_bounded_preserves_ranges mh' cap (fuel - 1);
      RangePres.same_chunk_ranges_trans
        mh mh' (BDefs.chunked_mark_bounded mh' cap (fuel - 1))
    end
  end
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_push_children_bounded_field_preserved
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
        ChunkedMajorGraph.chunked_major_vertex mh target)
      (ensures
        (let (mh', _) =
           BDefs.chunked_push_children_bounded mh st obj i ws cap in
         ChunkedMajorGraph.chunked_major_field_preserved mh mh' target))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then begin
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap;
    chunked_major_field_preserved_refl mh target
  end else begin
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then begin
        BPres.chunked_push_children_bounded_preservation_ready_child
          mh obj i ws;
        assert (Seq.mem child (MH.major_objects mh));
        let mh_gray = MarkDefs.chunked_make_gray mh child in
        chunked_make_gray_field_preserved mh child target;
        if U64.v i < U64.v ws then begin
          MarkPres.chunked_make_gray_preserves_well_formed mh child;
          BPres.chunked_push_children_bounded_preservation_ready_next
            mh obj i ws;
          let st' =
            if Seq.length st < cap then Seq.cons child st else st in
          ChunkedMajorGraph.chunked_major_field_preserved_elim
            mh mh_gray target;
          chunked_push_children_bounded_field_preserved
            mh_gray st' obj (U64.add i 1UL) ws cap target;
          let (mh', _) =
            BDefs.chunked_push_children_bounded
              mh_gray st' obj (U64.add i 1UL) ws cap in
          chunked_major_field_preserved_trans mh mh_gray mh' target
        end
      end else if U64.v i < U64.v ws then begin
        BPres.chunked_push_children_bounded_preservation_ready_next
          mh obj i ws;
        chunked_push_children_bounded_field_preserved
          mh st obj (U64.add i 1UL) ws cap target
      end else
        chunked_major_field_preserved_refl mh target
    end else if U64.v i < U64.v ws then begin
      BPres.chunked_push_children_bounded_preservation_ready_next
        mh obj i ws;
      chunked_push_children_bounded_field_preserved
        mh st obj (U64.add i 1UL) ws cap target
    end else
      chunked_major_field_preserved_refl mh target
  end

let chunked_mark_step_bounded_field_preserved
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        ChunkedMajorGraph.chunked_major_vertex mh target)
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_step_bounded mh st cap in
         ChunkedMajorGraph.chunked_major_field_preserved mh mh' target))
  =
  if Seq.length st = 0 then begin
    BDefs.chunked_mark_step_bounded_empty mh st cap;
    chunked_major_field_preserved_refl mh target
  end else begin
    BReady.chunked_bounded_stack_head mh st;
    let obj = Seq.head st in
    let mh_black = MarkDefs.chunked_make_black mh obj in
    chunked_make_black_field_preserved mh obj target;
    if MarkDefs.chunked_is_no_scan mh obj then
      BDefs.chunked_mark_step_bounded_no_scan mh st cap
    else begin
      BDefs.chunked_mark_step_bounded_scan mh st cap;
      BPres.chunked_mark_step_bounded_preservation_ready_scan mh st cap;
      MarkPres.chunked_make_black_preserves_well_formed mh obj;
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      ChunkedMajorGraph.chunked_major_field_preserved_elim
        mh mh_black target;
      chunked_push_children_bounded_field_preserved
        mh_black (Seq.tail st) obj 1UL ws cap target;
      let (mh', _) =
        BDefs.chunked_push_children_bounded
          mh_black (Seq.tail st) obj 1UL ws cap in
      chunked_major_field_preserved_trans mh mh_black mh' target
    end
  end

let rec chunked_mark_inner_loop_field_preserved
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
        ChunkedMajorGraph.chunked_major_vertex mh target)
      (ensures
        (let (mh', _) =
           BDefs.chunked_mark_inner_loop mh st cap fuel in
         ChunkedMajorGraph.chunked_major_field_preserved mh mh' target))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then begin
    BDefs.chunked_mark_inner_loop_base mh st cap fuel;
    chunked_major_field_preserved_refl mh target
  end else begin
    BPres.chunked_mark_inner_loop_preservation_ready_step mh st cap fuel;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    BPres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    chunked_mark_step_bounded_field_preserved mh st cap target;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    ChunkedMajorGraph.chunked_major_field_preserved_elim mh mh' target;
    chunked_mark_inner_loop_field_preserved
      mh' st' cap (fuel - 1) target;
    let (mh_final, _) =
      BDefs.chunked_mark_inner_loop mh' st' cap (fuel - 1) in
    chunked_major_field_preserved_trans mh mh' mh_final target;
    BDefs.chunked_mark_inner_loop_step mh st cap fuel
  end

let rec chunked_mark_bounded_field_preserved
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        ChunkedMajorGraph.chunked_major_vertex mh target)
      (ensures
        ChunkedMajorGraph.chunked_major_field_preserved
          mh (BDefs.chunked_mark_bounded mh cap fuel) target)
      (decreases fuel)
  =
  if fuel = 0 then begin
    BDefs.chunked_mark_bounded_base mh cap;
    chunked_major_field_preserved_refl mh target
  end else begin
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      chunked_major_field_preserved_refl mh target
    else begin
      BReady.chunked_rescan_heap_bounded_stack_props mh cap;
      BPres.chunked_mark_bounded_preservation_ready_step mh cap fuel;
      let inner_fuel = BDefs.chunked_count_non_black mh in
      chunked_mark_inner_loop_field_preserved mh st cap inner_fuel target;
      BPres.chunked_mark_inner_loop_preserves_well_formed
        mh st cap inner_fuel;
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      ChunkedMajorGraph.chunked_major_field_preserved_elim mh mh' target;
      chunked_mark_bounded_field_preserved mh' cap (fuel - 1) target;
      chunked_major_field_preserved_trans
        mh mh' (BDefs.chunked_mark_bounded mh' cap (fuel - 1)) target
    end
  end
#pop-options

#push-options "--z3rlimit 10"
let chunked_mark_bounded_pointer_classification_preserved
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel)
      (ensures
        ChunkedMajorGraph.chunked_major_pointer_classification_preserved
          mh (BDefs.chunked_mark_bounded mh cap fuel))
  =
  chunked_mark_bounded_preserves_ranges mh cap fuel;
  let same (v: U64.t)
    : Lemma
        (ensures
          MarkDefs.chunked_is_pointer_field mh v ==
          MarkDefs.chunked_is_pointer_field
            (BDefs.chunked_mark_bounded mh cap fuel) v)
    =
    MarkDefs.chunked_is_pointer_field_step mh v;
    MarkDefs.chunked_is_pointer_field_step
      (BDefs.chunked_mark_bounded mh cap fuel) v;
    RangePres.same_chunk_ranges_preserves_is_major_pointer
      mh (BDefs.chunked_mark_bounded mh cap fuel) v
  in
  FStar.Classical.forall_intro same;
  ChunkedMajorGraph.chunked_major_pointer_classification_preserved_intro
    mh (BDefs.chunked_mark_bounded mh cap fuel)
#pop-options

#push-options "--z3rlimit 10"
let chunked_mark_bounded_preserves_no_pointer_to_blue
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        MarkLive.chunked_no_pointer_to_blue mh)
      (ensures
        MarkLive.chunked_no_pointer_to_blue
          (BDefs.chunked_mark_bounded mh cap fuel))
  =
  let mh_mark = BDefs.chunked_mark_bounded mh cap fuel in
  BPres.chunked_mark_bounded_preserves_major_objects mh cap fuel;
  chunked_mark_bounded_pointer_classification_preserved mh cap fuel;
  let edge_no_blue (src dst: obj_addr)
    : Lemma
        (requires
          ChunkedMajorGraph.chunked_major_edge mh_mark src dst /\
          ~(SweepDefs.chunked_is_blue mh_mark src))
        (ensures ~(SweepDefs.chunked_is_blue mh_mark dst))
    =
    if SweepDefs.chunked_is_blue mh src then begin
      chunked_mark_bounded_preserves_blue mh cap fuel src;
      assert False
    end;
    ChunkedMajorGraph.chunked_major_edge_source_vertex mh_mark src dst;
    ChunkedMajorGraph.chunked_major_vertex_elim mh_mark src;
    ChunkedMajorGraph.chunked_major_vertex_intro mh src;
    chunked_mark_bounded_field_preserved mh cap fuel src;
    BMetadata.chunked_mark_bounded_preserves_no_scan_status
      mh cap fuel src;
    ChunkedMajorGraph.chunked_major_successors_preserved_from_fields
      mh mh_mark src;
    ChunkedMajorGraph.chunked_major_successors_preserved_elim
      mh mh_mark src;
    assert (ChunkedMajorGraph.chunked_major_edge mh src dst);
    MarkLive.chunked_no_pointer_to_blue_elim mh src dst;
    chunked_mark_bounded_no_new_blue mh cap fuel dst
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 edge_no_blue);
  MarkLive.chunked_no_pointer_to_blue_intro mh_mark
#pop-options
