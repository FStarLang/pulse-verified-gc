module GC.Spec.ChunkedMarkBounded.TagInvariant

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module MarkPres = GC.Spec.ChunkedMark.Preservation
module MarkDefs = GC.Spec.ChunkedMark.Defs
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady
module BStackStep = GC.Spec.ChunkedMarkBounded.StackStep

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

#push-options "--z3rlimit 10"
let rec chunked_push_children_bounded_preserves_tag_of_object
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
         SweepDefs.chunked_tag_of_object mh' target ==
         SweepDefs.chunked_tag_of_object mh target))
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
        MarkPres.chunked_make_gray_preserves_tag_of_object mh child target;
        if U64.v i < U64.v ws then begin
          MarkPres.chunked_make_gray_preserves_well_formed mh child;
          MarkPres.chunked_make_gray_preserves_major_objects mh child;
          BPres.chunked_push_children_bounded_preservation_ready_next
            mh obj i ws;
          let st' =
            if Seq.length st < cap then Seq.cons child st else st in
          chunked_push_children_bounded_preserves_tag_of_object
            mh_gray st' obj (U64.add i 1UL) ws cap target
        end
      end else if U64.v i < U64.v ws then begin
        BPres.chunked_push_children_bounded_preservation_ready_next
          mh obj i ws;
        chunked_push_children_bounded_preserves_tag_of_object
          mh st obj (U64.add i 1UL) ws cap target
      end
    end else if U64.v i < U64.v ws then begin
      BPres.chunked_push_children_bounded_preservation_ready_next
        mh obj i ws;
      chunked_push_children_bounded_preserves_tag_of_object
        mh st obj (U64.add i 1UL) ws cap target
    end
  end

let chunked_push_children_bounded_preserves_infix_status
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
         SweepDefs.chunked_is_infix mh' target ==
         SweepDefs.chunked_is_infix mh target))
  =
  chunked_push_children_bounded_preserves_tag_of_object
    mh st obj i ws cap target;
  let (mh', _) =
    BDefs.chunked_push_children_bounded mh st obj i ws cap in
  SweepDefs.chunked_is_infix_step mh target;
  SweepDefs.chunked_is_infix_step mh' target
#pop-options

#push-options "--z3rlimit 10"
let chunked_mark_step_bounded_preserves_tag_of_object
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
         SweepDefs.chunked_tag_of_object mh' target ==
         SweepDefs.chunked_tag_of_object mh target))
  =
  if Seq.length st = 0 then
    BDefs.chunked_mark_step_bounded_empty mh st cap
  else begin
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    BReady.chunked_bounded_stack_head mh st;
    let obj = Seq.head st in
    let mh_black = MarkDefs.chunked_make_black mh obj in
    MarkPres.chunked_make_black_preserves_tag_of_object mh obj target;
    if MarkDefs.chunked_is_no_scan mh obj then
      BDefs.chunked_mark_step_bounded_no_scan mh st cap
    else begin
      BDefs.chunked_mark_step_bounded_scan mh st cap;
      BPres.chunked_mark_step_bounded_preservation_ready_scan mh st cap;
      MarkPres.chunked_make_black_preserves_well_formed mh obj;
      MarkPres.chunked_make_black_preserves_major_objects mh obj;
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_push_children_bounded_preserves_tag_of_object
        mh_black (Seq.tail st) obj 1UL ws cap target
    end
  end

let chunked_mark_step_bounded_preserves_infix_status
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
         SweepDefs.chunked_is_infix mh' target ==
         SweepDefs.chunked_is_infix mh target))
  =
  chunked_mark_step_bounded_preserves_tag_of_object mh st cap target;
  let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
  SweepDefs.chunked_is_infix_step mh target;
  SweepDefs.chunked_is_infix_step mh' target
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_mark_inner_loop_preserves_tag_of_object
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
         SweepDefs.chunked_tag_of_object mh' target ==
         SweepDefs.chunked_tag_of_object mh target))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    BDefs.chunked_mark_inner_loop_base mh st cap fuel
  else begin
    assert (fuel > 0);
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    let fuel_pred : n:nat{n < fuel} = fuel - 1 in
    BPres.chunked_mark_inner_loop_preservation_ready_step mh st cap fuel;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    BPres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    BPres.chunked_mark_step_bounded_preserves_major_objects mh st cap;
    chunked_mark_step_bounded_preserves_tag_of_object mh st cap target;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    chunked_mark_inner_loop_preserves_tag_of_object
      mh' st' cap fuel_pred target;
    BDefs.chunked_mark_inner_loop_step mh st cap fuel
  end

let chunked_mark_inner_loop_preserves_infix_status
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
         SweepDefs.chunked_is_infix mh' target ==
         SweepDefs.chunked_is_infix mh target))
      (decreases fuel)
  =
  chunked_mark_inner_loop_preserves_tag_of_object mh st cap fuel target;
  let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap fuel in
  SweepDefs.chunked_is_infix_step mh target;
  SweepDefs.chunked_is_infix_step mh' target
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_mark_bounded_preserves_tag_of_object
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
        SweepDefs.chunked_tag_of_object
          (BDefs.chunked_mark_bounded mh cap fuel) target ==
        SweepDefs.chunked_tag_of_object mh target)
      (decreases fuel)
  =
  if fuel = 0 then
    BDefs.chunked_mark_bounded_base mh cap
  else begin
    assert (fuel > 0);
    let fuel_pred : n:nat{n < fuel} = fuel - 1 in
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      ()
    else begin
      BReady.chunked_rescan_heap_bounded_stack_props mh cap;
      BPres.chunked_mark_bounded_preservation_ready_step mh cap fuel;
      let inner_fuel = BDefs.chunked_count_non_black mh in
      chunked_mark_inner_loop_preserves_tag_of_object
        mh st cap inner_fuel target;
      BPres.chunked_mark_inner_loop_preserves_well_formed
        mh st cap inner_fuel;
      BPres.chunked_mark_inner_loop_preserves_major_objects
        mh st cap inner_fuel;
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      assert (Seq.mem target (MH.major_objects mh'));
      chunked_mark_bounded_preserves_tag_of_object
        mh' cap fuel_pred target
    end
  end

let chunked_mark_bounded_preserves_infix_status
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
        SweepDefs.chunked_is_infix
          (BDefs.chunked_mark_bounded mh cap fuel) target ==
        SweepDefs.chunked_is_infix mh target)
      (decreases fuel)
  =
  chunked_mark_bounded_preserves_tag_of_object mh cap fuel target;
  SweepDefs.chunked_is_infix_step mh target;
  SweepDefs.chunked_is_infix_step (BDefs.chunked_mark_bounded mh cap fuel) target
#pop-options
