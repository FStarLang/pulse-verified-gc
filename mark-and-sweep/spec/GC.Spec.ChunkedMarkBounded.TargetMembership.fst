module GC.Spec.ChunkedMarkBounded.TargetMembership

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module Pres = GC.Spec.ChunkedMarkBounded.Preservation
module MarkPres = GC.Spec.ChunkedMark.Preservation
module Readiness = GC.Spec.ChunkedMarkBounded.Readiness

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

let chunked_scanned_white_targets_in_major
    (mh: MH.major_heap)
  : GTot prop
  =
  forall (obj: obj_addr) (i: U64.t{U64.v i >= 1}).
    Seq.mem obj (MH.major_objects mh) /\
    U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) ==>
    (let v = MarkDefs.chunked_get_field mh obj i in
     if MarkDefs.chunked_is_pointer_field mh v then
       let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
       let child = MarkDefs.chunked_resolve_object mh child_raw in
       SweepDefs.chunked_is_white mh child ==>
         Seq.mem child (MH.major_objects mh)
     else
       True)

let chunked_scanned_white_targets_in_major_elim
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        chunked_scanned_white_targets_in_major mh /\
        Seq.mem obj (MH.major_objects mh) /\
        U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) /\
        (let v = MarkDefs.chunked_get_field mh obj i in
         MarkDefs.chunked_is_pointer_field mh v /\
         (let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
          let child = MarkDefs.chunked_resolve_object mh child_raw in
          SweepDefs.chunked_is_white mh child)))
      (ensures
        (let v = MarkDefs.chunked_get_field mh obj i in
         let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
         let child = MarkDefs.chunked_resolve_object mh child_raw in
         Seq.mem child (MH.major_objects mh)))
  =
  ()

let rec chunked_push_children_scanned_targets_policy
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Tot prop
    (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then True
  else
    let v = MarkDefs.chunked_get_field mh obj i in
    let mh' =
      if MarkDefs.chunked_is_pointer_field mh v then
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then
          MarkDefs.chunked_make_gray mh child
        else
          mh
      else
        mh in
    chunked_scanned_white_targets_in_major mh /\
    (if U64.v i < U64.v ws then
      chunked_push_children_scanned_targets_policy
        mh' obj (U64.add i 1UL) ws
     else
      True)

let rec chunked_push_children_target_membership_policy_from_scanned_targets
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        U64.v ws <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) /\
        chunked_push_children_scanned_targets_policy mh obj i ws)
      (ensures
        Readiness.chunked_push_children_target_membership_policy
          mh obj i ws)
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    Readiness.chunked_push_children_target_membership_policy_base_intro
      mh obj i ws
  else begin
    let v = MarkDefs.chunked_get_field mh obj i in
    let mh' =
      if MarkDefs.chunked_is_pointer_field mh v then
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then
          MarkDefs.chunked_make_gray mh child
        else
          mh
      else
        mh in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then
        chunked_scanned_white_targets_in_major_elim mh obj i
    end;
    if U64.v i < U64.v ws then begin
      if MarkDefs.chunked_is_pointer_field mh v then begin
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then begin
          assert (Seq.mem child (MH.major_objects mh));
          MarkPres.chunked_make_gray_preserves_major_objects mh child;
          MarkPres.chunked_make_gray_preserves_well_formed mh child;
          assert (MH.major_objects mh' == MH.major_objects mh);
          assert (Seq.mem obj (MH.major_objects mh'));
          MarkPres.chunked_make_gray_preserves_wosize_of_object mh child obj;
          assert (SweepDefs.chunked_wosize_of_object mh' obj ==
                  SweepDefs.chunked_wosize_of_object mh obj)
        end
      end;
      assert (MH.well_formed_major_heap mh');
      assert (Seq.mem obj (MH.major_objects mh'));
      assert (U64.v ws <= U64.v (SweepDefs.chunked_wosize_of_object mh' obj));
      assert (chunked_push_children_scanned_targets_policy
        mh' obj (U64.add i 1UL) ws);
      chunked_push_children_target_membership_policy_from_scanned_targets
        mh' obj (U64.add i 1UL) ws
    end;
    Readiness.chunked_push_children_target_membership_policy_step_intro
      mh obj i ws
  end

let chunked_mark_step_scanned_targets_policy
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : GTot prop
  =
  if Seq.length st = 0 then True
  else
    let obj = Seq.head st in
    Seq.mem obj (MH.major_objects mh) /\
    (if MarkDefs.chunked_is_no_scan mh obj then
      True
     else
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_push_children_scanned_targets_policy mh' obj 1UL ws)

let chunked_mark_step_target_membership_policy_from_scanned_targets
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_scanned_targets_policy mh st cap)
      (ensures
        Readiness.chunked_mark_step_target_membership_policy mh st cap)
  =
  if Seq.length st = 0 then
    Readiness.chunked_mark_step_target_membership_policy_intro mh st cap
  else begin
    let obj = Seq.head st in
    if MarkDefs.chunked_is_no_scan mh obj then
      ()
    else begin
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      MarkPres.chunked_make_black_preserves_major_objects mh obj;
      MarkPres.chunked_make_black_preserves_well_formed mh obj;
      MarkPres.chunked_make_black_preserves_wosize_of_object mh obj obj;
      assert (MH.major_objects mh' == MH.major_objects mh);
      assert (Seq.mem obj (MH.major_objects mh'));
      assert (SweepDefs.chunked_wosize_of_object mh' obj ==
              SweepDefs.chunked_wosize_of_object mh obj);
      chunked_push_children_target_membership_policy_from_scanned_targets
        mh' obj 1UL ws
    end;
    Readiness.chunked_mark_step_target_membership_policy_intro mh st cap
  end

let rec chunked_mark_inner_loop_scanned_targets_policy
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Tot prop
    (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then True
  else
    let fuel_pred : n:nat{n < fuel} = fuel - 1 in
    chunked_mark_step_scanned_targets_policy mh st cap /\
    (let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
     chunked_mark_inner_loop_scanned_targets_policy
       mh' st' cap fuel_pred)

let rec chunked_mark_inner_loop_target_membership_policy_from_scanned_targets
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_inner_loop_scanned_targets_policy mh st cap fuel)
      (ensures
        Readiness.chunked_mark_inner_loop_target_membership_policy
          mh st cap fuel)
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    Readiness.chunked_mark_inner_loop_target_membership_policy_base_intro
      mh st cap fuel
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    assert (fuel > 0);
    let fuel_pred : n:nat{n < fuel} = fuel - 1 in
    chunked_mark_step_target_membership_policy_from_scanned_targets mh st cap;
    Readiness.chunked_mark_step_bounded_preservation_ready_from_target_membership
      mh st cap;
    Pres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    assert (MH.well_formed_major_heap mh');
    assert (chunked_mark_inner_loop_scanned_targets_policy
      mh' st' cap fuel_pred);
    chunked_mark_inner_loop_target_membership_policy_from_scanned_targets
      mh' st' cap fuel_pred;
    Readiness.chunked_mark_inner_loop_target_membership_policy_step_intro
      mh st cap fuel
  end

let rec chunked_mark_bounded_scanned_targets_policy
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Tot prop
    (decreases fuel)
  =
  if fuel = 0 then True
  else
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then True
    else
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let fuel_pred : n:nat{n < fuel} = fuel - 1 in
      chunked_mark_inner_loop_scanned_targets_policy mh st cap inner_fuel /\
      (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
       chunked_mark_bounded_scanned_targets_policy mh' cap fuel_pred)

let rec chunked_mark_bounded_target_membership_policy_from_scanned_targets
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_scanned_targets_policy mh cap fuel)
      (ensures
        Readiness.chunked_mark_bounded_target_membership_policy mh cap fuel)
      (decreases fuel)
  =
  if fuel = 0 then
    Readiness.chunked_mark_bounded_target_membership_policy_base_intro
      mh cap
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    assert (fuel > 0);
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      Readiness.chunked_mark_bounded_target_membership_policy_empty_intro
        mh cap fuel
    else begin
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let fuel_pred : n:nat{n < fuel} = fuel - 1 in
      chunked_mark_inner_loop_target_membership_policy_from_scanned_targets
        mh st cap inner_fuel;
      Readiness.chunked_mark_inner_loop_preservation_ready_from_target_membership
        mh st cap inner_fuel;
      Pres.chunked_mark_inner_loop_preserves_well_formed
        mh st cap inner_fuel;
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      assert (MH.well_formed_major_heap mh');
      assert (chunked_mark_bounded_scanned_targets_policy
        mh' cap fuel_pred);
      chunked_mark_bounded_target_membership_policy_from_scanned_targets
        mh' cap fuel_pred;
      Readiness.chunked_mark_bounded_target_membership_policy_step_intro
        mh cap fuel
    end
  end

let chunked_mark_bounded_preservation_ready_from_scanned_targets
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_scanned_targets_policy mh cap fuel)
      (ensures
        Pres.chunked_mark_bounded_preservation_ready mh cap fuel)
  =
  chunked_mark_bounded_target_membership_policy_from_scanned_targets
    mh cap fuel;
  Readiness.chunked_mark_bounded_preservation_ready_from_target_membership
    mh cap fuel
