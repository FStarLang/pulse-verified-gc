module GC.Spec.ChunkedMarkBounded.Readiness

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module Pres = GC.Spec.ChunkedMarkBounded.Preservation

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

let rec chunked_push_children_target_membership_policy
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
    (if MarkDefs.chunked_is_pointer_field mh v then
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      SweepDefs.chunked_is_white mh child ==>
        Seq.mem child (MH.major_objects mh)
     else
      True) /\
    (if U64.v i < U64.v ws then
      chunked_push_children_target_membership_policy
        mh' obj (U64.add i 1UL) ws
     else
      True)

let chunked_push_children_target_membership_policy_base_intro
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires U64.v i > U64.v ws)
      (ensures chunked_push_children_target_membership_policy mh obj i ws)
  =
  ()

let chunked_push_children_target_membership_policy_step_intro
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires
       U64.v i <= U64.v ws /\
       (let v = MarkDefs.chunked_get_field mh obj i in
        if MarkDefs.chunked_is_pointer_field mh v then
          let child_raw =
            MarkDefs.chunked_pointer_field_as_obj_addr mh v in
          let child =
            MarkDefs.chunked_resolve_object mh child_raw in
          SweepDefs.chunked_is_white mh child ==>
            Seq.mem child (MH.major_objects mh)
        else
          True) /\
       (if U64.v i < U64.v ws then
         (let v = MarkDefs.chunked_get_field mh obj i in
          let mh' =
            if MarkDefs.chunked_is_pointer_field mh v then
              let child_raw =
                MarkDefs.chunked_pointer_field_as_obj_addr mh v in
              let child =
                MarkDefs.chunked_resolve_object mh child_raw in
              if SweepDefs.chunked_is_white mh child then
                MarkDefs.chunked_make_gray mh child
              else
                mh
            else
              mh in
          chunked_push_children_target_membership_policy
            mh' obj (U64.add i 1UL) ws)
        else
          True))
      (ensures chunked_push_children_target_membership_policy mh obj i ws)
  =
  ()

let rec chunked_push_children_bounded_preservation_ready_from_target_membership
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Lemma
      (requires chunked_push_children_target_membership_policy mh obj i ws)
      (ensures Pres.chunked_push_children_bounded_preservation_ready mh obj i ws)
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    Pres.chunked_push_children_bounded_preservation_ready_intro mh obj i ws
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
    if U64.v i < U64.v ws then begin
      assert (chunked_push_children_target_membership_policy
        mh' obj (U64.add i 1UL) ws);
      chunked_push_children_bounded_preservation_ready_from_target_membership
        mh' obj (U64.add i 1UL) ws
    end;
    Pres.chunked_push_children_bounded_preservation_ready_intro mh obj i ws
  end

let chunked_mark_step_target_membership_policy
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : prop =
  if Seq.length st = 0 then True
  else
    let obj = Seq.head st in
    Seq.mem obj (MH.major_objects mh) /\
    (if MarkDefs.chunked_is_no_scan mh obj then
      True
     else
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_push_children_target_membership_policy mh' obj 1UL ws)

let chunked_mark_step_target_membership_policy_intro
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        (Seq.length st > 0 ==>
          Seq.mem (Seq.head st) (MH.major_objects mh)) /\
        ((Seq.length st > 0 /\
          ~(MarkDefs.chunked_is_no_scan mh (Seq.head st))) ==>
          (let obj = Seq.head st in
           let mh' = MarkDefs.chunked_make_black mh obj in
           let ws = SweepDefs.chunked_wosize_of_object mh obj in
           chunked_push_children_target_membership_policy mh' obj 1UL ws)))
      (ensures chunked_mark_step_target_membership_policy mh st cap)
  =
  if Seq.length st = 0 then
    ()
  else begin
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    assert (Seq.length st > 0);
    assert (Seq.mem (Seq.head st) (MH.major_objects mh));
    if MarkDefs.chunked_is_no_scan mh (Seq.head st) then
      ()
    else begin
      let obj = Seq.head st in
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      assert (chunked_push_children_target_membership_policy mh' obj 1UL ws)
    end
  end

let chunked_mark_step_bounded_preservation_ready_from_target_membership
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires chunked_mark_step_target_membership_policy mh st cap)
      (ensures Pres.chunked_mark_step_bounded_preservation_ready mh st cap)
  =
  if Seq.length st = 0 then
    Pres.chunked_mark_step_bounded_preservation_ready_intro mh st cap
  else begin
    let obj = Seq.head st in
    if MarkDefs.chunked_is_no_scan mh obj then
      Pres.chunked_mark_step_bounded_preservation_ready_intro mh st cap
    else begin
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_push_children_bounded_preservation_ready_from_target_membership
        mh' obj 1UL ws;
      Pres.chunked_mark_step_bounded_preservation_ready_intro mh st cap
    end
  end

let rec chunked_mark_inner_loop_target_membership_policy
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
    chunked_mark_step_target_membership_policy mh st cap /\
    (let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
     chunked_mark_inner_loop_target_membership_policy
       mh' st' cap fuel_pred)

let chunked_mark_inner_loop_target_membership_policy_base_intro
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
     (requires fuel = 0 \/ Seq.length st = 0)
     (ensures
       chunked_mark_inner_loop_target_membership_policy mh st cap fuel)
  =
  ()

let chunked_mark_inner_loop_target_membership_policy_step_intro
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
     (requires
       fuel > 0 /\
       Seq.length st > 0 /\
       chunked_mark_step_target_membership_policy mh st cap /\
       (let (mh', st') =
         BDefs.chunked_mark_step_bounded mh st cap in
        chunked_mark_inner_loop_target_membership_policy
          mh' st' cap (fuel - 1)))
     (ensures
       chunked_mark_inner_loop_target_membership_policy mh st cap fuel)
  =
  ()

let rec chunked_mark_inner_loop_preservation_ready_from_target_membership
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires chunked_mark_inner_loop_target_membership_policy mh st cap fuel)
      (ensures Pres.chunked_mark_inner_loop_preservation_ready mh st cap fuel)
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    Pres.chunked_mark_inner_loop_preservation_ready_base_intro mh st cap fuel
  else begin
    let fuel_pred : n:nat{n < fuel} = fuel - 1 in
    chunked_mark_step_bounded_preservation_ready_from_target_membership
      mh st cap;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    assert (chunked_mark_inner_loop_target_membership_policy
      mh' st' cap fuel_pred);
    chunked_mark_inner_loop_preservation_ready_from_target_membership
      mh' st' cap fuel_pred;
    Pres.chunked_mark_inner_loop_preservation_ready_step_intro mh st cap fuel
  end

let rec chunked_mark_bounded_target_membership_policy
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
      chunked_mark_inner_loop_target_membership_policy mh st cap inner_fuel /\
      (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
       chunked_mark_bounded_target_membership_policy mh' cap fuel_pred)

let chunked_mark_bounded_target_membership_policy_base_intro
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
  : Lemma
      (ensures chunked_mark_bounded_target_membership_policy mh cap 0)
  =
  ()

let chunked_mark_bounded_target_membership_policy_empty_intro
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        Seq.length (BDefs.chunked_rescan_heap mh Seq.empty cap) = 0)
      (ensures chunked_mark_bounded_target_membership_policy mh cap fuel)
  =
  ()

let chunked_mark_bounded_target_membership_policy_step_intro
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        (let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
         Seq.length st > 0 /\
         (let inner_fuel = BDefs.chunked_count_non_black mh in
          chunked_mark_inner_loop_target_membership_policy
            mh st cap inner_fuel /\
          (let (mh', _) =
            BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
           chunked_mark_bounded_target_membership_policy
             mh' cap (fuel - 1)))))
      (ensures chunked_mark_bounded_target_membership_policy mh cap fuel)
  =
  ()

let rec chunked_mark_bounded_preservation_ready_from_target_membership
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires chunked_mark_bounded_target_membership_policy mh cap fuel)
      (ensures Pres.chunked_mark_bounded_preservation_ready mh cap fuel)
      (decreases fuel)
  =
  if fuel = 0 then
    Pres.chunked_mark_bounded_preservation_ready_base_intro mh cap
  else begin
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      Pres.chunked_mark_bounded_preservation_ready_empty_intro mh cap fuel
    else begin
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let fuel_pred : n:nat{n < fuel} = fuel - 1 in
      chunked_mark_inner_loop_preservation_ready_from_target_membership
        mh st cap inner_fuel;
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      assert (chunked_mark_bounded_target_membership_policy
        mh' cap fuel_pred);
      chunked_mark_bounded_preservation_ready_from_target_membership
        mh' cap fuel_pred;
      Pres.chunked_mark_bounded_preservation_ready_step_intro mh cap fuel
    end
  end
