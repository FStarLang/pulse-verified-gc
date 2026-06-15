module GC.Spec.ChunkedMarkBounded.Readiness

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module Pres = GC.Spec.ChunkedMarkBounded.Preservation

val chunked_push_children_target_membership_policy
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : GTot prop

val chunked_push_children_target_membership_policy_base_intro
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires U64.v i > U64.v ws)
      (ensures chunked_push_children_target_membership_policy mh obj i ws)

val chunked_push_children_target_membership_policy_step_intro
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        U64.v i <= U64.v ws /\
        (let v = GC.Spec.ChunkedMark.Defs.chunked_get_field mh obj i in
         if GC.Spec.ChunkedMark.Defs.chunked_is_pointer_field mh v then
           let child_raw =
             GC.Spec.ChunkedMark.Defs.chunked_pointer_field_as_obj_addr mh v in
           let child =
             GC.Spec.ChunkedMark.Defs.chunked_resolve_object mh child_raw in
           GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white mh child ==>
             Seq.mem child (MH.major_objects mh)
         else
           True) /\
        (if U64.v i < U64.v ws then
          (let v = GC.Spec.ChunkedMark.Defs.chunked_get_field mh obj i in
           let mh' =
             if GC.Spec.ChunkedMark.Defs.chunked_is_pointer_field mh v then
               let child_raw =
                 GC.Spec.ChunkedMark.Defs.chunked_pointer_field_as_obj_addr mh v in
               let child =
                 GC.Spec.ChunkedMark.Defs.chunked_resolve_object mh child_raw in
               if GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white mh child then
                 GC.Spec.ChunkedMark.Defs.chunked_make_gray mh child
               else
                 mh
             else
               mh in
           chunked_push_children_target_membership_policy
             mh' obj (U64.add i 1UL) ws)
         else
           True))
      (ensures chunked_push_children_target_membership_policy mh obj i ws)

val chunked_push_children_bounded_preservation_ready_from_target_membership
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires chunked_push_children_target_membership_policy mh obj i ws)
      (ensures Pres.chunked_push_children_bounded_preservation_ready mh obj i ws)

val chunked_mark_step_target_membership_policy
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : GTot prop

val chunked_mark_step_target_membership_policy_intro
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        (Seq.length st > 0 ==>
          Seq.mem (Seq.head st) (MH.major_objects mh)) /\
        ((Seq.length st > 0 /\
          ~(GC.Spec.ChunkedMark.Defs.chunked_is_no_scan
            mh (Seq.head st))) ==>
          (let obj = Seq.head st in
           let mh' = GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj in
           let ws =
             GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
               mh obj in
           chunked_push_children_target_membership_policy mh' obj 1UL ws)))
      (ensures chunked_mark_step_target_membership_policy mh st cap)

val chunked_mark_step_bounded_preservation_ready_from_target_membership
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires chunked_mark_step_target_membership_policy mh st cap)
      (ensures Pres.chunked_mark_step_bounded_preservation_ready mh st cap)

val chunked_mark_inner_loop_target_membership_policy
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : GTot prop

val chunked_mark_inner_loop_target_membership_policy_base_intro
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires fuel = 0 \/ Seq.length st = 0)
      (ensures
        chunked_mark_inner_loop_target_membership_policy mh st cap fuel)

val chunked_mark_inner_loop_target_membership_policy_step_intro
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

val chunked_mark_inner_loop_preservation_ready_from_target_membership
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires chunked_mark_inner_loop_target_membership_policy mh st cap fuel)
      (ensures Pres.chunked_mark_inner_loop_preservation_ready mh st cap fuel)

val chunked_mark_bounded_target_membership_policy
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : GTot prop

val chunked_mark_bounded_target_membership_policy_base_intro
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  : Lemma
      (ensures chunked_mark_bounded_target_membership_policy mh cap 0)

val chunked_mark_bounded_target_membership_policy_empty_intro
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        Seq.length (BDefs.chunked_rescan_heap mh Seq.empty cap) = 0)
      (ensures chunked_mark_bounded_target_membership_policy mh cap fuel)

val chunked_mark_bounded_target_membership_policy_step_intro
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

val chunked_mark_bounded_preservation_ready_from_target_membership
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires chunked_mark_bounded_target_membership_policy mh cap fuel)
      (ensures Pres.chunked_mark_bounded_preservation_ready mh cap fuel)
