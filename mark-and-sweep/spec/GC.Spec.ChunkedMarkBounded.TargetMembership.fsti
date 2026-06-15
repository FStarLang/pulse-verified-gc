module GC.Spec.ChunkedMarkBounded.TargetMembership

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module Readiness = GC.Spec.ChunkedMarkBounded.Readiness
module Roots = GC.Spec.ChunkedMajorGC.Roots

val chunked_scanned_white_targets_in_major
  (mh: MH.major_heap)
  : GTot prop

val chunked_scanned_raw_targets_in_major
  (mh: MH.major_heap)
  : GTot prop

val chunked_scanned_raw_targets_in_major_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (obj: obj_addr) (i: U64.t{U64.v i >= 1}).
          Seq.mem obj (MH.major_objects mh) /\
          ~(GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh obj) /\
          U64.v i <=
            U64.v
              (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                mh obj) ==>
          (let v = GC.Spec.ChunkedMark.Defs.chunked_get_field mh obj i in
           if GC.Spec.ChunkedMark.Defs.chunked_is_pointer_field mh v then
             let child_raw =
               GC.Spec.ChunkedMark.Defs.chunked_pointer_field_as_obj_addr mh v in
             Seq.mem child_raw (MH.major_objects mh) /\
             ~(GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_infix mh child_raw)
           else
             True))
      (ensures chunked_scanned_raw_targets_in_major mh)

val chunked_scanned_white_targets_in_major_from_raw_targets
  (mh: MH.major_heap)
  : Lemma
      (requires chunked_scanned_raw_targets_in_major mh)
      (ensures chunked_scanned_white_targets_in_major mh)

val chunked_scanned_raw_targets_in_major_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_scanned_raw_targets_in_major mh)
      (ensures
        chunked_scanned_raw_targets_in_major
          (Roots.chunked_gray_roots mh roots))

val chunked_scanned_white_targets_in_major_elim
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        chunked_scanned_white_targets_in_major mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ~(GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh obj) /\
        U64.v i <=
          U64.v
            (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
              mh obj) /\
        (let v = GC.Spec.ChunkedMark.Defs.chunked_get_field mh obj i in
         GC.Spec.ChunkedMark.Defs.chunked_is_pointer_field mh v /\
         (let child_raw =
            GC.Spec.ChunkedMark.Defs.chunked_pointer_field_as_obj_addr mh v in
          let child =
            GC.Spec.ChunkedMark.Defs.chunked_resolve_object mh child_raw in
          GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white mh child)))
      (ensures
        (let v = GC.Spec.ChunkedMark.Defs.chunked_get_field mh obj i in
         let child_raw =
           GC.Spec.ChunkedMark.Defs.chunked_pointer_field_as_obj_addr mh v in
         let child =
           GC.Spec.ChunkedMark.Defs.chunked_resolve_object mh child_raw in
         Seq.mem child (MH.major_objects mh)))

val chunked_push_children_scanned_targets_policy
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : GTot prop

val chunked_push_children_target_membership_policy_from_scanned_targets
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ~(GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh obj) /\
        U64.v ws <=
          U64.v
            (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
              mh obj) /\
        chunked_push_children_scanned_targets_policy mh obj i ws)
      (ensures
        Readiness.chunked_push_children_target_membership_policy
          mh obj i ws)

val chunked_mark_step_scanned_targets_policy
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : GTot prop

val chunked_mark_step_target_membership_policy_from_scanned_targets
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_scanned_targets_policy mh st cap)
      (ensures
        Readiness.chunked_mark_step_target_membership_policy mh st cap)

val chunked_mark_inner_loop_scanned_targets_policy
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : GTot prop

val chunked_mark_inner_loop_target_membership_policy_from_scanned_targets
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

val chunked_mark_bounded_scanned_targets_policy
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : GTot prop

val chunked_mark_bounded_raw_targets_policy
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : GTot prop

val chunked_mark_bounded_scanned_targets_policy_from_raw_targets
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires chunked_mark_bounded_raw_targets_policy mh cap fuel)
      (ensures chunked_mark_bounded_scanned_targets_policy mh cap fuel)

val chunked_mark_bounded_target_membership_policy_from_scanned_targets
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_scanned_targets_policy mh cap fuel)
      (ensures
        Readiness.chunked_mark_bounded_target_membership_policy mh cap fuel)

val chunked_mark_bounded_target_membership_policy_from_raw_targets
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_raw_targets_policy mh cap fuel)
      (ensures
        Readiness.chunked_mark_bounded_target_membership_policy mh cap fuel)

val chunked_mark_bounded_preservation_ready_from_scanned_targets
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_scanned_targets_policy mh cap fuel)
      (ensures
        GC.Spec.ChunkedMarkBounded.Preservation.chunked_mark_bounded_preservation_ready
          mh cap fuel)

val chunked_mark_bounded_preservation_ready_from_raw_targets
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_raw_targets_policy mh cap fuel)
      (ensures
        GC.Spec.ChunkedMarkBounded.Preservation.chunked_mark_bounded_preservation_ready
          mh cap fuel)

val chunked_mark_bounded_raw_targets_policy_from_static
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_scanned_raw_targets_in_major mh)
      (ensures chunked_mark_bounded_raw_targets_policy mh cap fuel)
