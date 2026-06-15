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

val chunked_mark_bounded_preservation_ready_from_target_membership
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires chunked_mark_bounded_target_membership_policy mh cap fuel)
      (ensures Pres.chunked_mark_bounded_preservation_ready mh cap fuel)
