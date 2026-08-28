module GC.SPOT.MinorInfixCall

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.Impl
open GC.Impl.Heap
open GC.Impl.Stack

module CheneyImpl = GC.Gen.Impl.Cheney
module CheneySpec = GC.Gen.Cheney
module GenInv = GC.Gen.HeapInvariant
module Major = GC.SPOT.ConcreteMajorInfix
module MIPre = GC.SPOT.MinorInfixPre

/// Running the real collector on a heap whose major object points *into the
/// middle of a nursery closure*.
///
/// The precondition is discharged entirely by `GC.SPOT.MinorInfixPre`, so
/// calling this function at all is the machine-checked statement that `gen_gc`
/// accepts a major-to-minor interior pointer --- the exact shape that
/// `GC.SPOT.MinorInfixPre.spot_mi_was_forbidden` shows the pre-Phase-H
/// invariant ruled out.
///
/// The postcondition records what comes back:
///
///   * `GC.Gen.HeapInvariant.collection_heap_shape` --- literally the predicate
///     the precondition demands --- holds again of the returned state, so the
///     runtime can go straight into the next cycle;
///   * the nursery handed back is the zeroed one;
///   * the root array has been rewritten to the Cheney-collected roots, so the
///     interior root has been forwarded rather than dropped.
///
/// `snd res` is deliberately left unconstrained.  `gen_gc` reports failure only
/// on a concrete out-of-memory event (`CheneyBFS.cheney_oom`), and ruling that
/// out for a nursery with live content is a separate, and much larger, proof
/// obligation (`GC.SPOT.ConcreteForwarding` does it for the two-object nursery
/// in 600 lines).  It is orthogonal to the question this SPOT answers.
fn call_gen_gc_minor_infix
  (r: (r:unit{Major.spot_major_room}))
  (gh: gen_heap_t)
  (roots: array U64.t) (nroots: SZ.t)
  (fwd_arr: array U64.t)
  (queue: larray U64.t CheneyImpl.queue_size)
  (slots: array U64.t) (nslots: SZ.t)
  (st: gray_stack)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           is_gray_stack st 'st **
           pure (SZ.v nroots == Seq.length 'rs /\
                 ({ data = 'd; bump = 'b } <: minor_state) == MIPre.spot_mi_minor /\
                 's == Major.spot_major_heap r /\
                 'fp == Major.spot_major_fp r /\
                 'rs == MIPre.spot_mi_roots r /\
                 'farr == MIPre.spot_mi_fwd_array /\
                 'sl == MIPre.spot_mi_slots r /\
                 SZ.v nslots == 1 /\
                 'st == Seq.empty /\
                 stack_capacity st >= 2)
  returns res: (U64.t & bool)
  ensures exists* d2 b2 s2 rs2 farr2 qv2 st2.
    is_gen_heap gh d2 b2 s2 (fst res) **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    is_gray_stack st st2 **
    pure (
      ({ data = d2; bump = b2 } <: minor_state) == minor_reset MIPre.spot_mi_minor /\
      GenInv.collection_heap_shape
        ({ data = d2; bump = b2 } <: minor_state) s2 (fst res) /\
      gen_gc_heap_shape_post d2 b2 s2 /\
      rs2 == (CheneySpec.cheney_collect_spec
                MIPre.spot_mi_minor (Major.spot_major_heap r)
                (Major.spot_major_fp r) (MIPre.spot_mi_roots r)).mc_roots)
{
  MIPre.spot_mi_gen_gc_pre r (stack_capacity st);
  GC.SPOT.Preconditions.gen_gc_pre_elim
    MIPre.spot_mi_minor 's 'fp 'rs 'farr 'sl (SZ.v nslots) 'st (stack_capacity st);
  GC.SPOT.Preconditions.minor_collect_full_pre_elim
    MIPre.spot_mi_minor 's 'fp 'rs 'farr 'sl (SZ.v nslots);
  let res = gen_gc gh roots nroots fwd_arr queue slots nslots st;
  with d2 b2 s2. assert (is_gen_heap gh d2 b2 s2 (fst res));
  gen_gc_heap_shape_post_intro d2 b2 s2 (fst res);
  res
}
