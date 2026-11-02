/// ---------------------------------------------------------------------------
/// GC.SPOT.IncrementalCycle - the incremental entry points compose
/// ---------------------------------------------------------------------------
///
/// A caller holding only `gen_gc`'s precondition runs one incremental major
/// collection -- `gen_gc_start`, one slice, then `finish_sweep` -- with no
/// fact supplied in between: each entry point's postcondition is the next
/// one's precondition (`gc_state` at whatever phase it leaves), and the cycle
/// ends idle in the stop-the-world shape `gen_gc` demands.  On success the
/// slice starts from the marked heap, and its result is the spec's slice of it.

module GC.SPOT.IncrementalCycle

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
open GC.Gen.Impl.Incremental
open GC.Impl.Heap
open GC.Impl.Stack

module CheneyImpl = GC.Gen.Impl.Cheney
module Ph = GC.Spec.Phase
module SL = GC.Spec.SweepPhase.Slice
module GenInv = GC.Gen.HeapInvariant
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module RT = GC.Gen.RefTable
module MinorFwd = GC.Gen.MinorCollectForwarding

fn incremental_cycle_spot
  (gh: gen_heap_t)
  (roots: array U64.t) (nroots: SZ.t)
  (fwd_arr: array U64.t)
  (queue: larray U64.t CheneyImpl.queue_size)
  (slots: array U64.t) (nslots: SZ.t)
  (st: gray_stack)
  requires gc_state gh 'd 'b 's 'fp Ph.Idle **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           is_gray_stack st 'st **
           pure (gen_gc_stack_budget 'rs 'st (stack_capacity st) /\
                 SZ.v nroots == Seq.length 'rs /\
                 Seq.length 'farr == UpdatePtrs.fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
                 RT.ref_table_sound 's 'sl (SZ.v nslots) /\
                 RT.ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
                 RT.slots_pairwise_distinct 'sl (SZ.v nslots) /\
                 MinorFwd.remembered_targets_in_roots 's 'rs 'sl (SZ.v nslots) /\
                 MinorFwd.roots_valid_for_minor_collection
                   ({ data = 'd; bump = 'b } <: minor_state) 's 'rs)
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2 st2.
    gc_state gh d2 b2 s2 fp2 Ph.Idle **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    is_gray_stack st st2 **
    pure (GenInv.collection_heap_shape ({ data = d2; bump = b2 } <: minor_state) s2 fp2 /\
          ({ data = d2; bump = b2 } <: minor_state) == minor_reset ({ data = 'd; bump = 'b } <: minor_state))
{
  let ok = gen_gc_start gh roots nroots fwd_arr queue slots nslots st;
  with d1 b1 s1 fp1 ph1. assert (gc_state gh d1 b1 s1 fp1 ph1);
  // on success the collector is sweeping the marked heap
  assert (pure (ok ==> ph1 == Ph.Sweeping GC.Spec.FusedSweep.sweep_start));
  let fin = sweep_slice gh 64UL;
  with s2 fp2 ph2. assert (gc_state gh d1 b1 s2 fp2 ph2);
  assert (pure ((s2, fp2, ph2) == SL.phase_slice s1 fp1 ph1 64));
  finish_sweep gh;
}
