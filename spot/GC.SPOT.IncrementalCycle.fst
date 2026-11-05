/// ---------------------------------------------------------------------------
/// GC.SPOT.IncrementalCycle - the incremental entry points compose
/// ---------------------------------------------------------------------------
///
/// A caller holding only `gen_gc`'s precondition runs one incremental major
/// collection -- `gen_gc_start`, one slice, then `finish_sweep` -- with no
/// fact supplied in between: each entry point's postcondition is the next
/// one's precondition (`gc_state` at whatever phase it leaves), and the cycle
/// ends idle in the stop-the-world shape `gen_gc` demands.  On success the
/// slice starts from the marked heap, and its result is the spec's slice of it;
/// and the sweep's completeness applies to the cycle (`cycle_frees_dead`): at
/// the end every object white in the marked heap -- unreachable from the
/// roots when marking ended, given that the roots reach the graph
/// (`GC.Spec.SweepPhase.Completeness.roots_in_graph`, which `gen_gc_start`'s
/// postcondition does not carry) -- is freed.

module GC.SPOT.IncrementalCycle

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Phase
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
module GI = GC.Gen.Incremental
module Corr = GC.Spec.Correctness
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPC = GC.Spec.SweepPhase.Completeness

/// Every object white in the marked heap `s1` is freed in `s3`, and so is
/// every object unreachable from the roots when marking ended.
let cycle_frees_dead_post (h_init: heap) (roots: Seq.seq obj_addr) (s1 s3: heap) : prop =
  (forall (x: obj_addr). SPI.white_after_mark s1 x ==> SPC.freed s3 x) /\
  (SPC.roots_in_graph h_init roots ==>
     (forall (x: obj_addr). SPC.dead_at_mark h_init s1 roots x ==> SPC.freed s3 x))

/// **The cycle frees what marking left dead**: from the marked heap `s1` at
/// the start of the sweep, a slice and then the rest of the sweep leave every
/// object white in `s1` -- unreachable from the roots when marking ended --
/// freed.  Nothing is allocated in between, so no address is new.
let cycle_frees_dead (minor: minor_state) (h_init: heap) (roots: Seq.seq obj_addr)
                     (s1: heap) (fp1: U64.t) (s2: heap) (fp2: U64.t) (ph2: Ph.gc_phase)
                     (s3: heap) (fp3: U64.t)
  : Lemma (requires GI.phase_shape minor s1 fp1 (Ph.Sweeping zero_addr) /\
                    Corr.mark_post h_init s1 roots fp1 /\
                    (s2, fp2, ph2) == SL.phase_slice s1 fp1 (Ph.Sweeping zero_addr) 64 /\
                    (s3, fp3, Ph.Idle) == SL.phase_slice s2 fp2 ph2 (pow2 64 - 1))
          (ensures cycle_frees_dead_post h_init roots s1 s3)
  = GI.phase_shape_sweeping minor s1 fp1 zero_addr;
    Corr.mark_post_elim_no_grey h_init s1 roots fp1;
    SPC.survivor_or_new_start s1;
    SPC.phase_account_slice s1 SPC.nothing_new s1 fp1 (Ph.Sweeping zero_addr) 64;
    SPC.phase_account_slice s1 SPC.nothing_new s2 fp2 ph2 (pow2 64 - 1);
    SPC.phase_account_idle s1 SPC.nothing_new s3 fp3;
    if FStar.IndefiniteDescription.strong_excluded_middle (SPC.roots_in_graph h_init roots) then
      FStar.Classical.forall_intro (FStar.Classical.move_requires
        (SPC.dead_at_mark_white h_init s1 roots fp1))

fn incremental_cycle_spot
  (gh: gen_heap_t)
  (roots: array U64.t) (nroots: SZ.t)
  (fwd_arr: array U64.t)
  (queue: larray U64.t GC.Gen.ForwardingArray.queue_size)
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
                 Seq.length 'farr == GC.Gen.ForwardingArray.fwd_array_size /\
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
  assert (pure (ok ==> ph1 == Ph.Sweeping zero_addr));
  unfold (gc_state gh d1 b1 s1 fp1 ph1);
  fold (gc_state gh d1 b1 s1 fp1 ph1);
  let fin = sweep_slice gh 64UL;
  with s2 fp2 ph2. assert (gc_state gh d1 b1 s2 fp2 ph2);
  assert (pure ((s2, fp2, ph2) == SL.phase_slice s1 fp1 ph1 64));
  finish_sweep gh;
  with s3 fp3. assert (gc_state gh d1 b1 s3 fp3 Ph.Idle);
  // on success, everything marking left dead is freed by the end of the sweep
  let prepared = Ghost.hide (gen_gc_prepared_state ({ data = 'd; bump = 'b } <: minor_state)
                               's 'fp 'rs 'st (stack_capacity st));
  if ok {
    cycle_frees_dead ({ data = d1; bump = b1 } <: minor_state) (fst prepared) (snd prepared)
      s1 fp1 s2 fp2 ph2 s3 fp3;
    assert (pure (cycle_frees_dead_post (fst prepared) (snd prepared) s1 s3))
  }
}
