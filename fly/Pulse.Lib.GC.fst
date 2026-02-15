(*
   Pulse GC - Top-Level Garbage Collector for Parallel GC

   The parallel GC algorithm (Dijkstra-style on-the-fly):

   collect():
     1. Enable write barriers (set gc_phase = Marking)
     2. For each thread T_i:
        a. Stop T_i
        b. mark_other_roots_blue(all stacks except T_i)
        c. scan_thread_roots(T_i.stack, gray_stack)
        d. mark_loop(gray_stack)
        e. reset_blue_to_white(other stacks)
        f. Resume T_i
     3. Stop the world
     4. sweep_all()
     5. Resume all
     6. Disable write barriers (set gc_phase = Idle)

   Key properties:
   - Black accumulates across thread passes
   - Blue is temporary per-thread, reset after each pass
   - After all threads: black = reachable, white = garbage
   - Write barriers active for running mutators during marking
*)

module Pulse.Lib.GC

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
open Pulse.Lib.GC.Stack
open Pulse.Lib.GC.RootScanning
open Pulse.Lib.GC.ConcurrentMark
open Pulse.Lib.GC.Sweep
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SpecFields = Pulse.Spec.GC.Fields
open Pulse.Spec.GC.ColorLemmas

/// ---------------------------------------------------------------------------
/// GC Phase State
/// ---------------------------------------------------------------------------

type gc_phase =
  | Phase_Idle
  | Phase_Marking
  | Phase_Sweeping

/// GC state: tracks phase and thread information
noeq
type gc_state = {
  phase: ref gc_phase;
  heap_len: (n:U64.t{U64.v n == heap_size});
}

/// ---------------------------------------------------------------------------
/// Ghost helpers
/// ---------------------------------------------------------------------------

ghost fn is_heap_length (h: heap_t)
  requires is_heap h 's
  ensures is_heap h 's ** pure (Seq.length 's == heap_size)
{
  unfold is_heap;
  fold (is_heap h 's)
}

/// All thread root sets are valid objects in the heap
let all_roots_valid (g: Pulse.Spec.GC.Base.heap) (all_roots: Seq.seq (Seq.seq obj_addr)) : prop =
  forall (t: nat). t < Seq.length all_roots ==>
    roots_valid g (Seq.index all_roots t)

/// all_roots_valid transfers via objects_preserved (equality of objects)
let all_roots_valid_preserved (g1 g2: Pulse.Spec.GC.Base.heap)
    (all_roots: Seq.seq (Seq.seq obj_addr))
  : Lemma (requires all_roots_valid g2 all_roots /\ objects_preserved g1 g2)
          (ensures all_roots_valid g1 all_roots)
  = let aux (t: nat{t < Seq.length all_roots})
      : Lemma (roots_valid g1 (Seq.index all_roots t))
      = objects_preserved_roots_valid g1 g2 (Seq.index all_roots t)
    in
    Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// Per-Thread Mark Pass
/// ---------------------------------------------------------------------------

/// Execute the mark pass for a single thread:
/// 1. Blue-mark other threads' roots
/// 2. Gray this thread's roots
/// 3. Run mark loop to completion
/// 4. Reset blue markings
fn mark_one_thread
  (heap: heap_t) (st: gray_stack)
  (thread_roots: Seq.seq obj_addr)
  (other_roots: Seq.seq obj_addr)
  (n_thread: SZ.t{SZ.v n_thread == Seq.length thread_roots})
  (n_other: SZ.t{SZ.v n_other == Seq.length other_roots})
  requires is_heap heap 's ** is_gray_stack st 'gs **
           pure (SpecFields.well_formed_heap 's /\
                 roots_valid 's thread_roots /\
                 roots_valid 's other_roots /\
                 stack_valid 's 'gs /\
                 contiguous_heap 's)
  ensures exists* s2 gs2. is_heap heap s2 ** is_gray_stack st gs2 **
           pure (SpecFields.well_formed_heap s2 /\
                 objects_preserved s2 's /\
                 stack_valid s2 gs2 /\
                 contiguous_heap s2)
{
  // Step 1: Mark other threads' roots as blue (temporary fence)
  mark_other_roots_blue heap other_roots n_other;

  // Step 2: Gray this thread's roots
  // After mark_other_roots_blue: objects_preserved, so roots_valid + stack_valid transfer
  with s_blue. assert (is_heap heap s_blue);
  objects_preserved_roots_valid s_blue 's thread_roots;
  stack_valid_preserved s_blue 's 'gs;
  scan_thread_roots heap st thread_roots n_thread;

  // Step 3: Run mark loop until gray stack is empty
  mark_loop heap st;

  // Step 4: Reset blue markings back to white
  // mark_loop exposes objects_preserved + stack_valid
  with s3 gs3. assert (is_heap heap s3 ** is_gray_stack st gs3);
  // s3 has: objects_preserved s3 's, stack_valid s3 gs3
  objects_preserved_roots_valid s3 's other_roots;
  reset_blue_to_white heap other_roots n_other;
  // Transfer stack_valid to new heap: objects_preserved s4 s3 + stack_valid s3 gs3
  with s4. assert (is_heap heap s4);
  stack_valid_preserved s4 s3 gs3;
  ()
}

/// ---------------------------------------------------------------------------
/// Full Collection
/// ---------------------------------------------------------------------------

/// Execute a full garbage collection cycle.
///
/// This is the top-level entry point called by the runtime.
/// In the actual runtime integration:
/// - Thread stopping/resuming is handled by the runtime
/// - Shadow stacks provide root sets
/// - Write barriers are toggled via gc_state.phase
///
/// For verification purposes, we take the roots as explicit parameters.
fn collect
  (gc: gc_state)
  (heap: heap_t) (st: gray_stack)
  (all_thread_roots: Seq.seq (Seq.seq obj_addr))
  (n_threads: SZ.t{SZ.v n_threads == Seq.length all_thread_roots})
  requires is_heap heap 's ** is_gray_stack st 'gs ** pts_to gc.phase 'p **
           pure (SpecFields.well_formed_heap 's /\
                 all_roots_valid 's all_thread_roots /\
                 Seq.length (SpecFields.objects 0UL 's) > 0 /\
                 stack_valid 's 'gs /\
                 contiguous_heap 's /\
                 (forall (i:nat). i < Seq.length all_thread_roots ==>
                   SZ.fits (Seq.length (Seq.index all_thread_roots i))))
  ensures exists* s2 gs2. is_heap heap s2 ** is_gray_stack st gs2 **
          pts_to gc.phase Phase_Idle **
          pure (SpecFields.well_formed_heap s2)
{
  // Phase 1: Enable write barriers
  gc.phase := Phase_Marking;

  // Phase 2: Mark each thread's roots
  let mut thread_idx = 0sz;
  while (SZ.lt !thread_idx n_threads)
    invariant exists* ti s_i gs_i.
      pts_to thread_idx ti **
      is_heap heap s_i **
      is_gray_stack st gs_i **
      pts_to gc.phase Phase_Marking **
      pure (SZ.v ti <= SZ.v n_threads) **
      pure (SpecFields.well_formed_heap s_i /\
            all_roots_valid s_i all_thread_roots /\
            Seq.length (SpecFields.objects 0UL s_i) > 0 /\
            stack_valid s_i gs_i /\
            objects_preserved s_i 's /\
            contiguous_heap s_i /\
            (forall (i:nat). i < Seq.length all_thread_roots ==>
              SZ.fits (Seq.length (Seq.index all_thread_roots i))))
  {
    let ti = !thread_idx;
    let thread_roots = Seq.index all_thread_roots (SZ.v ti);
    // In a real implementation, other_roots = union of all other stacks
    // For now, use empty seq as placeholder
    let other_roots = Seq.empty #obj_addr;
    let n_thread : SZ.t = SZ.uint_to_t (Seq.length thread_roots);
    let n_other = 0sz;
    mark_one_thread heap st thread_roots other_roots n_thread n_other;
    // mark_one_thread returns objects_preserved: transfer all_roots_valid + objects length
    with s_after gs_after. assert (is_heap heap s_after ** is_gray_stack st gs_after);
    all_roots_valid_preserved s_after 's all_thread_roots;
    thread_idx := SZ.add ti 1sz;
    ()
  };

  // Phase 3: Stop the world and sweep
  gc.phase := Phase_Sweeping;
  sweep_all heap gc.heap_len;

  // Phase 4: Done
  gc.phase := Phase_Idle;
  ()
}
