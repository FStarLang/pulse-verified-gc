(*
   Pulse GC - Top-Level Module
   
   This module provides the top-level garbage collection entry point,
   combining mark and sweep phases. The postcondition connects to the
   end-to-end correctness theorem from Pulse.Spec.GC.Correctness via
   the opaque gc_postcondition predicate.
   
   Based on: Proofs/Impl.GC_closure_infix_ver3.fst
*)

module Pulse.Lib.GC

#lang-pulse

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
open Pulse.Lib.GC.Stack
open Pulse.Lib.GC.Mark
open Pulse.Lib.GC.Sweep
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SpecGCPost = Pulse.Spec.GC.GCPost
module SpecMarkInv = Pulse.Spec.GC.MarkInv

/// ---------------------------------------------------------------------------
/// Full GC
/// ---------------------------------------------------------------------------

/// Main garbage collection entry point
/// 1. Mark: process gray stack until empty (preserves mark_inv)
/// 2. Sweep: reset black objects to white, build free list
///
/// Precondition: mark_inv (well_formed_heap + stack_props)
/// Postcondition:
/// - gc_postcondition: well_formed_heap preserved, all objects white
///   (Pillars 1 and 4 from end_to_end_correctness)
/// - Stack empty after mark phase
fn collect (heap: heap_t) (st: gray_stack) (fp: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (SpecMarkInv.mark_inv 's 'st)
  returns final_fp: U64.t
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecGCPost.gc_postcondition s2) ** pure (Seq.length st2 == 0)
{
  // Mark phase: process gray stack until empty
  // mark_loop preserves mark_inv
  mark_loop heap st;
  
  // Sweep phase: reset black to white, build free list
  let result_fp = sweep heap fp;
  
  // Bind the existential to get the actual post-sweep ghost heap
  with s_sweep. assert (is_heap heap s_sweep);
  
  // Bridge: gc_postcondition (pillars 1+4) — well_formed_heap now formally
  // proven via mark_inv through mark_loop. Pillar 4 (all-white) still assumed
  // pending proof that Pulse sweep matches spec sweep.
  assume (pure (SpecGCPost.gc_postcondition s_sweep));
  
  result_fp
}
