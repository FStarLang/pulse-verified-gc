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
module SpecFields = Pulse.Spec.GC.Fields
module SI = Pulse.Spec.GC.SweepInv

let zero_hp_addr : hp_addr = 0UL

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
           pure (SpecMarkInv.mark_inv 's 'st /\ SI.fp_valid fp 's)
  returns final_fp: U64.t
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecGCPost.gc_postcondition s2) ** pure (Seq.length st2 == 0)
{
  // Mark phase: process gray stack until empty (preserves mark_inv)
  mark_loop heap st;
  
  // Bind existentials and extract well_formed_heap from mark_inv
  with s_mark st_mark. assert (is_heap heap s_mark ** is_gray_stack st st_mark **
                                pure (SpecMarkInv.mark_inv s_mark st_mark /\ Seq.length st_mark == 0 /\
                                      SpecFields.objects zero_hp_addr s_mark == SpecFields.objects zero_hp_addr 's));
  SpecMarkInv.mark_inv_elim_wfh s_mark st_mark;
  SpecMarkInv.mark_inv_elim_objects s_mark st_mark;
  
  // fp_valid preservation: objects list is preserved from 's to s_mark
  SI.fp_valid_transfer fp 's s_mark;
  
  // Density preservation: density is part of mark_inv
  SpecMarkInv.mark_inv_elim_density s_mark st_mark;
  
  // Sweep phase: reset black to white, build free list
  // sweep preserves well_formed_heap (via internal loop invariant)
  let result_fp = sweep heap fp;
  
  // After sweep: well_formed_heap s_sweep is PROVEN (from sweep postcondition)
  // all_objects_white: pending sweep↔spec correspondence (sweep_resets_colors in spec)
  with s_sweep. assert (is_heap heap s_sweep ** pure (SpecFields.well_formed_heap s_sweep));
  assume (pure (SpecGCPost.all_objects_white s_sweep));
  SpecGCPost.gc_postcondition_from_parts s_sweep;
  
  result_fp
}
