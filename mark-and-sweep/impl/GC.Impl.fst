(*
   Pulse GC - Top-Level Module
   
   This module provides the top-level garbage collection entry point,
   combining mark, sweep, and coalesce phases. The postcondition connects to the
   end-to-end correctness theorem from GC.Spec.Correctness via
   the opaque gc_postcondition predicate.
   
   Based on: Proofs/Impl.GC_closure_infix_ver3.fst
*)

module GC.Impl

#lang-pulse

#set-options "--fuel 0 --ifuel 0 --z3rlimit 12"

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Stack
open GC.Impl.MarkBounded
open GC.Impl.FusedSweepCoalesce
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SpecGCPost = GC.Spec.Correctness
module SpecMark = GC.Spec.Mark
module SpecMarkInv = GC.Spec.MarkInv
module SpecMarkBoundedInv = GC.Spec.MarkBoundedInv
module SpecMarkBoundedCorr = GC.Spec.MarkBoundedCorrectness
module SpecSweep = GC.Spec.Sweep
module SpecCoalesce = GC.Spec.Coalesce
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object
module SI = GC.Spec.SweepInv
module SpecHeapModel = GC.Spec.HeapModel
module SpecHeapGraph = GC.Spec.HeapGraph
module SpecGraph = GC.Spec.Graph
module FS = GC.Spec.FusedSweep


/// ---------------------------------------------------------------------------
/// Full GC
/// ---------------------------------------------------------------------------

/// Main garbage collection entry point
/// 1. Mark: bounded-stack mark with overflow handling
/// 2. Fused sweep: single-pass scan whitening survivors and merging free blocks
///
/// Precondition: bounded_mark_inv + root/graph conditions for full correctness
/// Postcondition:
/// - gc_postcondition: well_formed_heap preserved, all objects white or blue
/// - full_gc_correctness: reachable objects survive with preserved data
#push-options "--z3rlimit 50"
fn collect_with_roots
    (heap: heap_t) (st: gray_stack)
    (roots: Ghost.erased (Seq.seq GC.Spec.Base.obj_addr)) (fp: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (gc_precondition_with_roots 's 'st roots fp (stack_capacity st))
  returns final_fp: U64.t
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecGCPost.gc_postcondition s2 /\
               SpecGCPost.full_gc_correctness 's s2 roots /\
               SpecGCPost.major_gc_live_subgraph_isomorphism 's s2 roots /\
               SpecGCPost.major_gc_unreachable_final_blue 's s2 roots /\
               SpecGCPost.gc_coalesce_source 's s2 roots fp final_fp)
{
  // Mark phase: bounded-stack mark with overflow handling
  mark_loop_bounded heap st roots;
  
  // Bind existentials
  with s_mark st_mark. assert (is_heap heap s_mark ** is_gray_stack st st_mark);
  
  // Assemble mark_post from the mark invariants
  SpecMarkBoundedCorr.mark_post_from_bounded_mark 's s_mark roots fp;
  
  // fp_valid transfers from 's to s_mark since objects list is preserved
  SI.fp_valid_transfer fp 's s_mark;
  
  // The sweep starts from the marked heap and the free list the last cycle left
  SpecGCPost.mark_post_sweep_pre 's s_mark roots fp;

  // Fused sweep: one pass that whitens survivors, frees garbage, merges free
  // blocks and keeps the free list exact and ascending
  let final_fp = fused_sweep_coalesce heap fp;
  with s_fused. assert (is_heap heap s_fused **
    pure ((s_fused, final_fp) == FS.fused_sweep_coalesce s_mark fp));

  // The collector's theorems at that heap
  SpecGCPost.gc_result_fused 's s_mark roots fp;
  SpecGCPost.gc_coalesce_source_intro 's s_mark roots fp s_fused final_fp;

  final_fp
}

fn collect (heap: heap_t) (st: gray_stack) (fp: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st **
            pure (gc_precondition 's 'st fp (stack_capacity st))
  returns final_fp: U64.t
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecGCPost.gc_postcondition s2 /\
                SpecGCPost.full_gc_correctness 's s2 'st /\
                SpecGCPost.major_gc_live_subgraph_isomorphism 's s2 'st /\
                SpecGCPost.major_gc_unreachable_final_blue 's s2 'st /\
                SpecGCPost.gc_coalesce_source 's s2 'st fp final_fp)
{
  collect_with_roots heap st 'st fp
}
#pop-options
