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
module Defs = GC.Spec.SweepCoalesce.Defs
module SpecSweepCoalesce = GC.Spec.SweepCoalesce
module SC = GC.Spec.SizeClass
module FLs = GC.Spec.FreeLists
module CL = GC.Spec.CollectLists
module SCL = GC.Spec.SweepCoalesce.Lists
module HeapAgree = GC.Spec.HeapAgree
module OT = GC.Spec.ObjectTable
module TS = GC.Spec.ObjectTable.Sweep


/// ---------------------------------------------------------------------------
/// Full GC
/// ---------------------------------------------------------------------------

/// Main garbage collection entry point
/// 1. Mark: bounded-stack mark with overflow handling
/// 2. Fused sweep+coalesce: single-pass scan whitening survivors and merging free blocks
///
/// Precondition: bounded_mark_inv + root/graph conditions for full correctness
/// Postcondition:
/// - gc_postcondition: well_formed_heap preserved, all objects white or blue
/// - full_gc_correctness: reachable objects survive with preserved data
///
/// `ov = false` additionally promises that every gray object is on the stack,
/// which lets the mark phase skip its heap rescan when no child is dropped
/// (`mark_loop_bounded_flagged`).
#push-options "--z3rlimit 50"
fn collect_core
    (heap: heap_t) (st: gray_stack)
    (roots: Ghost.erased (Seq.seq GC.Spec.Base.obj_addr)) (heads: array U64.t)
    (tbl: array U64.t) (ov: bool)
  requires is_heap heap 's ** is_gray_stack st 'st ** pts_to heads 'fls ** pts_to tbl 't **
           pure (gc_precondition_with_roots 's 'st roots (stack_capacity st) /\
                 Seq.length 'fls == SC.n_lists /\
                 Seq.length 't == OT.n_windows /\
                 (not ov ==> SpecMark.gray_objects_on_stack 's 'st))
  ensures exists* s2 st2 fls2 t2. is_heap heap s2 ** is_gray_stack st st2 **
          pts_to heads fls2 ** pts_to tbl t2 **
          pure (SpecGCPost.gc_postcondition s2 /\
               SpecGCPost.full_gc_correctness 's s2 roots /\
               SpecGCPost.major_gc_live_subgraph_isomorphism 's s2 roots /\
               SpecGCPost.major_gc_unreachable_final_blue 's s2 roots /\
               CL.gc_coalesce_source_lists 's s2 roots fls2 /\
               OT.table_ok s2 t2)
{
  // The sweep rebuilds every list, so the reference sweep starts empty.
  let fp = 0UL;
  SI.fp_valid_not_pointer fp 's;
  // Mark phase: bounded-stack mark with overflow handling
  mark_loop_bounded_flagged heap st roots ov;
  
  // Bind existentials
  with s_mark st_mark. assert (is_heap heap s_mark ** is_gray_stack st st_mark);
  
  // Assemble mark_post from the mark invariants
  SpecMarkBoundedCorr.mark_post_from_bounded_mark 's s_mark roots fp;
  
  // fp_valid transfers from 's to s_mark since objects list is preserved
  SI.fp_valid_transfer fp 's s_mark;
  
  // No gray objects: bridge from SweepInv to Mark for fused_sweep_coalesce
  SpecMarkBoundedCorr.noGreyObjects_from_no_gray s_mark;
  
  // Fused sweep+coalesce: single pass that whitens survivors, merges free
  // blocks and pushes each on the list of its size class
  // ... and rebuilds the object-start table of the heap it leaves
  fused_sweep_coalesce heap heads tbl;

  with s_fused fls2 t2. assert (is_heap heap s_fused ** pts_to heads fls2 ** pts_to tbl t2 **
    pure ((s_fused, fls2) == SCL.fused_sweep_coalesce_lists s_mark /\
          OT.table_matches s_fused t2));

  // The lists, and the heap modulo free blocks' bodies and links, are the
  // coalescer's: the theorems about coalesce(sweep ...) carry over.
  CL.gc_coalesce_source_lists_intro 's s_mark roots s_fused fls2;
  assert (pure (SpecGCPost.mark_post 's s_mark roots fp));
  assert (pure (HeapAgree.heaps_agree_mod_free_links s_fused
    (fst (SpecCoalesce.coalesce (fst (SpecSweep.sweep s_mark fp))))));
  SpecGCPost.gc_result_agree_links 's s_mark roots fp s_fused;
  assert (pure (SpecGCPost.gc_postcondition s_fused));
  assert (pure (SpecGCPost.full_gc_correctness 's s_fused roots));
  assert (pure (SpecGCPost.major_gc_live_subgraph_isomorphism 's s_fused roots));
  assert (pure (SpecGCPost.major_gc_unreachable_final_blue 's s_fused roots));
  assert (pure (CL.gc_coalesce_source_lists 's s_fused roots fls2));
  assert (pure (OT.table_matches s_fused t2));
  TS.collect_table_ok 's s_mark roots s_fused t2;
  assert (pure (OT.table_ok s_fused t2))
}

fn collect_with_roots
    (heap: heap_t) (st: gray_stack)
    (roots: Ghost.erased (Seq.seq GC.Spec.Base.obj_addr)) (heads: array U64.t)
    (tbl: array U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st ** pts_to heads 'fls ** pts_to tbl 't **
           pure (gc_precondition_with_roots 's 'st roots (stack_capacity st) /\
                 Seq.length 'fls == SC.n_lists /\
                 Seq.length 't == OT.n_windows)
  ensures exists* s2 st2 fls2 t2. is_heap heap s2 ** is_gray_stack st st2 **
          pts_to heads fls2 ** pts_to tbl t2 **
          pure (SpecGCPost.gc_postcondition s2 /\
               SpecGCPost.full_gc_correctness 's s2 roots /\
               SpecGCPost.major_gc_live_subgraph_isomorphism 's s2 roots /\
               SpecGCPost.major_gc_unreachable_final_blue 's s2 roots /\
               CL.gc_coalesce_source_lists 's s2 roots fls2 /\
               OT.table_ok s2 t2)
{
  // General roots: nothing says the grays are on the stack, so rescan.
  collect_core heap st roots heads tbl true
}

/// With the stack as the root set, "gray or black ==> root" says every gray
/// object is on the stack, so the mark phase may skip its rescan.
fn collect (heap: heap_t) (st: gray_stack) (heads: array U64.t) (tbl: array U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st ** pts_to heads 'fls ** pts_to tbl 't **
            pure (gc_precondition 's 'st (stack_capacity st) /\
                  Seq.length 'fls == SC.n_lists /\
                  Seq.length 't == OT.n_windows)
  ensures exists* s2 st2 fls2 t2. is_heap heap s2 ** is_gray_stack st st2 **
          pts_to heads fls2 ** pts_to tbl t2 **
          pure (SpecGCPost.gc_postcondition s2 /\
                SpecGCPost.full_gc_correctness 's s2 'st /\
                SpecGCPost.major_gc_live_subgraph_isomorphism 's s2 'st /\
                SpecGCPost.major_gc_unreachable_final_blue 's s2 'st /\
                CL.gc_coalesce_source_lists 's s2 'st fls2 /\
                OT.table_ok s2 t2)
{
  GC.Spec.MarkBoundedNoOverflow.gray_on_stack_of_roots_eq_stack 's 'st;
  collect_core heap st 'st heads tbl false
}
#pop-options
