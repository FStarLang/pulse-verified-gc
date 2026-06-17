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

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

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
module SpecAlloc = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module SI = GC.Spec.SweepInv
module SpecHeapModel = GC.Spec.HeapModel
module SpecHeapGraph = GC.Spec.HeapGraph
module SpecGraph = GC.Spec.Graph
module Defs = GC.Spec.SweepCoalesce.Defs
module SpecSweepCoalesce = GC.Spec.SweepCoalesce
module Allocator = GC.Impl.Allocator

/// ---------------------------------------------------------------------------
/// Public allocation wrappers
/// ---------------------------------------------------------------------------

fn init_heap (heap: heap_t)
  requires is_heap heap 's
  returns fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure ((s2, fp) == SpecAlloc.init_heap_spec 's)
{
  Allocator.init_heap heap
}

fn allocate (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap 's)
  returns res: (U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 **
    pure (let spec_res = SpecAlloc.alloc_spec 's fp (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fst res == spec_res.fp_out /\
          snd res == spec_res.obj_out)
{
  Allocator.allocate heap fp wosize
}

fn allocate_part1 (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap_part1 's /\
                 AllocLemmas.fl_valid 's fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 's fp (heap_size / U64.v mword))
  returns res: (U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 **
    pure (let spec_res = SpecAlloc.alloc_spec 's fp (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fst res == spec_res.fp_out /\
          snd res == spec_res.obj_out)
{
  Allocator.allocate_part1 heap fp wosize
}

fn init_major_chunk_raw (heap: heap_t)
                        (base: hp_addr)
                        (fp_out: obj_addr)
                        (wz: wosize)
                        (next_fp: U64.t)
  requires is_heap heap 's **
           pure (U64.v fp_out == U64.v base + U64.v mword)
  returns new_fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure (let hdr = makeHeader wz blue 0UL in
          s2 == GC.Spec.Heap.write_word
                  (GC.Spec.Heap.write_word 's base hdr) fp_out next_fp /\
          new_fp == fp_out)
{
  Allocator.init_major_chunk_raw heap base fp_out wz next_fp
}

fn major_preflight_required_head_wosize
  (demand_words: U64.t{U64.v demand_words < pow2 64 - 1})
  requires emp
  returns needed: U64.t
  ensures emp ** pure (needed == U64.add demand_words 1UL)
{
  Allocator.major_preflight_required_head_wosize demand_words
}

fn major_preflight_required_chunk_words
  (head_wosize: U64.t{U64.v head_wosize < pow2 64 - 1})
  requires emp
  returns words: U64.t
  ensures emp ** pure (words == U64.add head_wosize 1UL)
{
  Allocator.major_preflight_required_chunk_words head_wosize
}

fn major_preflight_head_ready
  (head_wosize required_head_wosize: U64.t)
  requires emp
  returns ready: bool
  ensures emp ** pure (ready <==> U64.v head_wosize >= U64.v required_head_wosize)
{
  U64.gte head_wosize required_head_wosize
}

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
#push-options "--z3rlimit 200 --split_queries always"
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
               SpecGCPost.major_gc_unreachable_final_blue 's s2 roots)
{
  // Mark phase: bounded-stack mark with overflow handling
  mark_loop_bounded heap st roots;
  
  // Bind existentials
  with s_mark st_mark. assert (is_heap heap s_mark ** is_gray_stack st st_mark);
  
  // Assemble mark_post from the mark invariants
  SpecMarkBoundedCorr.mark_post_from_bounded_mark 's s_mark roots fp;
  
  // fp_valid transfers from 's to s_mark since objects list is preserved
  SI.fp_valid_transfer fp 's s_mark;
  
  // No gray objects: bridge from SweepInv to Mark for fused_sweep_coalesce
  SpecMarkBoundedCorr.noGreyObjects_from_no_gray s_mark;
  
  // Fused sweep+coalesce: single pass that whitens survivors and merges free blocks
  let final_fp = fused_sweep_coalesce heap;
  
  // After fused: (s_fused, final_fp) == fused_sweep_coalesce s_mark
  with s_fused. assert (is_heap heap s_fused **
    pure ((s_fused, final_fp) == Defs.fused_sweep_coalesce s_mark));

  // Bridge: fused_sweep_coalesce == coalesce(fst(sweep ...))
  SpecSweepCoalesce.fused_eq_sweep_coalesce s_mark fp;

  // gc_postcondition and full_gc_correctness from generalized bridges
  // These only need mark_post, which we established above
  SpecGCPost.gc_postcondition_gen 's s_mark roots fp;
  SpecGCPost.full_gc_correctness_through_coalesce_gen 's s_mark roots fp;
  SpecGCPost.major_gc_live_subgraph_isomorphism_gen 's s_mark roots fp;
  SpecGCPost.major_gc_unreachable_final_blue_gen 's s_mark roots fp;
  
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
                SpecGCPost.major_gc_unreachable_final_blue 's s2 'st)
{
  collect_with_roots heap st 'st fp
}
#pop-options
