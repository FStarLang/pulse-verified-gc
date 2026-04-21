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
open GC.Impl.Mark
open GC.Impl.Sweep
open GC.Impl.Coalesce
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SpecGCPost = GC.Spec.Correctness
module SpecMark = GC.Spec.Mark
module SpecMarkInv = GC.Spec.MarkInv
module SpecSweep = GC.Spec.Sweep
module SpecCoalesce = GC.Spec.Coalesce
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object
module SI = GC.Spec.SweepInv
module SpecHeapModel = GC.Spec.HeapModel
module SpecHeapGraph = GC.Spec.HeapGraph
module SpecGraph = GC.Spec.Graph


/// Precondition bundle for full GC correctness
let gc_precondition (s: GC.Spec.Base.heap) (st: Seq.seq GC.Spec.Base.obj_addr) (fp: U64.t) : prop =
  SpecMarkInv.mark_inv s st /\ SI.fp_valid fp s /\
  SpecMark.root_props s st /\
  SpecSweep.fp_in_heap fp s /\
  SpecMark.no_black_objects s /\
  SpecMark.no_pointer_to_blue s /\
  (let graph = SpecHeapModel.create_graph s in
   let roots' = SpecHeapGraph.coerce_to_vertex_list st in
   SpecGraph.graph_wf graph /\ SpecGraph.is_vertex_set roots' /\
   SpecGraph.subset_vertices roots' graph.vertices)

/// Bridge lemma: call full_gc_correctness_from_end_to_end from bundled precondition
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10 --split_queries no"
let gc_correctness_bridge (s: GC.Spec.Base.heap) (st: Seq.seq GC.Spec.Base.obj_addr) (fp: U64.t)
  : Lemma (requires gc_precondition s st fp)
          (ensures SpecGCPost.full_gc_correctness s (fst (SpecSweep.sweep (SpecMark.mark s st) fp)) st)
  = SpecMarkInv.mark_inv_elim_wfh s st;
    SpecMarkInv.mark_inv_elim_sp s st;
    SpecGCPost.full_gc_correctness_from_end_to_end s st st fp
#pop-options


/// ---------------------------------------------------------------------------
/// Full GC
/// ---------------------------------------------------------------------------

/// Main garbage collection entry point
/// 1. Mark: process gray stack until empty (preserves mark_inv)
/// 2. Sweep: reset black objects to white, build free list
/// 3. Coalesce: merge adjacent free blocks into larger ones
///
/// Precondition: mark_inv + root/graph conditions for full correctness
/// The gray stack 'st doubles as the root set.
/// Postcondition:
/// - gc_postcondition: well_formed_heap preserved, all objects white or blue
/// - full_gc_correctness on the sweep output (before coalesce)
/// - Coalesced heap matches spec: (s2, final_fp) == coalesce(fst(sweep(mark s st, fp)))
#push-options "--z3rlimit 100"
fn collect (heap: heap_t) (st: gray_stack) (fp: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (gc_precondition 's 'st fp /\ stack_capacity st >= heap_size)
  returns final_fp: U64.t
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecGCPost.gc_postcondition s2 /\ Seq.length st2 == 0 /\
                (s2, final_fp) == SpecCoalesce.coalesce (fst (SpecSweep.sweep (SpecMark.mark 's 'st) fp)) /\
                SpecGCPost.full_gc_correctness 's (fst (SpecSweep.sweep (SpecMark.mark 's 'st) fp)) 'st)
{
  // Establish initial-state facts needed later for coalesce bridge
  // (mark_inv 's 'st will be consumed by mark_loop, so extract facts now)
  SpecMarkInv.mark_inv_elim_wfh 's 'st;
  SpecMarkInv.mark_inv_elim_sp 's 'st;
  // Frame fp_in_heap and no_black/no_pointer_to_blue through mark_loop
  assert (pure (SpecSweep.fp_in_heap fp 's));
  assert (pure (SpecMark.no_black_objects 's));
  assert (pure (SpecMark.no_pointer_to_blue 's));
  
  // Mark phase: process gray stack until empty (preserves mark_inv)
  mark_loop heap st;
  
  // Bind existentials and extract well_formed_heap from mark_inv
  with s_mark st_mark. assert (is_heap heap s_mark ** is_gray_stack st st_mark **
                                pure (SpecMarkInv.mark_inv s_mark st_mark /\ Seq.length st_mark == 0 /\
                                      SpecFields.objects zero_addr s_mark == SpecFields.objects zero_addr 's /\
                                      s_mark == SpecMark.mark 's 'st));
  SpecMarkInv.mark_inv_elim_wfh s_mark st_mark;
  SpecMarkInv.mark_inv_elim_objects s_mark st_mark;
  
  // fp_valid preservation: objects list is preserved from 's to s_mark
  SI.fp_valid_transfer fp 's s_mark;
  
  // Density preservation: density is part of mark_inv
  SpecMarkInv.mark_inv_elim_density s_mark st_mark;
  
  // No gray objects: from empty stack + mark_inv → no_gray_objects
  SpecMarkInv.mark_inv_no_gray s_mark st_mark;
  // Also establish noGreyObjects (Mark) for coalesce_precondition_bridge
  SpecMarkInv.mark_inv_noGreyObjects s_mark st_mark;
  
  // fp_in_heap transfers from 's to s_mark since objects list is preserved
  assert (pure (SpecSweep.fp_in_heap fp s_mark));
  
  // Sweep phase: reset black to white, build free list
  let sweep_fp = sweep heap fp;
  
  // After sweep: well_formed_heap AND all_objects_white_or_blue AND spec equality
  with s_sweep. assert (is_heap heap s_sweep **
    pure (SpecFields.well_formed_heap s_sweep /\
          (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr s_sweep) ==>
            (SpecObject.is_white x s_sweep \/ SpecObject.is_blue x s_sweep)) /\
          (s_sweep, sweep_fp) == SpecSweep.sweep s_mark fp));

  // --- Bridge to coalesce preconditions ---
  
  // 1. post_sweep_strong: initial-state facts already established before mark_loop
  SpecGCPost.sweep_post_sweep_strong 's 'st fp;
  
  // 2+3. objects nonempty + density: bridge from post-mark to post-sweep
  //       This calls sweep_preserves_objects and sweep_preserves_density internally,
  //       connecting noGreyObjects (Mark) with no_gray_objects (SweepInv) in pure F*.
  SpecGCPost.coalesce_precondition_bridge s_mark fp;

  // Coalesce phase: merge adjacent free blocks
  let final_fp = coalesce heap;
  
  // After coalesce: well_formed_heap AND all_objects_white_or_blue AND spec equality
  with s_coal. assert (is_heap heap s_coal **
    pure (SpecFields.well_formed_heap s_coal /\
          (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr s_coal) ==>
            (SpecObject.is_white x s_coal \/ SpecObject.is_blue x s_coal)) /\
          (s_coal, final_fp) == SpecCoalesce.coalesce s_sweep));

  // gc_postcondition on coalesced heap (wf + all white or blue)
  SpecGCPost.gc_postcondition_intro s_coal;
  
  // Full GC correctness on sweep output (before coalesce)
  gc_correctness_bridge 's 'st fp;
  
  final_fp
}
#pop-options
