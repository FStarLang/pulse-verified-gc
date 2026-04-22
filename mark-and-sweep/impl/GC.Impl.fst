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
open GC.Impl.FusedSweepCoalesce
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
module Defs = GC.Spec.SweepCoalesce.Defs
module SpecSweepCoalesce = GC.Spec.SweepCoalesce


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

/// Bridge lemma: call full_gc_correctness_through_coalesce from bundled precondition
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10 --split_queries no"
let gc_correctness_bridge (s: GC.Spec.Base.heap) (st: Seq.seq GC.Spec.Base.obj_addr) (fp: U64.t)
  : Lemma (requires gc_precondition s st fp)
          (ensures SpecGCPost.full_gc_correctness s
                     (fst (SpecCoalesce.coalesce (fst (SpecSweep.sweep (SpecMark.mark s st) fp)))) st)
  = SpecMarkInv.mark_inv_elim_wfh s st;
    SpecMarkInv.mark_inv_elim_sp s st;
    SpecGCPost.full_gc_correctness_through_coalesce s st st fp
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
/// - full_gc_correctness on the coalesced output
/// - Coalesced heap matches spec: (s2, final_fp) == coalesce(fst(sweep(mark s st, fp)))
#push-options "--z3rlimit 100"
fn collect (heap: heap_t) (st: gray_stack) (fp: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (gc_precondition 's 'st fp /\ stack_capacity st >= heap_size)
  returns final_fp: U64.t
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecGCPost.gc_postcondition s2 /\ Seq.length st2 == 0 /\
                (s2, final_fp) == SpecCoalesce.coalesce (fst (SpecSweep.sweep (SpecMark.mark 's 'st) fp)) /\
                SpecGCPost.full_gc_correctness 's s2 'st)
{
  // Establish initial-state facts needed later
  SpecMarkInv.mark_inv_elim_wfh 's 'st;
  SpecMarkInv.mark_inv_elim_sp 's 'st;
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
  
  // Fused sweep+coalesce: single pass that whitens survivors and merges free blocks
  let final_fp = fused_sweep_coalesce heap;
  
  // After fused: (s_fused, final_fp) == fused_sweep_coalesce s_mark
  with s_fused. assert (is_heap heap s_fused **
    pure ((s_fused, final_fp) == Defs.fused_sweep_coalesce s_mark));

  // Bridge: fused_sweep_coalesce == coalesce . fst . sweep
  SpecSweepCoalesce.fused_eq_sweep_coalesce s_mark fp;
  // Now: Defs.fused_sweep_coalesce s_mark == SpecCoalesce.coalesce (fst (SpecSweep.sweep s_mark fp))
  // Since s_mark == mark 's 'st:
  // (s_fused, final_fp) == SpecCoalesce.coalesce (fst (SpecSweep.sweep (mark 's 'st) fp))

  // Establish gc_postcondition on s_fused:
  //   - well_formed_heap s_fused
  //   - all objects white or blue in s_fused
  // These follow from coalesce_preserves_wf and coalesce_all_white_or_blue
  // applied to fst (sweep s_mark fp), since fused result == coalesce result.
  SpecGCPost.sweep_post_sweep_strong 's 'st fp;
  SpecGCPost.coalesce_precondition_bridge s_mark fp;
  SpecCoalesce.coalesce_preserves_wf (fst (SpecSweep.sweep s_mark fp));
  SpecCoalesce.coalesce_all_white_or_blue (fst (SpecSweep.sweep s_mark fp));
  SpecGCPost.gc_postcondition_intro s_fused;
  
  // Full GC correctness on coalesced output
  gc_correctness_bridge 's 'st fp;
  
  final_fp
}
#pop-options
