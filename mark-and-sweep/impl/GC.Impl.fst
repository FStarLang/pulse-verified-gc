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
module SI = GC.Spec.SweepInv
module SpecHeapModel = GC.Spec.HeapModel
module SpecHeapGraph = GC.Spec.HeapGraph
module SpecGraph = GC.Spec.Graph
module Defs = GC.Spec.SweepCoalesce.Defs
module SpecSweepCoalesce = GC.Spec.SweepCoalesce


/// Precondition bundle for full GC correctness (bounded mark variant)
let gc_precondition (s: GC.Spec.Base.heap) (st: Seq.seq GC.Spec.Base.obj_addr)
                    (fp: U64.t) (cap: nat) : prop =
  SpecMarkBoundedInv.bounded_mark_inv s st cap /\
  SI.fp_valid fp s /\
  SpecMark.root_props s st /\
  SpecSweep.fp_in_heap fp s /\
  SpecMark.no_black_objects s /\
  SpecMark.no_pointer_to_blue s /\
  (forall (x: GC.Spec.Base.obj_addr). Seq.mem x (SpecFields.objects GC.Spec.Base.zero_addr s) /\
    (GC.Spec.Object.is_gray x s \/ GC.Spec.Object.is_black x s) ==> Seq.mem x st) /\
  (let graph = SpecHeapModel.create_graph s in
   let roots' = SpecHeapGraph.coerce_to_vertex_list st in
   SpecGraph.graph_wf graph /\ SpecGraph.is_vertex_set roots' /\
   SpecGraph.subset_vertices roots' graph.vertices)


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
fn collect (heap: heap_t) (st: gray_stack) (fp: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (gc_precondition 's 'st fp (stack_capacity st))
  returns final_fp: U64.t
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecGCPost.gc_postcondition s2 /\
                SpecGCPost.full_gc_correctness 's s2 'st)
{
  // Mark phase: bounded-stack mark with overflow handling
  mark_loop_bounded heap st 'st;
  
  // Bind existentials
  with s_mark st_mark. assert (is_heap heap s_mark ** is_gray_stack st st_mark);
  
  // Assemble mark_post from the mark invariants
  SpecMarkBoundedCorr.mark_post_from_bounded_mark 's s_mark 'st fp;
  
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
  SpecGCPost.gc_postcondition_gen 's s_mark 'st fp;
  SpecGCPost.full_gc_correctness_through_coalesce_gen 's s_mark 'st fp;
  
  final_fp
}
#pop-options
