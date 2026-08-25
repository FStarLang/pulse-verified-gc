(*
   Pulse GC - Top-Level Module Interface

   Exports the collect entry point combining mark, sweep, and coalesce phases.
*)

module GC.Impl

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Stack
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SpecGCPost = GC.Spec.Correctness
module SpecMark = GC.Spec.Mark
module SpecMarkInv = GC.Spec.MarkInv
module SpecMarkBoundedInv = GC.Spec.MarkBoundedInv
module SpecSweep = GC.Spec.Sweep
module SpecCoalesce = GC.Spec.Coalesce
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object
module SI = GC.Spec.SweepInv
module SpecHeapModel = GC.Spec.HeapModel
module SpecHeapGraph = GC.Spec.HeapGraph
module SpecGraph = GC.Spec.Graph

/// Precondition bundle for full GC correctness (bounded mark variant).
/// The concrete gray stack may be a bounded worklist approximation of the
/// ghost root set used for correctness.
let gc_precondition_with_roots
    (s: GC.Spec.Base.heap) (st roots: Seq.seq GC.Spec.Base.obj_addr)
    (fp: U64.t) (cap: nat) : prop =
  SpecMarkBoundedInv.bounded_mark_inv s st cap /\
  SI.fp_valid fp s /\
  SpecMark.root_props s roots /\
  SpecSweep.fp_in_heap fp s /\
  SpecMark.no_black_objects s /\
  SpecMark.no_pointer_to_blue s /\
  SpecFields.no_scan_invariant s /\
  (forall (x: GC.Spec.Base.obj_addr). Seq.mem x (SpecFields.objects GC.Spec.Base.zero_addr s) /\
    (GC.Spec.Object.is_gray x s \/ GC.Spec.Object.is_black x s) ==> Seq.mem x roots) /\
  (let graph = SpecHeapModel.create_graph s in
   let roots' = SpecHeapGraph.coerce_to_vertex_list roots in
   SpecGraph.graph_wf graph /\ SpecGraph.is_vertex_set roots' /\
   SpecGraph.subset_vertices roots' graph.vertices)

let gc_precondition (s: GC.Spec.Base.heap) (st: Seq.seq GC.Spec.Base.obj_addr)
                    (fp: U64.t) (cap: nat) : prop =
  gc_precondition_with_roots s st st fp cap

/// Main garbage collection entry point with an explicit ghost root set.
fn collect_with_roots
    (heap: heap_t) (st: gray_stack)
    (roots: Ghost.erased (Seq.seq GC.Spec.Base.obj_addr)) (fp: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (gc_precondition_with_roots 's 'st roots fp (stack_capacity st))
  returns final_fp: U64.t
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecGCPost.gc_postcondition s2 /\
                SpecFields.blue_fields_non_infix s2 /\
                SpecGCPost.full_gc_correctness 's s2 roots /\
                SpecGCPost.major_gc_live_subgraph_isomorphism 's s2 roots /\
                SpecGCPost.major_gc_unreachable_final_blue 's s2 roots)

/// Main garbage collection entry point
/// 1. Mark: bounded-stack mark with overflow handling
/// 2. Sweep: reset black objects to white, build free list
/// 3. Coalesce: merge adjacent free blocks
fn collect (heap: heap_t) (st: gray_stack) (fp: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (gc_precondition 's 'st fp (stack_capacity st))
  returns final_fp: U64.t
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecGCPost.gc_postcondition s2 /\
                SpecFields.blue_fields_non_infix s2 /\
                SpecGCPost.full_gc_correctness 's s2 'st /\
                SpecGCPost.major_gc_live_subgraph_isomorphism 's s2 'st /\
                SpecGCPost.major_gc_unreachable_final_blue 's s2 'st)
