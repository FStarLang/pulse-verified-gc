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

/// Main garbage collection entry point
/// 1. Mark: process gray stack until empty
/// 2. Sweep: reset black objects to white, build free list
/// 3. Coalesce: merge adjacent free blocks
fn collect (heap: heap_t) (st: gray_stack) (fp: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (gc_precondition 's 'st fp /\ stack_capacity st >= heap_size)
  returns final_fp: U64.t
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecGCPost.gc_postcondition s2 /\ Seq.length st2 == 0 /\
                (s2, final_fp) == SpecCoalesce.coalesce (fst (SpecSweep.sweep (SpecMark.mark 's 'st) fp)) /\
                SpecGCPost.full_gc_correctness 's s2 'st)
