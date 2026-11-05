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
module SC = GC.Spec.SizeClass
module FLs = GC.Spec.FreeLists
module CL = GC.Spec.CollectLists
module OT = GC.Spec.ObjectTable

/// Precondition bundle for full GC correctness (bounded mark variant).
/// The concrete gray stack may be a bounded worklist approximation of the
/// ghost root set used for correctness.
let gc_precondition_with_roots
    (s: GC.Spec.Base.heap) (st roots: Seq.seq GC.Spec.Base.obj_addr)
    (cap: nat) : prop =
  SpecMarkBoundedInv.bounded_mark_inv s st cap /\
  SpecMark.root_props s roots /\
  SpecMark.no_black_objects s /\
  SpecMark.no_pointer_to_blue s /\
  (forall (x: GC.Spec.Base.obj_addr). Seq.mem x (SpecFields.objects GC.Spec.Base.zero_addr s) /\
    (GC.Spec.Object.is_gray x s \/ GC.Spec.Object.is_black x s) ==> Seq.mem x roots) /\
  (let graph = SpecHeapModel.create_graph s in
   let roots' = SpecHeapGraph.coerce_to_vertex_list roots in
   SpecGraph.graph_wf graph /\ SpecGraph.is_vertex_set roots' /\
   SpecGraph.subset_vertices roots' graph.vertices)

let gc_precondition (s: GC.Spec.Base.heap) (st: Seq.seq GC.Spec.Base.obj_addr)
                    (cap: nat) : prop =
  gc_precondition_with_roots s st st cap

/// Main garbage collection entry point with an explicit ghost root set.
///
/// `heads` holds the free-list heads, one per size class.  Their incoming
/// contents are irrelevant -- the sweep rebuilds every list -- and on return
/// they are the lists `gc_coalesce_source_lists` describes.
///
/// `tbl` is the object-start table (GC.Spec.ObjectTable).  The sweep rebuilds
/// every entry too, so its incoming contents are irrelevant; on return it is
/// the table of `s2` (`OT.table_ok`).
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

/// Main garbage collection entry point
/// 1. Mark: bounded-stack mark with overflow handling
/// 2. Sweep: reset black objects to white, build free list
/// 3. Coalesce: merge adjacent free blocks
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
