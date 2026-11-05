/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPhase.Stw - marking with no program in between: the
/// stop-the-world strengthening of the marking invariant
/// ---------------------------------------------------------------------------
///
/// A full collection (`GC.Gen.Impl.full_gc`) marks through the same slices as
/// the incremental collector, but runs no program between them.  The marking
/// invariant (`GC.Spec.MarkPhase.marking_inv`) then holds with something
/// stronger, as the sweep's `sweep_inv_stw` strengthens its incremental
/// invariant: from the heap `g0` marking started from (the roots darkened,
/// nothing black):
///
///   * **only colours change** (`colours_only_changed`): the walk, every
///     block's size, tag and fields, and the object graph are `g0`'s, the
///     heap is well formed, and no black object points at a white one (the
///     strong tri-colour invariant: with no program writing, a black object's
///     fields are the ones it had when it was scanned);
///   * **what is dark was reachable** (`dark_were_reachable`): every grey or
///     black object is reachable from the roots in `g0`;
///   * **what was darkened stays dark** (`darkened_stay_dark`): an object grey
///     in `g0` is grey or black.
///
/// Every move of a slice (`GC.Spec.MarkPhase.Slice.mark_move`) keeps it
/// (`marking_inv_stw_move`); when nothing is grey any more it is the mark
/// postcondition (`marking_inv_stw_done`, `GC.Spec.Correctness.mark_post`):
/// black is exactly reachable from the roots, which is where the
/// stop-the-world end-to-end theorems start (`gc_result_fused`).

module GC.Spec.MarkPhase.Stw

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Mark = GC.Spec.Mark
module MBC = GC.Spec.MarkBoundedCorrectness
module Corr = GC.Spec.Correctness
module HM = GC.Spec.HeapModel
module HG = GC.Spec.HeapGraph
module S = GC.Spec.MarkPhase.Slice

/// The heap differs from `g0` only in colours, and no black object points at
/// a white one.
let colours_only_changed (g0 g: heap) : prop = MBC.mark_color_inv g0 g

/// Every grey or black object is reachable from the roots in `g0`.
let dark_were_reachable (g0 g: heap) (roots: seq obj_addr) : prop =
  MBC.gray_black_reachable g0 g roots

/// Every object grey in `g0` is grey or black.
let darkened_stay_dark (g0 g: heap) : prop = MBC.gray_stays g0 g

/// **The stop-the-world strengthening of the marking invariant.**
let marking_inv_stw (g0 g: heap) (roots: seq obj_addr) : prop =
  colours_only_changed g0 g /\ dark_were_reachable g0 g roots /\ darkened_stay_dark g0 g

/// What marking starts from: the roots darkened (every grey object a root),
/// nothing black, the roots a set of vertices of the object graph.
let stw_start (g0: heap) (roots: seq obj_addr) : prop =
  well_formed_heap g0 /\
  Seq.length (objects zero_addr g0) > 0 /\
  heap_objects_dense g0 /\
  Mark.no_black_objects g0 /\
  Mark.root_props g0 roots /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g0) /\ (is_gray x g0 \/ is_black x g0) ==>
     Seq.mem x roots) /\
  (let graph = HM.create_graph g0 in
   let roots' = HG.coerce_to_vertex_list roots in
   GC.Spec.Graph.graph_wf graph /\ GC.Spec.Graph.is_vertex_set roots' /\
   GC.Spec.Graph.subset_vertices roots' graph.GC.Spec.Graph.vertices)

/// **Start.**
val marking_inv_stw_start (g0: heap) (roots: seq obj_addr)
  : Lemma (requires stw_start g0 roots) (ensures marking_inv_stw g0 g0 roots)

/// **A move keeps it** ...
val marking_inv_stw_move (g0 g g': heap) (roots: seq obj_addr)
  : Lemma (requires marking_inv_stw g0 g roots /\ S.mark_move g g')
          (ensures marking_inv_stw g0 g' roots)

/// ... and so does any number of moves.
val marking_inv_stw_steps (g0 g g': heap) (roots: seq obj_addr)
  : Lemma (requires marking_inv_stw g0 g roots /\ S.mark_steps g g')
          (ensures marking_inv_stw g0 g' roots)

/// **End.**  With nothing grey, the heap is the marked heap of `g0`
/// (`mark_post`: black exactly when reachable from the roots, the objects
/// and their fields unchanged), from which the stop-the-world theorems
/// follow.
val marking_inv_stw_done (g0 g: heap) (roots: seq obj_addr) (fp: U64.t)
  : Lemma (requires stw_start g0 roots /\ marking_inv_stw g0 g roots /\ Mark.noGreyObjects g /\
                    GC.Spec.FreeList.fp_in_heap fp g0)
          (ensures Corr.mark_post g0 g roots fp)
