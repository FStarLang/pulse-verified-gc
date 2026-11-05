/// ---------------------------------------------------------------------------
/// GC.Impl.Correct - End-to-end correctness of the collector, in two parts
/// ---------------------------------------------------------------------------
///
/// `gc_correct`: the heap `s2` that `GC.Impl.collect_with_roots` returns is
///
///   - safe:   nothing reachable is lost (`gc_safe`), and
///   - live:   everything unreachable is reclaimed and reusable (`gc_live`).
///
/// Every clause is stated of `s2` itself, the heap the fused sweep leaves.
/// The collector's postcondition says `(s2, final_fp)` is exactly
/// `fused_sweep_coalesce h_mark fp` for a marked heap `h_mark` satisfying
/// `mark_post`, so the fused sweep's theorems (`GC.Spec.FusedSweep.Facts`,
/// `GC.Spec.FusedSweep.Lossless`) apply to it directly.
///
/// Fully proved, no admits.  See docs/gc-correct.md for each clause in plain
/// words, the lemmas it rests on, and the vacuity checks at the end of this
/// file.

module GC.Impl.Correct

#lang-pulse

open Pulse.Lib.Pervasives
open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Seq = FStar.Seq
module Impl = GC.Impl
module Corr = GC.Spec.Correctness
module FS = GC.Spec.FusedSweep
module FSF = GC.Spec.FusedSweep.Facts
module LS = GC.Spec.FusedSweep.Lossless
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module Part = GC.Spec.Partition
module W = GC.Spec.Walk
module IH = GC.Impl.Heap
module IS = GC.Impl.Stack
module HeapGraph = GC.Spec.HeapGraph
module Graph = GC.Spec.Graph
module Mark = GC.Spec.Mark
module IndDesc = FStar.IndefiniteDescription

/// ---------------------------------------------------------------------------
/// The collector's postcondition
/// ---------------------------------------------------------------------------

/// The pure part of `GC.Impl.collect_with_roots`'s `ensures`, word for word.
/// `collect_correct` below checks the match: it calls the real function and
/// discharges `gc_correct`'s hypothesis from what that call returns.
let collect_post
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) : prop =
  Corr.gc_postcondition s2 /\
  Corr.full_gc_correctness h_init s2 roots /\
  Corr.major_gc_live_subgraph_isomorphism h_init s2 roots /\
  Corr.major_gc_unreachable_final_blue h_init s2 roots /\
  Corr.gc_coalesce_source h_init s2 roots fp final_fp

/// ---------------------------------------------------------------------------
/// The marked heap behind `s2`
/// ---------------------------------------------------------------------------

/// `gc_coalesce_source`'s body, at a given witness.
let source_at
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) (h_mark: heap) : prop =
  FLA.fl_ascending h_init fp /\
  Corr.mark_post h_init h_mark roots fp /\
  (s2, final_fp) == FS.fused_sweep_coalesce h_mark fp

/// Name the witness of `gc_coalesce_source`, so each clause below can be
/// proved about one fixed marked heap.
let source_mark
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t)
  : Ghost heap
    (requires Corr.gc_coalesce_source h_init s2 roots fp final_fp)
    (ensures fun h_mark -> source_at h_init s2 roots fp final_fp h_mark)
  = IndDesc.indefinite_description_ghost heap
      (fun h_mark -> source_at h_init s2 roots fp final_fp h_mark)

/// The free list from `final_fp` is exactly the free blocks of `s2` that have
/// a field: `fused_exact`.
let s2_fl_exact
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) (h_mark: heap)
  : Lemma
    (requires source_at h_init s2 roots fp final_fp h_mark)
    (ensures FL.fl_exact s2 final_fp)
  = FSF.fused_exact h_init h_mark roots fp

/// ---------------------------------------------------------------------------
/// 1. Safety: nothing reachable is lost
/// ---------------------------------------------------------------------------

/// The last conjunct is `fl_sound`: every block on the free list from
/// `final_fp` is a free block of `s2`, so the allocator never hands out a
/// live object.
let gc_safe (h_init s2: heap) (roots: seq obj_addr) (final_fp: U64.t) : prop =
  well_formed_heap s2 /\
  Corr.full_gc_correctness h_init s2 roots /\
  Corr.major_gc_live_subgraph_isomorphism h_init s2 roots /\
  FL.fl_sound s2 final_fp

val gc_safe_of_post
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t)
  : Lemma
    (requires collect_post h_init s2 roots fp final_fp)
    (ensures gc_safe h_init s2 roots final_fp)

let gc_safe_of_post h_init s2 roots fp final_fp =
  Corr.gc_postcondition_elim s2;
  let h_mark = source_mark h_init s2 roots fp final_fp in
  s2_fl_exact h_init s2 roots fp final_fp h_mark

/// ---------------------------------------------------------------------------
/// 2. Liveness: everything unreachable is reclaimed and reusable
/// ---------------------------------------------------------------------------

/// (a) Every word of every object unreachable before the collection -- its
///     header and its fields -- lies inside a free (blue) block of `s2`.
let unreachable_reclaimed (h_init s2: heap) (roots: seq obj_addr) : prop =
  forall (x: obj_addr) (p: nat).
    Seq.mem x (objects zero_addr h_init) /\
    ~(Corr.heap_reachable h_init roots x) /\
    LS.in_extent h_init x p ==>
    LS.blue_covered s2 p

/// (b) Every free block of `s2` with at least one field is on the free list
///     from `final_fp`.  A wosize-0 block (a fragment) cannot hold a link and
///     is excepted.  This is `GC.Spec.FreeList.fl_complete`.
let free_blocks_listed (s2: heap) (final_fp: U64.t) : prop =
  FL.fl_complete s2 final_fp

/// (c1) `s2` is the fused sweep of the heap a correct mark left, and the sweep
///      lost nothing (`GC.Spec.FusedSweep.Lossless.sweep_lossless`): its free
///      space is the marked heap's dead space, a word is free exactly when it
///      was dead, no two free blocks touch, and every live object survives
///      white at its size.
let coalescing_lossless
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) : prop =
  exists (h_mark: heap).
    Corr.mark_post h_init h_mark roots fp /\
    (s2, final_fp) == FS.fused_sweep_coalesce h_mark fp /\
    LS.sweep_lossless h_mark s2

/// (c2) `s2` splits into live objects, the free list from `final_fp` and
///      fragments, with no fourth class: `heap_partition_strong` at `s2`, the
///      statement of `fused_partition`.
let heap_partitioned (s2: heap) (final_fp: U64.t) : prop =
  let objs = objects zero_addr s2 in
  U64.v zero_addr
  + (Part.white_whsize s2 objs
     + Part.onchain_whsize s2 final_fp objs
     + Part.frag_whsize s2 objs) * U64.v mword
  == W.walk_end s2 zero_addr

let gc_live (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) : prop =
  unreachable_reclaimed h_init s2 roots /\
  free_blocks_listed s2 final_fp /\
  coalescing_lossless h_init s2 roots fp final_fp /\
  heap_partitioned s2 final_fp

/// ---------------------------------------------------------------------------
/// The liveness clauses, one lemma each
/// ---------------------------------------------------------------------------

let live_b
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) (h_mark: heap)
  : Lemma
    (requires source_at h_init s2 roots fp final_fp h_mark)
    (ensures free_blocks_listed s2 final_fp)
  = s2_fl_exact h_init s2 roots fp final_fp h_mark

let live_c2
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) (h_mark: heap)
  : Lemma
    (requires source_at h_init s2 roots fp final_fp h_mark)
    (ensures heap_partitioned s2 final_fp)
  = FSF.fused_partition h_init h_mark roots fp

let live_c1
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) (h_mark: heap)
  : Lemma
    (requires source_at h_init s2 roots fp final_fp h_mark)
    (ensures coalescing_lossless h_init s2 roots fp final_fp)
  = Corr.mark_post_sweep_pre h_init h_mark roots fp;
    LS.fused_sweep_lossless h_mark fp

/// The graph-shape facts of the initial heap that `gc_precondition_with_roots`
/// carries; pillar 2 of `mark_post` is guarded by them.
let graph_pre (h_init: heap) (roots: seq obj_addr) : prop =
  let g = GC.Spec.HeapModel.create_graph h_init in
  let roots' = HeapGraph.coerce_to_vertex_list roots in
  Graph.graph_wf g /\ Graph.is_vertex_set roots' /\ Graph.subset_vertices roots' g.vertices

/// One word `p` of one object `x` unreachable in `h_init`.  `x` is not black
/// in the marked heap (pillar 2), and marking kept its size, so `p` lies in a
/// dead block of the marked heap; the fused sweep puts every such word in a
/// free block (`fused_dead_covered`).
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let live_a_word
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) (h_mark: heap)
  (x: obj_addr) (p: nat)
  : Lemma
    (requires source_at h_init s2 roots fp final_fp h_mark /\
              graph_pre h_init roots /\
              Seq.mem x (objects zero_addr h_init) /\
              ~(Corr.heap_reachable h_init roots x) /\
              LS.in_extent h_init x p)
    (ensures LS.blue_covered s2 p)
  = Corr.mark_post_elim_objects h_init h_mark roots fp;
    Corr.mark_post_elim_black_reachable h_init h_mark roots fp;
    Corr.mark_post_elim_wosize h_init h_mark roots fp;
    GC.Spec.HeapModel.graph_vertices_mem h_init x;
    assert (~(is_black x h_mark));
    assert (LS.in_extent h_mark x p);
    Corr.mark_post_sweep_pre h_init h_mark roots fp;
    LS.fused_dead_covered h_mark fp x p
#pop-options

let live_a
  (h_init s2: heap) (st roots: seq obj_addr) (fp final_fp: U64.t) (cap: nat) (h_mark: heap)
  : Lemma
    (requires Impl.gc_precondition_with_roots h_init st roots fp cap /\
              collect_post h_init s2 roots fp final_fp /\
              source_at h_init s2 roots fp final_fp h_mark)
    (ensures unreachable_reclaimed h_init s2 roots)
  = introduce forall (x: obj_addr) (p: nat).
      Seq.mem x (objects zero_addr h_init) /\
      ~(Corr.heap_reachable h_init roots x) /\
      LS.in_extent h_init x p ==>
      LS.blue_covered s2 p
    with introduce _ ==> _
    with live_a_word h_init s2 roots fp final_fp h_mark x p

/// ---------------------------------------------------------------------------
/// 3. The top-level theorem
/// ---------------------------------------------------------------------------

/// The collector's precondition is needed, not only its postcondition: clause
/// (a) speaks of reachability in the *initial* heap, and relating that to the
/// mark bits takes the graph well-formedness facts the precondition carries.
val gc_correct
  (h_init s2: heap) (st roots: seq obj_addr) (fp final_fp: U64.t) (cap: nat)
  : Lemma
    (requires Impl.gc_precondition_with_roots h_init st roots fp cap /\
              collect_post h_init s2 roots fp final_fp)
    (ensures gc_safe h_init s2 roots final_fp /\
             gc_live h_init s2 roots fp final_fp)

let gc_correct h_init s2 st roots fp final_fp cap =
  gc_safe_of_post h_init s2 roots fp final_fp;
  let h_mark = source_mark h_init s2 roots fp final_fp in
  live_a h_init s2 st roots fp final_fp cap h_mark;
  live_b h_init s2 roots fp final_fp h_mark;
  live_c1 h_init s2 roots fp final_fp h_mark;
  live_c2 h_init s2 roots fp final_fp h_mark

/// `gc_correct` at the collector itself: calls `collect_with_roots` and
/// returns its result.  Its body checks that `collect_post` is exactly what
/// `collect_with_roots` ensures.
fn collect_correct
    (heap: IH.heap_t) (st: IS.gray_stack)
    (roots: Ghost.erased (Seq.seq obj_addr)) (fp: U64.t)
  requires IH.is_heap heap 's ** IS.is_gray_stack st 'st **
           pure (Impl.gc_precondition_with_roots 's 'st roots fp (IS.stack_capacity st))
  returns final_fp: U64.t
  ensures exists* s2 st2. IH.is_heap heap s2 ** IS.is_gray_stack st st2 **
          pure (gc_safe 's s2 roots final_fp /\ gc_live 's s2 roots fp final_fp)
{
  let final_fp = Impl.collect_with_roots heap st roots fp;
  with s2 st2. assert (IH.is_heap heap s2 ** IS.is_gray_stack st st2);
  gc_correct 's s2 'st roots fp final_fp (IS.stack_capacity st);
  final_fp
}

/// `gc_correct` at `GC.Impl.collect`, the entry point the generational
/// collector (`GC.Gen.Impl.full_gc`) calls.  `collect` is `collect_with_roots`
/// with the gray stack as the root set, so its precondition is
/// `gc_precondition_with_roots 's 'st 'st` and its postcondition is
/// `collect_post` at roots `'st`: `gc_correct` applies unchanged.
fn collect_stack_correct
    (heap: IH.heap_t) (st: IS.gray_stack) (fp: U64.t)
  requires IH.is_heap heap 's ** IS.is_gray_stack st 'st **
           pure (Impl.gc_precondition 's 'st fp (IS.stack_capacity st))
  returns final_fp: U64.t
  ensures exists* s2 st2. IH.is_heap heap s2 ** IS.is_gray_stack st st2 **
          pure (gc_safe 's s2 'st final_fp /\ gc_live 's s2 'st fp final_fp)
{
  let final_fp = Impl.collect heap st fp;
  with s2 st2. assert (IH.is_heap heap s2 ** IS.is_gray_stack st st2);
  gc_correct 's s2 'st 'st fp final_fp (IS.stack_capacity st);
  final_fp
}

/// ---------------------------------------------------------------------------
/// Vacuity checks
/// ---------------------------------------------------------------------------
///
/// Checked on every build.  `expect_failure` makes the build fail if the
/// inner proof ever *succeeds*.

/// The hypotheses of `gc_correct` are not refutable by Z3: if they were
/// contradictory, `gc_correct` would hold of no heap at all.  The repo's
/// usual check (mark-and-sweep/NOTES.md, "Vacuity checking").
#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
[@@expect_failure [19]]
let gc_correct_hyps_not_false
  (h_init s2: heap) (st roots: seq obj_addr) (fp final_fp: U64.t) (cap: nat)
  : Lemma
    (requires Impl.gc_precondition_with_roots h_init st roots fp cap /\
              collect_post h_init s2 roots fp final_fp)
    (ensures False)
  = ()

/// Liveness does not follow from safety alone.  If it did, `gc_live` would
/// add nothing to `gc_safe`.
[@@expect_failure [19]]
let gc_live_not_from_safe
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t)
  : Lemma
    (requires gc_safe h_init s2 roots final_fp)
    (ensures gc_live h_init s2 roots fp final_fp)
  = ()
#pop-options

/// Clause (a) has a non-empty guard: an object's own header word is in its
/// extent, so (a) says something about every unreachable object rather than
/// holding because no `p` satisfies `in_extent`.  Proved.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let unreachable_reclaimed_header
  (h_init s2: heap) (roots: seq obj_addr) (x: obj_addr)
  : Lemma
    (requires unreachable_reclaimed h_init s2 roots /\
              Seq.mem x (objects zero_addr h_init) /\
              ~(Corr.heap_reachable h_init roots x))
    (ensures LS.blue_covered s2 (U64.v (hd_address x)))
  = assert (whsize h_init x >= 1);
    assert (LS.next_pos h_init x >= U64.v (hd_address x) + U64.v mword);
    assert (LS.in_extent h_init x (U64.v (hd_address x)))
#pop-options
