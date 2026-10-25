/// ---------------------------------------------------------------------------
/// GC.Impl.Correct - End-to-end correctness of the collector, in two parts
/// ---------------------------------------------------------------------------
///
/// `gc_correct`: the heap `s2` that `GC.Impl.collect_with_roots` returns is
///
///   - safe:   nothing reachable is lost (`gc_safe`), and
///   - live:   everything unreachable is reclaimed and reusable (`gc_live`).
///
/// Every clause is stated of `s2` itself, the heap the fused sweep+coalesce
/// pass leaves.  The collector's postcondition relates `s2` to the spec heap
/// `coalesce (sweep h_mark fp)` only up to `heaps_agree_mod_free` (equal
/// headers, live fields and free links; free-block bodies not compared), so
/// the coalescing theorems are carried across that relation.
///
/// Stage 1: definitions and statements only.  The proofs are admitted.  See
/// docs/gc-correct.md for each clause in plain words, which existing lemma it
/// rests on, and the vacuity checks at the end of this file.

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
module SpecSweep = GC.Spec.Sweep
module SpecCoalesce = GC.Spec.Coalesce
module HA = GC.Spec.HeapAgree
module CC = GC.Spec.Coalesce.Correct
module FL = GC.Spec.FreeList
module Part = GC.Spec.Partition
module WE = GC.Spec.WalkEnd
module IH = GC.Impl.Heap
module IS = GC.Impl.Stack
module Complete = GC.Spec.Coalesce.Complete
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
  Corr.mark_post h_init h_mark roots fp /\
  (let r = SpecCoalesce.coalesce (fst (SpecSweep.sweep h_mark fp)) in
   HA.heaps_agree_mod_free s2 (fst r) /\ final_fp == snd r)

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
/// a field: `coalesce_exact` on the swept heap, carried to `s2`.
let s2_fl_exact
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) (h_mark: heap)
  : Lemma
    (requires source_at h_init s2 roots fp final_fp h_mark)
    (ensures FL.fl_exact s2 final_fp)
  = let hs = fst (SpecSweep.sweep h_mark fp) in
    Corr.sweep_post_sweep_strong_gen h_init h_mark roots fp;
    Complete.coalesce_exact hs;
    HA.agree_fl_exact s2 (fst (SpecCoalesce.coalesce hs)) final_fp

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
    CC.in_extent h_init x p ==>
    CC.blue_covered s2 p

/// (b) Every free block of `s2` with at least one field is on the free list
///     from `final_fp`.  A wosize-0 block (a fragment) cannot hold a link and
///     is excepted.  This is `GC.Spec.FreeList.fl_complete`.
let free_blocks_listed (s2: heap) (final_fp: U64.t) : prop =
  FL.fl_complete s2 final_fp

/// What `GC.Spec.Coalesce.Correct.coalesce_correct` says of coalescing `hs`
/// into `g'`, verbatim.
let coalesce_correct_post (hs g': heap) : prop =
  CC.total_free_space g' == CC.total_free_space hs /\
  (forall (p: nat). p < heap_size ==> (CC.blue_covered g' p <==> CC.blue_covered hs p)) /\
  (forall (x y: obj_addr).
     Seq.mem x (objects zero_addr g') /\ Seq.mem y (objects zero_addr g') /\
     is_blue x g' /\ is_blue y g' /\ CC.adjacent g' x y ==> False) /\
  (forall (x: obj_addr).
     Seq.mem x (objects zero_addr hs) /\ is_white x hs ==>
     Seq.mem x (objects zero_addr g') /\ is_white x g' /\
     wosize_of_object x g' == wosize_of_object x hs)

/// (c1) `s2` is, modulo free-block bodies, the coalescing of the swept heap
///      of a correct mark, and what `coalesce_correct` says of that coalescing
///      holds with `s2` as its output: no free space or coverage lost.
let coalescing_lossless
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) : prop =
  exists (h_mark: heap).
    Corr.mark_post h_init h_mark roots fp /\
    (let hs = fst (SpecSweep.sweep h_mark fp) in
     let r = SpecCoalesce.coalesce hs in
     HA.heaps_agree_mod_free s2 (fst r) /\
     final_fp == snd r /\
     coalesce_correct_post hs s2)

/// (c2) `s2` splits into live objects, the free list from `final_fp` and
///      fragments, with no fourth class: `heap_partition_strong` at `s2`, the
///      statement of `fused_partition`.
let heap_partitioned (s2: heap) (final_fp: U64.t) : prop =
  let objs = objects zero_addr s2 in
  U64.v zero_addr
  + (Part.white_whsize s2 objs
     + Part.onchain_whsize s2 final_fp objs
     + Part.frag_whsize s2 objs) * U64.v mword
  == WE.walk_end s2 zero_addr

let gc_live (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) : prop =
  unreachable_reclaimed h_init s2 roots /\
  free_blocks_listed s2 final_fp /\
  coalescing_lossless h_init s2 roots fp final_fp /\
  heap_partitioned s2 final_fp

/// ---------------------------------------------------------------------------
/// Sweep keeps every object's size
/// ---------------------------------------------------------------------------

/// Restated from `GC.Spec.SweepCoalesce.sweep_preserves_wosize_all`, which is
/// private there; same proof, from the public `GC.Spec.Sweep` lemmas.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec sweep_aux_preserves_wosize_any
  (g: heap) (objs: seq obj_addr) (fp: U64.t) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\
                    (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects zero_addr g)) /\
                    SpecSweep.fp_in_heap fp g /\
                    Seq.mem x (objects zero_addr g) /\
                    Seq.mem x objs /\
                    Graph.is_vertex_set (HeapGraph.coerce_to_vertex_list objs))
          (ensures wosize_of_object x g == wosize_of_object x (fst (SpecSweep.sweep_aux g objs fp)))
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let (g', fp') = SpecSweep.sweep_object g obj fp in
      Seq.lemma_index_is_nth objs 0;
      SpecSweep.sweep_object_preserves_objects g obj fp;
      SpecSweep.sweep_object_preserves_wf g obj fp;
      wf_objects_non_infix g obj;
      HeapGraph.coerce_tail_lemma objs;
      if obj = x then begin
        SpecSweep.sweep_object_preserves_self_wosize g x fp;
        HeapGraph.coerce_mem_lemma (Seq.tail objs) x;
        assert (~(Seq.mem x (Seq.tail objs)));
        (if is_white obj g then () else ());
        assert (SpecSweep.fp_in_heap fp' g');
        SpecSweep.sweep_aux_preserves_wosize_nonmember g' (Seq.tail objs) fp' x
      end else begin
        SpecSweep.sweep_object_preserves_other_header g obj fp x;
        Seq.lemma_mem_inversion objs;
        (if is_white obj g then () else ());
        assert (SpecSweep.fp_in_heap fp' g');
        sweep_aux_preserves_wosize_any g' (Seq.tail objs) fp' x
      end
    end
#pop-options

#push-options "--z3rlimit 12 --fuel 1 --ifuel 0"
let sweep_preserves_wosize_all
  (g: heap) (fp: U64.t) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\
                    Mark.noGreyObjects g /\
                    SpecSweep.fp_in_heap fp g /\
                    Seq.mem x (objects zero_addr g))
          (ensures wosize_of_object x g == wosize_of_object x (fst (SpecSweep.sweep g fp)))
  = GC.Spec.HeapModel.objects_is_vertex_set g;
    sweep_aux_preserves_wosize_any g (objects zero_addr g) fp x
#pop-options

/// ---------------------------------------------------------------------------
/// The liveness clauses, one lemma each
/// ---------------------------------------------------------------------------

let live_b
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) (h_mark: heap)
  : Lemma
    (requires source_at h_init s2 roots fp final_fp h_mark)
    (ensures free_blocks_listed s2 final_fp)
  = admit ()

let live_c2
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) (h_mark: heap)
  : Lemma
    (requires source_at h_init s2 roots fp final_fp h_mark /\ Corr.gc_postcondition s2)
    (ensures heap_partitioned s2 final_fp)
  = admit ()

let live_c1
  (h_init s2: heap) (roots: seq obj_addr) (fp final_fp: U64.t) (h_mark: heap)
  : Lemma
    (requires source_at h_init s2 roots fp final_fp h_mark)
    (ensures coalescing_lossless h_init s2 roots fp final_fp)
  = admit ()

let live_a
  (h_init s2: heap) (st roots: seq obj_addr) (fp final_fp: U64.t) (cap: nat) (h_mark: heap)
  : Lemma
    (requires Impl.gc_precondition_with_roots h_init st roots fp cap /\
              collect_post h_init s2 roots fp final_fp /\
              source_at h_init s2 roots fp final_fp h_mark)
    (ensures unreachable_reclaimed h_init s2 roots)
  = admit ()

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
    (ensures CC.blue_covered s2 (U64.v (hd_address x)))
  = assert (whsize h_init x >= 1);
    assert (CC.next_pos h_init x >= U64.v (hd_address x) + U64.v mword);
    assert (CC.in_extent h_init x (U64.v (hd_address x)))
#pop-options
