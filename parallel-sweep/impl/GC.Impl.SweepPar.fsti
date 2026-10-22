(*
   Pulse GC - Parallel sweep: pre-pass, merge, and a sequential driver
   (interface; the implementations and their proofs are in
   GC.Impl.SweepPar.fst, GC.Impl.SweepPar.Prepass.fst and
   GC.Impl.SweepPar.Merge.fst)

   The parallel sweep runs in three steps (docs/parallel-sweep-phase1.md, §8):

     1. prepass         choose the segment boundaries;
     2. sweep_segment   one call per segment, each owning only its range
                        (GC.Impl.SweepSegment); the OCaml runtime runs these
                        on its worker threads;
     3. merge           link the segments' free runs and lists, sequentially.

   sweep_par_seq runs the three steps in one thread, calling sweep_segment
   on each segment in order.  Its postcondition is the sequential pass's.

   Buffers are provided by the caller, with their capacity passed as a
   runtime SZ.t, as GC.Impl.Stack does.
*)

module GC.Impl.SweepPar

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.SweepSegment
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SP = GC.Spec.SweepPar
module Defs = GC.Spec.SweepCoalesce.Defs

/// ---------------------------------------------------------------------------
/// Boundaries in an array
/// ---------------------------------------------------------------------------

/// The first n entries of `s`, as the model's boundary list.
let bounds_list (s: Seq.seq U64.t) (n: nat{n <= Seq.length s}) : list nat =
  List.Tot.map U64.v (Seq.seq_to_list (Seq.slice s 0 n))

/// ---------------------------------------------------------------------------
/// 1. The pre-pass
/// ---------------------------------------------------------------------------

/// Choose at most k segments: write n boundaries, 2 <= n <= k + 1, into
/// `bounds`, forming a valid boundary list for the heap.  The heap is only
/// read.  How the boundaries are spread is not specified.
fn prepass
  (heap: heap_t)
  (k: SZ.t{SZ.v k >= 1})
  (bounds: A.array U64.t)
  (#g: erased heap_state)
  (#s0: erased (Seq.seq U64.t))
  requires is_heap heap g **
           A.pts_to bounds s0 **
           pure (A.length bounds == SZ.v k + 1)
  returns n: SZ.t
  ensures exists* s.
    is_heap heap g **
    A.pts_to bounds s **
    pure (Seq.length s == SZ.v k + 1 /\
          2 <= SZ.v n /\ SZ.v n <= SZ.v k + 1 /\
          SP.valid_bounds g (bounds_list s (SZ.v n)))

/// ---------------------------------------------------------------------------
/// 3. The merge
/// ---------------------------------------------------------------------------

/// The first m records of `rs` are the model's segment outputs `ms`, in order.
let results_match (rs: Seq.seq seg_result) (m: nat) (ms: list SP.seg) : prop =
  m <= Seq.length rs /\
  List.Tot.length ms == m /\
  (forall (i: nat). i < m ==> result_matches (Seq.index rs i) (List.Tot.index ms i).SP.out)

/// Link the segments, left to right.  The heap is the one the workers left:
/// the model's spliced heap.  `results` holds the m = n - 1 workers' records,
/// in segment order.  Returns the final heap and free-list head of the
/// model's sweep_par.
fn merge
  (heap: heap_t)
  (results: A.array seg_result)
  (m: SZ.t)
  (#g: erased heap_state)
  (#bs: erased (list nat))
  (#rs: erased (Seq.seq seg_result))
  (#p: perm)
  requires is_heap heap (SP.splice_all g (SP.sweep_all g (SP.segments bs))) **
           A.pts_to results #p rs **
           pure (SP.fused_pre g /\
                 SP.valid_bounds g bs /\
                 results_match rs (SZ.v m) (SP.sweep_all g (SP.segments bs)))
  returns fp: U64.t
  ensures exists* h.
    is_heap heap h **
    A.pts_to results #p rs **
    pure ((h, fp) == SP.sweep_par bs g)

/// ---------------------------------------------------------------------------
/// The three steps in one thread
/// ---------------------------------------------------------------------------

/// prepass, then sweep_segment on each segment in order, then merge.  The
/// caller provides room for k + 1 boundaries and k records.  The result is
/// the sequential pass's, by GC.Spec.SweepPar.sweep_par_correct.
fn sweep_par_seq
  (heap: heap_t)
  (k: SZ.t{SZ.v k >= 1})
  (bounds: A.array U64.t)
  (results: A.array seg_result)
  (#g: erased heap_state)
  (#b0: erased (Seq.seq U64.t))
  (#r0: erased (Seq.seq seg_result))
  requires is_heap heap g **
           A.pts_to bounds b0 **
           A.pts_to results r0 **
           pure (A.length bounds == SZ.v k + 1 /\
                 A.length results == SZ.v k /\
                 SP.fused_pre g)
  returns fp: U64.t
  ensures exists* h b r.
    is_heap heap h **
    A.pts_to bounds b **
    A.pts_to results r **
    pure ((h, fp) == Defs.fused_sweep_coalesce g)
