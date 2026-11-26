/// ---------------------------------------------------------------------------
/// GC.Gen.MarkPhase.Walk - where the walk of the heap ends, across marking
/// ---------------------------------------------------------------------------
///
/// A dense heap's walk ends at the end of the heap, or one header slot short
/// of it (`GC.Spec.Walk.reaches_end_of_dense`).  The per-word account of the
/// cycle (`GC.Gen.Run.Invariant.cycle_lossless`) compares the heap the cycle started
/// from with the heap marking hands over, so it needs the walk to end at the
/// same place.  Recolouring and writes into a block's body keep the walk; an
/// allocation carves its object out of a free block and the end of that
/// block stays a position of the walk (`GC.Spec.Allocator.Caches.
/// alloc_caches`, at any phase: the allocator at a phase is the idle one
/// recoloured); a minor collection is allocations, copies into the new
/// blocks' bodies, and a pointer update that keeps every header.
///
/// Stated as "the walk still reaches `e`", which, for `e` the end of a dense
/// walk, is the walk ending at `e` (`W.walk_end_of_reaches`).

module GC.Gen.MarkPhase.Walk

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module W = GC.Spec.Walk
module AC = GC.Spec.Allocator.Cursor
module AP = GC.Spec.Allocator.Phase
module SA = GC.Spec.Allocator
module FLA = GC.Spec.FreeList.Ascending
module GMM = GC.Gen.MarkPhase.Minor
module Promote = GC.Gen.Promote

/// **An allocation at any phase keeps a position of the walk** (from an
/// ascending free list).
val alloc_reaches (ph: Ph.gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256}) (e: nat)
  : Lemma (requires AP.alloc_ok g fp /\ FLA.fl_ascending g fp /\ W.reaches g zero_addr e /\ e <= heap_size)
          (ensures W.reaches (AC.alloc_phase g fp ph wz tag).SA.heap_out zero_addr e)

/// **A minor collection while marking keeps a position of the walk.**
val minor_reaches (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) (e: nat)
  : Lemma (requires AP.alloc_ok g fp /\ FLA.fl_ascending g fp /\ W.reaches g zero_addr e /\ e <= heap_size)
          (ensures W.reaches (GMM.collect_marking minor g fp roots).Promote.mc_major zero_addr e)
