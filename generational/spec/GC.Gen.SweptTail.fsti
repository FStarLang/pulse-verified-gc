/// ---------------------------------------------------------------------------
/// GC.Gen.SweptTail - the sweep's caches across promotion
/// ---------------------------------------------------------------------------
///
/// The phase is the sweep's cursor alone; the implementation keeps the
/// sweep's two caches beside it in the phase record, and its phase predicate
/// says they are the ones derived from the current heap
/// (`GC.Spec.SweepPhase.Intrinsic.state_at`, `GC.Impl.Allocator.is_phase`).
/// The allocation of a promotion keeps them so
/// (`GC.Spec.Allocator.Caches.alloc_caches`, inside `GC.Impl.Allocator.allocate`);
/// the rest of a promotion (the copy of the fields, `promote_heads`) and the
/// pointer update after the promotions (`update_heads`) write no header, so
/// they keep the walk and every header, and with them the derived caches
/// (`GC.Spec.SweepPhase.Intrinsic.state_at_heads`).

module GC.Gen.SweptTail

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.SweepPhase.Intrinsic
open GC.Spec.Phase
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module AP = GC.Spec.Allocator.Phase
module Promote = GC.Gen.Promote

/// **The copy of a promotion** keeps the walk and every header of the heap
/// the allocation left (and a failed promotion changes nothing).
val promote_heads (ph: gc_phase) (g: heap) (fp: U64.t) (minor: minor_state) (obj: U64.t)
                  (wz: nat{wz > 0})
  : Lemma (requires FLA.fl_ascending g fp)
          (ensures (let tag = Promote.promoted_tag minor obj in
                    let ar = AP.alloc_at ph g fp wz tag in
                    let r = Promote.promote_object minor g obj fp wz ph in
                    same_heads ar.GC.Spec.Allocator.heap_out r.Promote.major_out))

/// The pointer update keeps the walk and every header.
val update_heads (major: heap) (free: free_def) (fwd: Promote.forwarding_map)
  : Lemma (same_heads major (Promote.update_pointers_with free major fwd))
