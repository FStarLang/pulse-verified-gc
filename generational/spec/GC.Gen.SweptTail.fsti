/// ---------------------------------------------------------------------------
/// GC.Gen.SweptTail - the sweep's caches across allocation and promotion
/// ---------------------------------------------------------------------------
///
/// The phase is the sweep's cursor alone; the implementation keeps the
/// sweep's two caches beside it in the phase record, and its phase predicate
/// says they are the ones derived from the current heap
/// (`GC.Spec.SweepPhase.Intrinsic.state_at`, `GC.Impl.Allocator.is_phase`).
/// This module is what keeps them so:
///
///   * **An allocation** (`alloc_caches`) only takes cells off the list or
///     shrinks them in place, inside the block it takes, so the cursor stays a
///     position of the walk and the fragment ending at it is the same.  When
///     it takes the last cell behind the cursor -- `swept_tail`'s own -- the
///     last cell behind the cursor is the cell before it on the ascending
///     list: the allocator's in-place update (`caml_fl_merge`,
///     `GC.Impl.Allocator.record_after_alloc`).
///   * **The rest of a promotion** (the copy of the fields, `promote_heads`)
///     and the pointer update after the promotions (`update_heads`) write
///     no header, so they keep the walk and every header, and with them the
///     derived caches (`GC.Spec.SweepPhase.Intrinsic.state_at_heads`).

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
module AC = GC.Spec.Allocator.Cursor
module AP = GC.Gen.AllocPhase
module Promote = GC.Gen.Promote

/// **One allocation keeps the caches derived**: from an exact ascending free
/// list, with the cursor `c` a position of the walk, the cursor is a
/// position of the new walk, and the derived state after it is the one
/// before with `swept_tail` moved back to the list predecessor of the block
/// taken when that block was `swept_tail`'s own and leaves the list.
val alloc_caches (g: heap) (fp: U64.t) (c: U64.t) (wz: nat) (tag: AP.tag_t)
  : Lemma (requires FLA.fl_ascending g fp /\ W.reaches g zero_addr (U64.v c))
          (ensures (let g' = (AC.alloc_phase g fp (Sweeping c) wz tag).GC.Spec.Allocator.heap_out in
                    let (p, cur) = AC.alloc_choice g fp wz in
                    let st = state_at g c in
                    W.reaches g' zero_addr (U64.v c) /\
                    state_at g' c ==
                      { st with swept_tail =
                          (if cur = st.swept_tail && AC.takes_off g cur wz then p
                           else st.swept_tail) }))

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
