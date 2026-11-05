/// ---------------------------------------------------------------------------
/// GC.Spec.Allocator.Caches - an allocation keeps the sweep's caches derived
/// ---------------------------------------------------------------------------
///
/// The phase is the sweep's cursor alone; the implementation keeps the
/// sweep's two caches beside it in the phase record, and its phase predicate
/// says they are the ones derived from the current heap
/// (`GC.Spec.SweepPhase.Intrinsic.state_at`, `GC.Impl.Allocator.is_phase`).
/// An allocation only takes cells off the list or shrinks them in place,
/// inside the block it takes, so the cursor stays a position of the walk and
/// the fragment ending at it is the same.  When it takes the last cell behind
/// the cursor -- `swept_tail`'s own -- the last cell behind the cursor is the
/// cell before it on the ascending list: the allocator's in-place update
/// (`caml_fl_merge`, in `GC.Impl.Allocator.allocate`).
///
/// Writes that keep the walk and every header keep the derived caches too
/// (`GC.Spec.SweepPhase.Intrinsic.state_at_heads`).

module GC.Spec.Allocator.Caches

open GC.Spec.Base
open GC.Spec.SweepPhase.Intrinsic
open GC.Spec.Phase

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FLA = GC.Spec.FreeList.Ascending
module AC = GC.Spec.Allocator.Cursor

/// **One allocation keeps the caches derived**: from an exact ascending free
/// list, with the cursor `c` a position of the walk, the cursor is a
/// position of the new walk, and the derived state after it is the one
/// before with `swept_tail` moved back to the list predecessor of the block
/// taken when that block was `swept_tail`'s own and leaves the list.
val alloc_caches (g: heap) (fp: U64.t) (c: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256})
  : Lemma (requires FLA.fl_ascending g fp /\ W.reaches g zero_addr (U64.v c))
          (ensures (let g' = (AC.alloc_phase g fp (Sweeping c) wz tag).GC.Spec.Allocator.heap_out in
                    let (p, cur) = AC.alloc_choice g fp wz in
                    let st = state_at g c in
                    W.reaches g' zero_addr (U64.v c) /\
                    state_at g' c ==
                      { st with swept_tail =
                          (if cur = st.swept_tail && AC.takes_off g cur wz then p
                           else st.swept_tail) }))
