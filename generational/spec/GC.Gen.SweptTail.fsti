/// ---------------------------------------------------------------------------
/// GC.Gen.SweptTail - the sweep's `swept_tail` across a minor collection
/// ---------------------------------------------------------------------------
///
/// During a sweep the allocator keeps `swept_tail` -- the last free-list cell
/// behind the cursor -- up to date as it takes cells off the list
/// (`GC.Spec.Allocator.Cursor.alloc_tail`).  Nothing else of the phase moves:
/// the colour of a new object depends only on the cursor.  So across the
/// promotions of a minor collection the phase the implementation holds is the
/// one it started in with `swept_tail` the last cell at or below where it was
/// (`phase_at`): allocation only takes cells off the list (or shrinks them in
/// place), and when it takes `swept_tail`'s own cell the tail moves to the
/// cell before it on the ascending list.

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
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module AC = GC.Spec.Allocator.Cursor
module AP = GC.Gen.AllocPhase
module Promote = GC.Gen.Promote

/// The last cell at or below `x` (0 when there is none).
let rec max_cell_below (g: heap) (x: nat) : GTot U64.t (decreases x) =
  if x = 0 then 0UL
  else if x < heap_size && FStar.IndefiniteDescription.strong_excluded_middle (FL.fl_cell g (U64.uint_to_t x))
  then U64.uint_to_t x
  else max_cell_below g (x - 1)

val max_cell_below_spec (g: heap) (x: nat)
  : Lemma (let m = max_cell_below g x in
           (m == 0UL \/ (FL.fl_cell g m /\ U64.v m <= x)) /\
           (forall (y: U64.t). FL.fl_cell g y /\ U64.v y <= x ==> m <> 0UL /\ U64.v y <= U64.v m))

/// Heaps with the same cells have the same last cells.
val max_cell_below_congr (g g': heap) (x: nat)
  : Lemma (requires forall (y: U64.t). FL.fl_cell g' y <==> FL.fl_cell g y)
          (ensures max_cell_below g' x == max_cell_below g x)

/// The phase, with `swept_tail` the last cell of `g` at or below where it was.
let phase_at (ph: gc_phase) (g: heap) : GTot gc_phase =
  match ph with
  | Idle -> Idle
  | Sweeping st -> Sweeping { st with swept_tail = max_cell_below g (U64.v st.swept_tail) }

/// A tail that is a cell (or the sentinel) is its own last cell.
val phase_at_self (ph: gc_phase) (g: heap)
  : Lemma (requires (match ph with
                     | Idle -> True
                     | Sweeping st -> st.swept_tail == 0UL \/ FL.fl_cell g st.swept_tail))
          (ensures phase_at ph g == ph)

/// The phase depends only on the free-list cells, so a change that keeps the
/// walk and every header keeps it.
val phase_at_heads (ph: gc_phase) (h h': heap)
  : Lemma (requires same_heads h h') (ensures phase_at ph h' == phase_at ph h)

/// **One allocation at the phase the implementation holds** is the one at
/// the phase the collection started in, and leaves the phase at the heap it
/// returns.
val alloc_phase_at (ph0: gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t)
  : Lemma (requires FLA.fl_ascending g fp)
          (ensures (let ar = AC.alloc_phase g fp (phase_at ph0 g) wz tag in
                    fst ar == AP.alloc_at ph0 g fp wz tag /\
                    snd ar == phase_at ph0 (AP.alloc_at ph0 g fp wz tag).GC.Spec.Allocator.heap_out))

/// **One promotion at the phase the implementation holds**: the same
/// allocation, and the phase it leaves is the phase at the heap the promotion
/// returns (copying the fields writes no header).
val promote_phase_at (ph0: gc_phase) (g: heap) (fp: U64.t) (minor: minor_state) (obj: U64.t)
                     (wz: nat{wz > 0})
  : Lemma (requires FLA.fl_ascending g fp)
          (ensures (let ar = AC.alloc_phase g fp (phase_at ph0 g) wz (Promote.promoted_tag minor obj) in
                    let r = Promote.promote_object minor g obj fp wz ph0 in
                    fst ar == AP.alloc_at ph0 g fp wz (Promote.promoted_tag minor obj) /\
                    snd ar == phase_at ph0 r.Promote.major_out))

/// The pointer update keeps the walk and every header (so the phase).
val update_heads (major: heap) (free: free_def) (fwd: Promote.forwarding_map)
  : Lemma (same_heads major (Promote.update_pointers_with free major fwd))
