/// ---------------------------------------------------------------------------
/// GC.SPOT.MarkPhaseUnreached - the marking invariant read as well-formedness
/// ---------------------------------------------------------------------------
///
/// `GC.Spec.MarkPhase.unreached g` counts as free the blue blocks and the
/// white blocks the marker will not reach.  The minor collection at
/// `Marking` (`GC.Gen.MarkPhase.Minor`) keeps the weak tri-colour clause by
/// keeping well-formedness for it.  On the two heaps of `GC.SPOT.MarkPhase`:
///
///   * the mid-mark heap (B black -> W white, reached through G -> W1 -> W)
///     is well formed for it (`mid_unreached_wf`, from `marking_inv`);
///   * the heap where the only path to W goes through a black object (G ->
///     B -> W, W white and not reached) is not (`through_black_not_unreached_wf`):
///     B is not free for it and points at W, which is.  So the reading
///     tells the two apart, as the invariant does.

module GC.SPOT.MarkPhaseUnreached

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.MarkPhase

module H = GC.SPOT.MarkPhaseHeap
module S = GC.SPOT.MarkPhase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

let mid_unreached_wf (r: unit{H.room})
  : Lemma (well_formed_heap_with (unreached (S.mid r)) (S.mid r))
  = S.mid_mark_inv r;
    marking_inv_unreached (S.mid r) (S.held_w1 r)

let through_black_not_unreached_wf (r: unit{H.room})
  : Lemma (~(well_formed_heap_with (unreached (S.thr r)) (S.thr r)))
  = let h = S.thr r in
    S.heap_facts r S.thr_col S.thr_tg;
    S.through_black_not_reached r;
    FStar.Classical.move_requires (unreached_black_edge h h (H.obj r 2)) (H.obj r 4)
