/// ---------------------------------------------------------------------------
/// GC.Spec.FusedSweep.Step - one step keeps the invariant
/// ---------------------------------------------------------------------------
///
/// One lemma per case of `GC.Spec.FusedSweep.sweep_step` (survivor; free
/// block left alone, linked or a fragment; garbage freed, linked or a
/// fragment; and the four merges -- into `swept_tail` or into the fragment
/// before the cursor, absorbing a block that was or was not on the list),
/// combined here into one statement, and lifted to the whole pass.

module GC.Spec.FusedSweep.Step

open GC.Spec.Base
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv

module U64 = FStar.UInt64

/// **One step keeps the invariant.**
val sweep_step_inv (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_g0 g0 /\ sweep_inv g0 g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in sweep_inv g0 g' fp' st'))

/// The sweep has reached the end of the heap with the invariant intact.
let sweep_done (g0 g: heap) (fp: U64.t) : prop =
  exists (st: sweep_state). sweep_inv g0 g fp st /\ U64.v st.cursor + 8 >= heap_size

/// **The whole pass keeps the invariant**, and stops at the end of the heap.
val sweep_from_done (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_g0 g0 /\ sweep_inv g0 g fp st)
          (ensures (let r = sweep_from g fp st in sweep_done g0 (fst r) (snd r)))

/// From the heap marking left, with the free list the previous cycle left.
val fused_sweep_done (g0: heap) (fp: U64.t)
  : Lemma (requires sweep_pre g0 fp)
          (ensures (let r = fused_sweep_coalesce g0 fp in sweep_done g0 (fst r) (snd r)))
