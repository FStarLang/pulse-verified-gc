/// ---------------------------------------------------------------------------
/// GC.Gen.MarkPhase.Start - the start of marking
/// ---------------------------------------------------------------------------
///
/// A major cycle starts idle, right after a minor collection (the nursery
/// empty): the roots are darkened (4.14's `caml_darken_all_roots_start`) and
/// the collector enters `Marking`.  `darkened g rs` is the heap root
/// darkening leaves; it does not depend on the stack the implementation
/// pushes onto (`GC.Gen.MarkSlice.darken_roots_heap`), so it is stated with
/// a stack that holds every root.
///
/// `mark_start_shape`: the darkened heap is the collector's state at
/// `Marking` -- the minor collection's shape at `free_stw` (darkening only
/// greys white blocks), and the marking invariant (nothing is black, so no
/// black object points at a white one, `MP.marking_inv_start`; the empty
/// nursery holds nothing) -- and every object the roots point at is grey,
/// so the roots are held (`MP.held_reached`).

module GC.Gen.MarkPhase.Start

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module GenInv = GC.Gen.HeapInvariant
module GI = GC.Gen.Incremental
module GMM = GC.Gen.MarkPhase.Minor
module MP = GC.Spec.MarkPhase
module MB = GC.Impl.MarkBounded
module MBP = GC.Impl.MarkBoundedPrecondition

/// The heap root darkening leaves.
let darkened (g: heap) (rs: seq U64.t) : GTot heap =
  fst (MB.darken_roots_bounded_spec g Seq.empty rs (Seq.length rs + 1))

/// **The start of marking.**
val mark_start_shape (minor: minor_state) (g: heap) (fp: U64.t) (rs: seq U64.t)
  : Lemma (requires GenInv.collection_heap_shape minor g fp /\ minor == minor_reset minor /\
                    (forall (i: nat). i < Seq.length rs ==> MBP.root_valid_for_darkening g (Seq.index rs i)))
          (ensures GI.phase_shape minor (darkened g rs) fp Ph.Marking /\
                   MP.held_reached (darkened g rs) (GMM.roots_held (darkened g rs) rs))

/// **Every object a root names is darkened**: not white in the darkened heap
/// (it is grey, on the stack root darkening pushes).
val darkened_roots_dark (minor: minor_state) (g: heap) (fp: U64.t) (rs: seq U64.t) (w: obj_addr)
  : Lemma (requires GenInv.collection_heap_shape minor g fp /\
                    (forall (i: nat). i < Seq.length rs ==> MBP.root_valid_for_darkening g (Seq.index rs i)) /\
                    GMM.roots_held (darkened g rs) rs w)
          (ensures ~(is_white w (darkened g rs)))
