/// ---------------------------------------------------------------------------
/// GC.Spec.MarkBoundedNoOverflow — when the bounded mark can skip the rescan
/// ---------------------------------------------------------------------------
///
/// The bounded mark drops a child when the gray stack is full: the child is
/// grayed in the heap but not pushed, and only a linear heap rescan finds it
/// again.  If no child was ever dropped, every gray object is still on the
/// stack (`SpecMark.gray_objects_on_stack`), so an empty stack already means
/// "no gray objects" and the rescan can be skipped.
///
/// The implementation does not instrument the drop itself.  A drop happens only
/// when the stack is full, and within one mark step the stack never shrinks
/// after the initial pop, so a step that dropped a child *ends* with a full
/// stack.  Testing `is_full` after each step is therefore a sound, conservative
/// overflow flag.  `mark_step_bounded_gray_on_stack` is that argument.

module GC.Spec.MarkBoundedNoOverflow

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Mark
open GC.Spec.MarkBounded

module U64 = FStar.UInt64
module SweepInv = GC.Spec.SweepInv

/// `push_children_bounded` only ever conses onto the stack.
val push_children_bounded_length_mono
  (g: heap) (st: seq obj_addr) (obj: obj_addr)
  (i: U64.t{U64.v i >= 1}) (ws: U64.t) (cap: nat)
  : Lemma (ensures Seq.length (snd (push_children_bounded g st obj i ws cap)) >= Seq.length st)
          (decreases (U64.v ws - U64.v i))

/// If every gray object is on the stack before `push_children_bounded`, and
/// the stack is not full afterwards, nothing was dropped, so every gray object
/// is still on the stack.
val push_children_bounded_gray_on_stack
  (g: heap) (st: seq obj_addr) (obj: obj_addr)
  (i: U64.t{U64.v i >= 1}) (ws: U64.t) (cap: nat)
  : Lemma (requires gray_objects_on_stack g st /\
                    Seq.length (snd (push_children_bounded g st obj i ws cap)) < cap)
          (ensures (let (g', st') = push_children_bounded g st obj i ws cap in
                    gray_objects_on_stack g' st'))
          (decreases (U64.v ws - U64.v i))

/// The same for a whole mark step: pop the head, blacken it, push children.
val mark_step_bounded_gray_on_stack
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires gray_objects_on_stack g st /\
                    Seq.length (snd (mark_step_bounded g st cap)) < cap)
          (ensures (let (g', st') = mark_step_bounded g st cap in
                    gray_objects_on_stack g' st'))

/// Every gray object is on the empty stack: there are none.
val no_gray_of_gray_on_empty_stack (g: heap) (st: seq obj_addr)
  : Lemma (requires gray_objects_on_stack g st /\ Seq.length st == 0)
          (ensures SweepInv.no_gray_objects g)

/// When the gray stack *is* the ghost root set, the major-GC precondition's
/// "gray or black ==> root" conjunct is `gray_objects_on_stack`.
val gray_on_stack_of_roots_eq_stack (g: heap) (st: seq obj_addr)
  : Lemma (requires forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\
                      (is_gray x g \/ is_black x g) ==> Seq.mem x st)
          (ensures gray_objects_on_stack g st)
