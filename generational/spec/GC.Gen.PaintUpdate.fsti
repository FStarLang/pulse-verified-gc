/// ---------------------------------------------------------------------------
/// GC.Gen.PaintUpdate - the pointer update commutes with painting
/// ---------------------------------------------------------------------------
///
/// After promotion the implementation rewrites the promoted objects' fields
/// (`update_promoted_iter`) and the remembered slots (`rewrite_slots_iter`) on
/// the heap it holds, which during a sweep is the idle heap painted
/// (`GC.Gen.Paint`).  Both passes write only words that are not positions of
/// the walk, and read headers only for their size and tag, which painting
/// keeps; so running them on the painted heap is painting their result.

module GC.Gen.PaintUpdate

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.SweepPhase.Intrinsic

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module Promote = GC.Gen.Promote
module Paint = GC.Gen.Paint
module UP = GC.Gen.Impl.UpdatePtrs
module RT = GC.Gen.RefTable

/// One object's update keeps the walk and every header, and commutes with
/// painting.
val paint_uop (c: nat) (g0 h: heap) (obj: obj_addr) (fwd: Promote.forwarding_map) (i: nat)
  : Lemma (requires Seq.mem obj (objects zero_addr h))
          (ensures (let wz = U64.v (wosize_of_object obj h) in
                    let h' = Promote.update_object_pointers h obj wz fwd i in
                    same_heads h h' /\
                    Paint.paint c g0 h' == Promote.update_object_pointers (Paint.paint c g0 h) obj wz fwd i))

/// The first pass.
val paint_upi (c: nat) (g0 h: heap) (farr: seq U64.t) (fwd: Promote.forwarding_map) (idx: nat)
  : Lemma (requires UP.promoted_entries_valid_from h farr idx)
          (ensures same_heads h (UP.update_promoted_iter h farr fwd idx) /\
                   UP.update_promoted_iter (Paint.paint c g0 h) farr fwd idx ==
                   Paint.paint c g0 (UP.update_promoted_iter h farr fwd idx))

/// Slots that are not positions of the walk.
let slots_off_walk (h: heap) (slots: seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (i: nat). i < n ==>
     (let a = U64.v (Seq.index slots i) in
      a < heap_size /\ a % 8 == 0 /\ ~(W.reaches h zero_addr a)))

/// The second pass.
val paint_rsi (c: nat) (g0 h: heap) (fwd: Promote.forwarding_map) (slots: seq U64.t) (n: nat) (idx: nat)
  : Lemma (requires slots_off_walk h slots n)
          (ensures same_heads h (UP.rewrite_slots_iter h fwd slots n idx) /\
                   UP.rewrite_slots_iter (Paint.paint c g0 h) fwd slots n idx ==
                   Paint.paint c g0 (UP.rewrite_slots_iter h fwd slots n idx))

/// The remembered slots are fields of non-free blocks, which the
/// collection keeps, so not positions of its walk.
val slots_off_walk_of_sound (free: free_def) (s: heap) (slots: seq U64.t) (n: nat) (h: heap)
  : Lemma (requires RT.ref_table_sound_with free s slots n /\ free_def_ok free /\ Paint.kept s h)
          (ensures slots_off_walk h slots n)

/// **Both passes, at a phase.**
val paint_two_pass (ph: GC.Spec.Phase.gc_phase) (g0 h: heap) (farr: seq U64.t)
                   (fwd: Promote.forwarding_map) (slots: seq U64.t) (n: nat)
  : Lemma (requires UP.promoted_entries_valid_from h farr 0 /\ slots_off_walk h slots n)
          (ensures UP.rewrite_slots_iter (UP.update_promoted_iter (Paint.paint_ph ph g0 h) farr fwd 0) fwd slots n 0 ==
                   Paint.paint_ph ph g0 (UP.rewrite_slots_iter (UP.update_promoted_iter h farr fwd 0) fwd slots n 0) /\
                   same_heads h (UP.rewrite_slots_iter (UP.update_promoted_iter h farr fwd 0) fwd slots n 0))
