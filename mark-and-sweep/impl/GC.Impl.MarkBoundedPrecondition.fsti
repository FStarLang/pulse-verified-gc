/// ---------------------------------------------------------------------------
/// GC.Impl.MarkBoundedPrecondition - deriving the major-GC precondition
/// ---------------------------------------------------------------------------
///
/// `GC.Impl.collect_with_roots` demands `gc_precondition_with_roots` on the
/// *post-darkening* heap and gray stack.  Asking a caller to discharge that
/// directly is unreasonable: it forces them to unfold `darken_roots_bounded_spec`
/// and reason about a state they never observe.
///
/// This module closes that gap once and for all.  `darken_establishes_precondition`
/// takes facts about the state the caller *does* observe -- the heap and stack
/// just before root darkening -- and produces the full major-GC precondition on
/// the darkened state, together with `roots_match_stack`.

module GC.Impl.MarkBoundedPrecondition

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SpecMark = GC.Spec.Mark
module SpecObject = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module SpecSweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module MB = GC.Impl.MarkBounded
module MajorGC = GC.Impl

open GC.Spec.Base

/// A root is usable by the darkening pass when it is a genuine, non-blue object
/// address of `g`.  This is the `U64.t`-valued analogue of `SpecMark.root_props`.
let root_valid_for_darkening (g: heap) (r: U64.t) : prop =
  is_val_addr r /\
  U64.v r >= U64.v zero_addr + U64.v mword /\
  Seq.mem (r <: obj_addr) (SpecFields.objects zero_addr g) /\
  ~(SpecObject.is_blue (r <: obj_addr) g)

val root_valid_for_darkening_points_to_object (g: heap) (r: U64.t)
  : Lemma (requires root_valid_for_darkening g r)
          (ensures MB.root_points_to_object g r)

/// The obligations a caller must meet on the heap and stack *before* root
/// darkening.  Every conjunct talks about `g`, `st` and `roots` only; nothing
/// here mentions `darken_roots_bounded_spec`.
let darken_precondition
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t) (fp: U64.t) (cap: nat)
  : prop =
  MarkBoundedInv.bounded_mark_inv g st cap /\
  SweepInv.fp_valid fp g /\
  SpecSweep.fp_in_heap fp g /\
  SpecMark.no_black_objects g /\
  SpecMark.no_pointer_to_blue g /\
  SpecFields.no_scan_invariant g /\
  SpecMark.gray_objects_on_stack g st /\
  (forall (x: obj_addr). Seq.mem x st ==> Seq.mem (x <: U64.t) roots) /\
  Seq.length st + Seq.length roots <= cap /\
  (forall (i: nat). i < Seq.length roots ==>
     root_valid_for_darkening g (Seq.index roots i))

/// Every root ends up on the darkened stack, and the darkened stack holds
/// nothing but roots.
val darken_roots_match_stack
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t) (fp: U64.t) (cap: nat)
  : Lemma
      (requires darken_precondition g st roots fp cap)
      (ensures
        (let st' = snd (MB.darken_roots_bounded_spec g st roots cap) in
         (forall (r: U64.t). Seq.mem r roots ==> is_val_addr r) /\
         (forall (r: obj_addr). Seq.mem (r <: U64.t) roots ==> Seq.mem r st') /\
         (forall (r: obj_addr). Seq.mem r st' ==> Seq.mem (r <: U64.t) roots)))

/// The main result: darkening a caller-supplied root set turns
/// `darken_precondition` into the full major-GC precondition.
val darken_establishes_precondition
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t) (fp: U64.t) (cap: nat)
  : Lemma
      (requires darken_precondition g st roots fp cap)
      (ensures
        (let g' = fst (MB.darken_roots_bounded_spec g st roots cap) in
         let st' = snd (MB.darken_roots_bounded_spec g st roots cap) in
         MajorGC.gc_precondition_with_roots g' st' st' fp cap))
