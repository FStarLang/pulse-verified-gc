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

/// A root is usable by the darkening pass when it *names* a genuine, non-blue
/// object of `g`.  This is the `U64.t`-valued analogue of `SpecMark.root_props`.
///
/// "Names" rather than "is": the root is passed through
/// `SpecObject.resolve_object`, exactly as `check_and_darken_bounded_spec`
/// does, so an interior (infix) pointer is a legitimate root and denotes the
/// closure it points into.  `resolve_object` is the identity on ordinary
/// pointers, so for those this is unchanged.
let root_valid_for_darkening (g: heap) (r: U64.t) : prop =
  is_val_addr r /\
  U64.v r >= U64.v zero_addr + U64.v mword /\
  Seq.mem (SpecObject.resolve_object (r <: obj_addr) g)
          (SpecFields.objects zero_addr g) /\
  ~(SpecObject.is_blue (SpecObject.resolve_object (r <: obj_addr) g) g)

val root_valid_for_darkening_points_to_object (g: heap) (r: U64.t)
  : Lemma (requires SpecFields.well_formed_heap g /\ root_valid_for_darkening g r)
          (ensures MB.root_points_to_object g r)

/// The objects `roots` names in `g`: every root, resolved through any interior
/// (infix) pointer it may be.  A darkened stack holds exactly these, which is
/// weaker than "every stack entry is a root value" -- an interior root pushes
/// the closure it points into, and that closure is not itself a root value.
let root_named (g: heap) (roots: Seq.seq U64.t) (x: obj_addr) : prop =
  exists (q: obj_addr).
    Seq.mem (q <: U64.t) roots /\ SpecObject.resolve_object q g == x

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
  SpecMark.gray_objects_on_stack g st /\
  (forall (x: obj_addr). Seq.mem x st ==> root_named g roots x) /\
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
         (forall (r: obj_addr). Seq.mem (r <: U64.t) roots ==>
            Seq.mem (SpecObject.resolve_object r g) st') /\
         (forall (r: obj_addr). Seq.mem r st' ==> root_named g roots r)))

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

/// Darkening recolours headers only, so the caller may freely move statements
/// about the object graph across it.
val darken_preserves_create_graph
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t) (fp: U64.t) (cap: nat)
  : Lemma
      (requires darken_precondition g st roots fp cap /\ SpecFields.well_formed_heap g)
      (ensures
        GC.Spec.HeapModel.create_graph (fst (MB.darken_roots_bounded_spec g st roots cap)) ==
        GC.Spec.HeapModel.create_graph g)
