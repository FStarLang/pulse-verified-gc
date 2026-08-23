/// ---------------------------------------------------------------------------
/// GC.Gen.MajorPrecondition -- deriving the major-GC entry condition across a
/// minor collection
/// ---------------------------------------------------------------------------
///
/// `GC.Impl.MarkBoundedPrecondition.darken_precondition` is the contract the
/// major collector needs *before* root darkening.  `gen_gc` must satisfy it on
/// the state produced by the preceding minor collection, so left to itself a
/// caller has to transport all ten of its conjuncts across
/// `cheney_collect_spec` by hand.
///
/// Seven of those ten are pure heap-shape transport: they mention only the
/// major heap and the caller's own gray stack, and `GC.Gen.CheneyPreservation`
/// already proves each of them.  Re-citing that family at every call site is
/// exactly the kind of leak `MarkBoundedPrecondition` was written to close, one
/// phase earlier.  This module closes it.
///
/// `darken_precondition_after_minor` takes facts about the state the caller
/// *does* observe -- the pre-minor heap and stack -- plus the three residual
/// obligations that genuinely mention the post-minor root set, and produces the
/// full `darken_precondition` on the post-minor state.

module GC.Gen.MajorPrecondition

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module SpecMark = GC.Spec.Mark
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module GenInv = GC.Gen.HeapInvariant
module Cheney = GC.Gen.Cheney
module CheneyPres = GC.Gen.CheneyPreservation
module MBP = GC.Impl.MarkBoundedPrecondition

/// The conjuncts of `darken_precondition` that genuinely belong to the caller,
/// because they relate the caller's gray stack and capacity budget to the
/// *post-minor* root set.  Unlike the other seven they are not preserved by
/// anything: the minor collection rewrites the roots, so only the caller knows
/// how the resulting set relates to the stack it supplied.
let post_minor_root_obligations
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (st: seq obj_addr) (cap: nat) : prop =
  let result = Cheney.cheney_collect_spec minor major fp roots in
  (forall (x: obj_addr). Seq.mem x st ==> Seq.mem (x <: U64.t) result.mc_roots) /\
  Seq.length st + Seq.length result.mc_roots <= cap /\
  (forall (i: nat). i < Seq.length result.mc_roots ==>
     MBP.root_valid_for_darkening result.mc_major (Seq.index result.mc_roots i))

/// `CheneyPreservation` states the color-stack condition in its gray-or-black
/// form because that is what promotion preserves; the major GC wants the
/// gray-only form.  Under `no_black_objects` -- which `major_heap_shape`
/// supplies -- the two coincide, but the implication holds outright.
val gray_black_objects_on_stack_weaken (g: heap) (st: seq obj_addr)
  : Lemma (requires CheneyPres.gray_black_objects_on_stack g st)
          (ensures SpecMark.gray_objects_on_stack g st)

/// The converse under `no_black_objects`, which is how a caller holding only
/// the gray-only form feeds the preservation lemma.
val gray_objects_on_stack_strengthen (g: heap) (st: seq obj_addr)
  : Lemma (requires SpecMark.gray_objects_on_stack g st /\
                    SpecMark.no_black_objects g)
          (ensures CheneyPres.gray_black_objects_on_stack g st)

/// The main result: a well-formed pre-minor state, a gray stack that is already
/// good for the *pre-minor* heap, and the three residual root obligations are
/// enough to enter the major collector after a minor collection.
///
/// Note what is *not* required: nothing here unfolds `cheney_collect_spec`, and
/// the only post-minor state the caller mentions is the root set, via
/// `post_minor_root_obligations`.
val darken_precondition_after_minor
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (st: seq obj_addr) (cap: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      MarkBoundedInv.bounded_mark_inv major st cap /\
      SpecMark.gray_objects_on_stack major st /\
      post_minor_root_obligations minor major fp roots st cap)
    (ensures (
      let result = Cheney.cheney_collect_spec minor major fp roots in
      MBP.darken_precondition result.mc_major st result.mc_roots result.mc_fp cap))
