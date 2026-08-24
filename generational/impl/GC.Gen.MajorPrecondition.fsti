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
/// None of that is really the caller's business.  Seven conjuncts are pure
/// heap-shape transport that `GC.Gen.CheneyPreservation` already proves; two
/// more become trivial once the gray stack starts empty, which is the only way
/// any caller ever calls the collector; and the last -- that every *post-minor*
/// root is a darkenable major object -- follows from the roots being valid for
/// the minor collection in the first place, plus the nursery fitting in the
/// free list.
///
/// So this module states the entry condition entirely in terms of the pre-minor
/// state the caller actually observes, and proves the transport once.

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
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney
module CheneyPres = GC.Gen.CheneyPreservation
module CheneyBFS = GC.Gen.CheneyBFS
module MinorFwd = GC.Gen.MinorCollectForwarding.Helpers
module MBP = GC.Impl.MarkBoundedPrecondition
module SpecGCPost = GC.Spec.Correctness

/// Every post-minor root is a genuine, non-blue major object.
///
/// This is the one conjunct of `darken_precondition` that mentions the rewritten
/// root set, and it used to be an obligation on `gen_gc`'s caller -- who has no
/// way to discharge it without unfolding the whole Cheney simulation.  It is
/// really a theorem about minor collection, and the two cases are quite
/// different.  A non-minor root survives `rewrite_root` untouched, so it only
/// has to stay a non-blue object, which Cheney's frame lemmas give.  A minor
/// root is forwarded (BFS coverage, from `cheney_no_oom`), and its target is an
/// ordinary object rather than an interior pointer because the source was a
/// `minor_objects` member and therefore not an infix sub-object.
val post_minor_roots_valid_for_darkening
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      MinorFwd.roots_valid_for_minor_collection minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let result = Cheney.cheney_collect_spec minor major fp roots in
      forall (i: nat). i < Seq.length result.mc_roots ==>
        MBP.root_valid_for_darkening result.mc_major (Seq.index result.mc_roots i)))

/// The main result: the major collector can be entered after a minor collection
/// on the strength of pre-minor facts alone.
///
/// `Seq.length roots <= cap` is the only sizing obligation, and it is the
/// obvious one: darkening pushes every root, so the gray stack has to be able
/// to hold them.  The stack itself starts empty -- it is collector scratch
/// space, and both real clients (SPOT and the OCaml runtime bridge) pass an
/// empty one.
val darken_precondition_after_minor
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (cap: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      MinorFwd.roots_valid_for_minor_collection minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots /\
      Seq.length roots <= cap /\ cap > 0)
    (ensures (
      let result = Cheney.cheney_collect_spec minor major fp roots in
      MBP.darken_precondition
        result.mc_major Seq.empty result.mc_roots result.mc_fp cap))

/// A heap between collections already satisfies the major-GC postcondition.
///
/// `major_heap_shape` records both `no_black_objects` and `no_gray_objects`, and
/// colours are exhaustive, so every object is white or blue -- which together
/// with well-formedness is exactly `gc_postcondition`.  `gen_gc` needs this on
/// the path where the minor collection ran out of memory and the major phase is
/// therefore skipped: the heap it returns is the post-minor heap, and the shape
/// invariant alone certifies it.
val major_heap_shape_gc_postcondition (major: heap) (fp: U64.t)
  : Lemma (requires GenInv.major_heap_shape major fp)
          (ensures SpecGCPost.gc_postcondition major)
