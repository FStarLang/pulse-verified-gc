module GC.SPOT.GcCorrect

/// `GC.Impl.Correct.gc_correct` on the SPOT's concrete A/B/C fixture.
///
/// `full_gc`'s major phase starts from the heap `gen_gc_prepared_major` builds
/// from the fixture (the post-minor major heap with the roots darkened), with
/// the root objects `gen_gc_prepared_roots` and the minor collection's free
/// pointer; it marks and sweeps it in slices, and its postcondition is the
/// stop-the-world collector's (`GC.Impl.collect_with_roots`) on that heap.
/// This module shows the stop-the-world collector's precondition -- the first
/// hypothesis of `gc_correct` -- holds on that concrete heap, with the
/// darkening capacity `full_gc`'s contract names it by
/// (`GenImpl.prepared_cap`: the number of roots + 1), and instantiates
/// `gc_correct` there.

open FStar.Seq
open GC.Spec.Base

module U64 = FStar.UInt64
module Seq = FStar.Seq
module ConcreteMinor = GC.SPOT.ConcreteMinor
module ConcreteMajor = GC.SPOT.ConcreteMajor
module ThreeObjects = GC.SPOT.ThreeObjects
module GenImpl = GC.Gen.Impl
module CheneySpec = GC.Gen.Cheney
module MajorGC = GC.Impl
module Correct = GC.Impl.Correct

/// The darkening capacity the prepared state is named with
/// (`GenImpl.prepared_cap` of the post-minor roots): two roots, plus one.
let spot_cap : nat = 3

let spot_major_h_init (r: unit{ConcreteMajor.spot_major_room}) : GTot heap =
  GenImpl.gen_gc_prepared_major
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))

let spot_major_roots (r: unit{ConcreteMajor.spot_major_room}) : GTot (seq obj_addr) =
  GenImpl.gen_gc_prepared_roots
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))

let spot_major_fp (r: unit{ConcreteMajor.spot_major_room}) : GTot U64.t =
  (CheneySpec.cheney_collect_spec
     ConcreteMinor.spot_minor2
     (ConcreteMajor.spot_major_heap r)
     (ConcreteMajor.spot_major_fp r)
     (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))).mc_fp

/// `spot_cap` is `full_gc`'s darkening capacity for the fixture.
val spot_cap_prepared (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (spot_cap ==
           GenImpl.prepared_cap
             (CheneySpec.cheney_collect_spec
                ConcreteMinor.spot_minor2
                (ConcreteMajor.spot_major_heap r)
                (ConcreteMajor.spot_major_fp r)
                (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))).mc_roots)

/// `gc_correct`'s precondition hypothesis holds on the concrete heap.
val spot_gc_precondition (r: unit{ConcreteMajor.spot_major_room})
  : Lemma (MajorGC.gc_precondition_with_roots
             (spot_major_h_init r) (spot_major_roots r) (spot_major_roots r)
             (spot_major_fp r) spot_cap)

/// Any result of `collect_with_roots` on that heap is safe and live.
val spot_gc_correct
  (r: unit{ConcreteMajor.spot_major_room}) (s2: heap) (final_fp: U64.t)
  : Lemma
    (requires Correct.collect_post
                (spot_major_h_init r) s2 (spot_major_roots r) (spot_major_fp r) final_fp)
    (ensures Correct.gc_safe (spot_major_h_init r) s2 (spot_major_roots r) final_fp /\
             Correct.gc_live (spot_major_h_init r) s2 (spot_major_roots r)
               (spot_major_fp r) final_fp)
