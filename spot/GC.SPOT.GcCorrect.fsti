module GC.SPOT.GcCorrect

/// `GC.Impl.Correct.gc_correct` on the SPOT's concrete A/B/C fixture.
///
/// Inside `gen_gc`, the major phase calls `GC.Impl.collect_with_roots` on the
/// heap `gen_gc_prepared_major` builds from the fixture (the post-minor major
/// heap with the roots darkened), with the prepared root stack and the minor
/// collection's free pointer.  This module shows that call's precondition --
/// the first hypothesis of `gc_correct` -- holds on that concrete heap, and
/// instantiates `gc_correct` there.

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

/// The gray stack `gen_gc` starts from (empty) and its capacity: two roots.
let spot_cap : nat = 2

let spot_major_h_init (r: unit{ConcreteMajor.spot_major_room}) : GTot heap =
  GenImpl.gen_gc_prepared_major
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
    Seq.empty spot_cap

let spot_major_roots (r: unit{ConcreteMajor.spot_major_room}) : GTot (seq obj_addr) =
  GenImpl.gen_gc_prepared_roots
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
    Seq.empty spot_cap

let spot_major_fp (r: unit{ConcreteMajor.spot_major_room}) : GTot U64.t =
  (CheneySpec.cheney_collect_spec
     ConcreteMinor.spot_minor2
     (ConcreteMajor.spot_major_heap r)
     (ConcreteMajor.spot_major_fp r)
     (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))).mc_fp

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
