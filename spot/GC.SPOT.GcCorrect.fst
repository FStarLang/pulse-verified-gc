module GC.SPOT.GcCorrect

open FStar.Seq
open GC.Spec.Base

module U64 = FStar.UInt64
module Seq = FStar.Seq
module ConcreteMinor = GC.SPOT.ConcreteMinor
module ConcreteMajor = GC.SPOT.ConcreteMajor
module ConcreteScenarios = GC.SPOT.ConcreteScenarios
module ConcreteForwarding = GC.SPOT.ConcreteForwarding
module ThreeObjects = GC.SPOT.ThreeObjects
module GenImpl = GC.Gen.Impl
module CheneySpec = GC.Gen.Cheney
module MajorGC = GC.Impl
module Correct = GC.Impl.Correct

/// The fixture's pre-minor shape, root validity and no-OOM fact are the
/// existing SPOT lemmas `gen_gc`'s own call is discharged with; the major
/// precondition then follows from `gen_gc_major_precondition_elim`.
let spot_gc_precondition r =
  ConcreteScenarios.spot_collection_heap_shape r;
  ConcreteScenarios.spot_roots_valid_for_minor_collection r;
  ConcreteForwarding.spot_concrete_no_oom r;
  ThreeObjects.spot_roots_len (ConcreteMajor.spot_c r);
  GenImpl.gen_gc_major_precondition_elim
    ConcreteMinor.spot_minor2
    (ConcreteMajor.spot_major_heap r)
    (ConcreteMajor.spot_major_fp r)
    (ThreeObjects.spot_roots (ConcreteMajor.spot_c r))
    Seq.empty spot_cap

let spot_gc_correct r s2 final_fp =
  spot_gc_precondition r;
  Correct.gc_correct
    (spot_major_h_init r) s2 (spot_major_roots r) (spot_major_roots r)
    (spot_major_fp r) final_fp spot_cap
