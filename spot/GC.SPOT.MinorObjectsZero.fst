module GC.SPOT.MinorObjectsZero

/// Lemma proving that bump==0 implies minor_objects is empty
///
/// This is needed for empty heap precondition proofs

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

/// When bump is 0, minor_objects returns empty sequence
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let minor_objects_zero (ms: minor_state)
  : Lemma (requires U64.v ms.bump == 0 /\ U64.v ms.bump % 8 == 0 /\ U64.v ms.bump <= minor_heap_size)
          (ensures minor_objects ms == Seq.empty)
  = // The definition of minor_objects checks the bump value
    // When bump==0, it should delegate to minor_objects_aux which immediately returns empty
    // Let's try to let the definition reduce
    assert (U64.v ms.bump == 0);
    // Try normalization at term level
    let result = normalize_term (minor_objects ms) in
    assert (result == Seq.empty)
#pop-options

/// Corollary: No object is a member when bump==0
let minor_objects_zero_not_mem (ms: minor_state) (addr: U64.t)
  : Lemma (requires U64.v ms.bump == 0)
          (ensures ~(Seq.mem addr (minor_objects ms)))
  = minor_objects_zero ms;
    assert (minor_objects ms == Seq.empty);
    assert_norm (Seq.count addr Seq.empty == 0)
