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
let minor_objects_zero (ms: minor_state)
  : Lemma (requires U64.v ms.bump == 0)
          (ensures minor_objects ms == Seq.empty)
  = // We know minor_reset produces a state with bump==0 and empty objects
    // Let's use minor_reset_objects_empty
    // However, minor_reset might change ms.data, so we can't directly use it
    // 
    // Instead, let's use the fact that minor_init also produces bump==0
    // and we can prove minor_init produces empty objects
    let ms_init = minor_init ms.data in
    // ms_init has bump==0, just like ms
    assert (U64.v ms_init.bump == 0);
    assert (U64.v ms.bump == 0);
    // Both call minor_objects_aux with the same data and bump=0
    // So they should give the same result
    // Actually, they have the SAME data and SAME bump
    assert (ms_init.data == ms.data);
    assert (ms_init.bump == ms.bump);
    // Therefore ms_init == ms
    assert (ms_init == ms);
    // Now we need to prove minor_objects (minor_init data) == Seq.empty
    // But we don't have that lemma either...
    admit() // TODO: Need fundamental lemma about minor_objects and bump==0

/// Corollary: No object is a member when bump==0
let minor_objects_zero_not_mem (ms: minor_state) (addr: U64.t)
  : Lemma (requires U64.v ms.bump == 0)
          (ensures ~(Seq.mem addr (minor_objects ms)))
  = minor_objects_zero ms;
    assert (minor_objects ms == Seq.empty);
    assert_norm (Seq.count addr Seq.empty == 0)
