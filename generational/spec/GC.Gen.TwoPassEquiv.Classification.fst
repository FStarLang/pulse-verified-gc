/// ---------------------------------------------------------------------------
/// GC.Gen.TwoPassEquiv.Classification
/// ---------------------------------------------------------------------------

module GC.Gen.TwoPassEquiv.Classification

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Impl.UpdatePtrs

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let fwd_ptrs_classified_field
  (major: heap) (fwd: forwarding_map) (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  (obj: obj_addr) (j: nat)
  = ()
#pop-options
