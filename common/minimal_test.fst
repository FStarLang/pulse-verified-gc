module MinimalTest

open FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap

// Test if the opens cause issues
private let mask_2bit : UInt.uint_t 64 = UInt.logor #64 1 2

#push-options "--z3rlimit 10"
private let nth_mask_2bit (i: nat{i < 64}) : Lemma (UInt.nth #64 mask_2bit i = (i < 2)) =
  UInt.one_nth_lemma #64 i; 
  UInt.pow2_nth_lemma #64 1 i;
  assert_norm (UInt.pow2_n #64 1 = 2); 
  UInt.logor_definition #64 1 2 i
#pop-options
