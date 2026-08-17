/// Opaque chain_all_inv predicate — implementation
module GC.Gen.PromoteUpdate.PromoteFields.ChainInv

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module AllocLemmas = GC.Spec.Allocator.Lemmas

[@@"opaque_to_smt"]
let chain_all_inv (minor: minor_state) (major: heap) (fp: U64.t)
                  (live_set: seq U64.t) (fwd: forwarding_map) (n: nat) : prop =
  forall (k:nat). k < n /\ k < Seq.length live_set ==>
    (let obj = Seq.index live_set k in
     let wz_k = minor_wosize minor obj in
     fwd obj <> 0UL /\ wz_k > 0 /\ is_val_addr (fwd obj) ==>
     (Seq.mem ((fwd obj) <: obj_addr) (objects zero_addr major) /\
      U64.v (wosize_of_object ((fwd obj) <: obj_addr) major) >= wz_k /\
      AllocLemmas.chain_avoids major fp (fwd obj) heap_words = true))

let chain_all_inv_intro (minor: minor_state) (major: heap) (fp: U64.t)
                        (live_set: seq U64.t) (fwd: forwarding_map) (n: nat)
  : Lemma (requires
      forall (k:nat). k < n /\ k < Seq.length live_set ==>
        (let obj = Seq.index live_set k in
         let wz_k = minor_wosize minor obj in
         fwd obj <> 0UL /\ wz_k > 0 /\ is_val_addr (fwd obj) ==>
         (Seq.mem ((fwd obj) <: obj_addr) (objects zero_addr major) /\
          U64.v (wosize_of_object ((fwd obj) <: obj_addr) major) >= wz_k /\
          AllocLemmas.chain_avoids major fp (fwd obj) heap_words = true)))
    (ensures chain_all_inv minor major fp live_set fwd n)
  = reveal_opaque (`%chain_all_inv) (chain_all_inv minor major fp live_set fwd n)

let chain_all_inv_elim (minor: minor_state) (major: heap) (fp: U64.t)
                       (live_set: seq U64.t) (fwd: forwarding_map) (n: nat)
  : Lemma (requires chain_all_inv minor major fp live_set fwd n)
    (ensures
      forall (k:nat). k < n /\ k < Seq.length live_set ==>
        (let obj = Seq.index live_set k in
         let wz_k = minor_wosize minor obj in
         fwd obj <> 0UL /\ wz_k > 0 /\ is_val_addr (fwd obj) ==>
         (Seq.mem ((fwd obj) <: obj_addr) (objects zero_addr major) /\
          U64.v (wosize_of_object ((fwd obj) <: obj_addr) major) >= wz_k /\
          AllocLemmas.chain_avoids major fp (fwd obj) heap_words = true)))
  = reveal_opaque (`%chain_all_inv) (chain_all_inv minor major fp live_set fwd n)

/// Pointwise elimination.
///
/// `chain_all_inv_elim` yields an unpatterned `forall`; instantiating it inside
/// a large proof context makes Z3 diverge, so callers that need a single index
/// use this version, which does the instantiation in a small context.
let chain_all_inv_elim_at (minor: minor_state) (major: heap) (fp: U64.t)
                          (live_set: seq U64.t) (fwd: forwarding_map) (n: nat) (k: nat)
  : Lemma (requires chain_all_inv minor major fp live_set fwd n /\
                    k < n /\ k < Seq.length live_set /\
                    (let obj = Seq.index live_set k in
                     let wz_k = minor_wosize minor obj in
                     fwd obj <> 0UL /\ wz_k > 0 /\ is_val_addr (fwd obj)))
    (ensures
      (let obj = Seq.index live_set k in
       let wz_k = minor_wosize minor obj in
       Seq.mem ((fwd obj) <: obj_addr) (objects zero_addr major) /\
       U64.v (wosize_of_object ((fwd obj) <: obj_addr) major) >= wz_k /\
       AllocLemmas.chain_avoids major fp (fwd obj) heap_words = true))
  = reveal_opaque (`%chain_all_inv) (chain_all_inv minor major fp live_set fwd n)
