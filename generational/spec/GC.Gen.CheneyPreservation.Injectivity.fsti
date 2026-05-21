/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation.Injectivity -- forwarding injectivity interface
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation.Injectivity

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas

let fwd_normal_injective (fwd: forwarding_map) (g: heap) : prop =
  forall (x y: U64.t). fwd x <> 0UL /\ fwd y <> 0UL /\
    is_val_addr (fwd x) /\ is_val_addr (fwd y) /\
    is_infix (fwd x) g = false /\ is_infix (fwd y) g = false /\
    fwd x = fwd y ==> x = y

let fwd_targets_not_blue (fwd: forwarding_map) (g: heap) : prop =
  forall (x: U64.t). fwd x <> 0UL /\ is_val_addr (fwd x) /\
    is_infix (fwd x) g = false ==>
    Seq.mem ((fwd x) <: obj_addr) (objects zero_addr g) /\
    is_blue ((fwd x) <: obj_addr) g = false

val cheney_promote_fwd_normal_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
           (ensures fwd_normal_injective (cheney_promote minor major fp roots).fwd_map
                                         (cheney_promote minor major fp roots).major_final)

val cheney_promote_fwd_targets_not_blue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_targets_not_blue (cheney_promote minor major fp roots).fwd_map
                                        (cheney_promote minor major fp roots).major_final)
