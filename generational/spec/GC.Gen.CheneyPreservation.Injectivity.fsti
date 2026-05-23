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

let fwd_noninfix_sources_in_minor_objects
  (minor: minor_state) (fwd: forwarding_map) (g: heap) : prop =
  forall (x: U64.t). fwd x <> 0UL /\ is_val_addr (fwd x) /\
    is_infix (fwd x) g = false ==> Seq.mem x (minor_objects minor)

/// Normal forwarding targets are fresh with respect to pre-existing non-blue
/// major objects.  Infix forwarding entries are excluded: they are interior
/// pointers into a promoted object, not ordinary object starts.
let fwd_normal_targets_disjoint_from_old_nonblue
  (fwd: forwarding_map) (g_final: heap) (major0: heap) : prop =
  forall (x: U64.t) (y: obj_addr).
    fwd x <> 0UL /\
    is_val_addr (fwd x) /\
    is_infix (fwd x) g_final = false /\
    Seq.mem y (objects zero_addr major0) /\
    is_blue y major0 = false ==>
    fwd x <> y

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

val cheney_promote_fwd_noninfix_sources_in_minor_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_noninfix_sources_in_minor_objects
                     minor
                     (cheney_promote minor major fp roots).fwd_map
                     (cheney_promote minor major fp roots).major_final)

val cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_normal_targets_disjoint_from_old_nonblue
                     (cheney_promote minor major fp roots).fwd_map
                     (cheney_promote minor major fp roots).major_final
                     major)
