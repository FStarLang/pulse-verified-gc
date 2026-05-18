/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyInjectivity — Forwarding map injectivity for Cheney BFS
/// ---------------------------------------------------------------------------
///
/// Proves that cheney_promote produces an injective forwarding map:
/// distinct minor objects get distinct major-heap addresses.
///
/// Key argument:
///   - The allocator returns a free-list node and removes it from the chain
///   - After allocation, the returned address is White (non-blue)
///   - chain_objects_blue is preserved, so non-blue objects avoid the chain
///   - Therefore subsequent allocations cannot return the same address
///
/// Building blocks used:
///   - GC.Gen.AllocProps.alloc_spec_obj_ne_excl
///   - GC.Gen.AllocProps.alloc_spec_obj_not_blue_part1
///   - GC.Gen.PromoteUpdate.PromoteFields.ReadOther.promote_object_preserves_chain_avoids

module GC.Gen.CheneyInjectivity

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

/// ---------------------------------------------------------------------------
/// Forwarding map injectivity predicate
/// ---------------------------------------------------------------------------

/// The forwarding map is injective on its defined domain (non-zero entries):
/// if fwd(a) == fwd(b) != 0 then a == b.
let fwd_injective (fwd: forwarding_map) : prop =
  forall (a b: U64.t).
    fwd a <> 0UL /\ fwd b <> 0UL /\ fwd a == fwd b ==> a == b

/// ---------------------------------------------------------------------------
/// Inductive invariant: fwd targets avoid the current free chain
/// ---------------------------------------------------------------------------

/// All non-zero targets of the forwarding map avoid the current free chain.
/// This ensures subsequent allocations return fresh addresses (via alloc_spec_obj_ne_excl).
/// Also carries validity properties needed by promote_object_preserves_chain_avoids.
let fwd_targets_avoid_chain (cs: cheney_state) : prop =
  forall (a: U64.t). cs.cs_fwd a <> 0UL ==>
    (U64.v (cs.cs_fwd a) >= U64.v mword /\
     U64.v (cs.cs_fwd a) < heap_size /\
     U64.v (cs.cs_fwd a) % U64.v mword == 0 /\
     Seq.mem ((cs.cs_fwd a) <: obj_addr) (objects zero_addr cs.cs_major) /\
     U64.v (wosize_of_object ((cs.cs_fwd a) <: obj_addr) cs.cs_major) >= 1 /\
     AllocLemmas.chain_avoids cs.cs_major cs.cs_fp (cs.cs_fwd a)
       (heap_size / U64.v mword) = true)

/// Combined invariant threaded through cheney_forward_one / scan
let cheney_inj_invariant (cs: cheney_state) : prop =
  well_formed_heap_part1 cs.cs_major /\
  AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
  AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
  chain_objects_blue cs.cs_major cs.cs_fp /\
  fwd_injective cs.cs_fwd /\
  fwd_targets_avoid_chain cs

/// ---------------------------------------------------------------------------
/// Preservation through cheney_forward_one
/// ---------------------------------------------------------------------------

/// cheney_forward_one preserves the injectivity invariant.
val cheney_forward_one_preserves_inj_invariant
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires cheney_inj_invariant cs)
          (ensures cheney_inj_invariant (cheney_forward_one minor cs addr))

/// ---------------------------------------------------------------------------
/// Preservation through cheney_forward_fields
/// ---------------------------------------------------------------------------

/// cheney_forward_fields preserves the injectivity invariant.
val cheney_forward_fields_preserves_inj_invariant
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires cheney_inj_invariant cs)
          (ensures cheney_inj_invariant (cheney_forward_fields minor cs parent idx wosize))

/// ---------------------------------------------------------------------------
/// Preservation through cheney_forward_roots
/// ---------------------------------------------------------------------------

/// cheney_forward_roots preserves the injectivity invariant.
val cheney_forward_roots_preserves_inj_invariant
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires cheney_inj_invariant cs)
          (ensures cheney_inj_invariant (cheney_forward_roots minor cs roots idx))

/// ---------------------------------------------------------------------------
/// Preservation through cheney_scan
/// ---------------------------------------------------------------------------

/// cheney_scan preserves the injectivity invariant.
val cheney_scan_preserves_inj_invariant
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires cheney_inj_invariant cs)
          (ensures cheney_inj_invariant (cheney_scan minor cs scan fuel))

/// ---------------------------------------------------------------------------
/// Top-level theorem: cheney_promote produces an injective fwd_map
/// ---------------------------------------------------------------------------

/// The forwarding map produced by cheney_promote is injective.
val cheney_promote_fwd_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp)
    (ensures
      fwd_injective (cheney_promote minor major fp roots).fwd_map)
