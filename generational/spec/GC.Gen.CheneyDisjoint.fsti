/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyDisjoint — Forwarding targets disjoint from non-blue objects
/// ---------------------------------------------------------------------------
///
/// Proves that the Cheney BFS forwarding map produces targets that are disjoint
/// from all non-blue (allocated, non-free-list) objects in the initial major heap.
///
/// This discharges the "Promoted disjoint from non-blue major" conjunct of
/// iso_structural_preconditions in CombinedGraph.Isomorphism.TopLevel.
///
/// Key insight: at each allocation step, the new object is taken FROM the free
/// chain. Non-blue objects avoid the chain (by chain_objects_blue). Therefore,
/// alloc_spec_obj_ne_excl gives new_addr ≠ non-blue objects. This invariant
/// is maintained inductively through cheney_promote.
///
/// Dependencies:
///   - GC.Gen.AllocProps.alloc_spec_obj_ne_excl
///   - GC.Gen.PromoteUpdate.PromoteFields.ReadOther.promote_object_preserves_chain_avoids
///   - GC.Gen.PromoteUpdate.BlueProm.promote_object_preserves_chain_objects_blue
///   - GC.Gen.Cheney (cheney_promote, cheney_forward_one, etc.)

module GC.Gen.CheneyDisjoint

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
/// Invariant definitions
/// ---------------------------------------------------------------------------

/// Non-blue objects of the initial major heap maintain chain_avoids,
/// membership in objects, and wosize >= 1 in the evolving heap.
let orig_nonblue_props (cs: cheney_state) (major_orig: heap) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (objects zero_addr major_orig) /\
    ~(is_blue obj major_orig) ==>
    (Seq.mem obj (objects zero_addr cs.cs_major) /\
     U64.v (wosize_of_object obj cs.cs_major) >= 1 /\
     AllocLemmas.chain_avoids cs.cs_major cs.cs_fp obj
       (heap_size / U64.v mword) = true)

/// All forwarding targets are disjoint from non-blue objects of the initial major.
/// (Defined on cheney_state for the inductive proof.)
let fwd_disjoint_nonblue (cs: cheney_state) (major_orig: heap) : prop =
  forall (a: U64.t) (obj: obj_addr).
    cs.cs_fwd a <> 0UL /\
    Seq.mem obj (objects zero_addr major_orig) /\
    ~(is_blue obj major_orig) ==>
    cs.cs_fwd a <> (obj <: U64.t)

/// Property on forwarding_map directly (for the top-level theorem).
let fwd_map_disjoint_nonblue (fwd: forwarding_map) (major_orig: heap) : prop =
  forall (a: U64.t) (obj: obj_addr).
    fwd a <> 0UL /\
    Seq.mem obj (objects zero_addr major_orig) /\
    ~(is_blue obj major_orig) ==>
    fwd a <> (obj <: U64.t)

/// Combined invariant for the disjoint property proof.
let cheney_disjoint_invariant (cs: cheney_state) (major_orig: heap) : prop =
  well_formed_heap_part1 cs.cs_major /\
  AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
  AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
  chain_objects_blue cs.cs_major cs.cs_fp /\
  orig_nonblue_props cs major_orig /\
  fwd_disjoint_nonblue cs major_orig

/// ---------------------------------------------------------------------------
/// Main theorem
/// ---------------------------------------------------------------------------

/// After cheney_promote, all forwarding targets are disjoint from non-blue
/// objects of the initial major heap.
val cheney_promote_fwd_disjoint_nonblue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp)
    (ensures
      (let prom = cheney_promote minor major fp roots in
       fwd_map_disjoint_nonblue prom.fwd_map major))
