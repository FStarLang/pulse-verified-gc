/// Recursive field preservation through promote_all_aux — implementation
module GC.Gen.PromoteUpdate.PromoteFields.FieldsPres

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate.PromoteFields.ChainInv
open GC.Gen.PromoteUpdate.PromoteFields.Step

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// Helper: extend chain_all_inv from idx to idx+1 when wz=0 (vacuous case).
#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let chain_all_inv_extend_skip
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      chain_all_inv minor major fp live_set fwd idx /\
      idx < Seq.length live_set /\
      minor_wosize minor (Seq.index live_set idx) = 0)
    (ensures chain_all_inv minor major fp live_set fwd (idx + 1))
  = chain_all_inv_elim minor major fp live_set fwd idx;
    let obj_idx = Seq.index live_set idx in
    assert (minor_wosize minor obj_idx = 0);
    assert (forall (k:nat). k < idx + 1 /\ k < Seq.length live_set /\ k = idx ==>
            minor_wosize minor (Seq.index live_set k) = 0);
    chain_all_inv_intro minor major fp live_set fwd (idx + 1)
#pop-options

/// Helper: extend fields_match_minor from idx to target when fwd is 0 above idx.
/// Each position k in [idx, target) has fwd(obj_k) = 0UL, making the condition vacuous.
#restart-solver
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let rec fields_match_minor_extend_zero
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx target: nat)
  : Lemma (requires
      fields_match_minor minor major fwd live_set idx /\
      target >= idx /\
      target <= Seq.length live_set /\
      (forall (k:nat). idx <= k /\ k < target ==>
        fwd (Seq.index live_set k) = 0UL))
    (ensures fields_match_minor minor major fwd live_set target)
    (decreases (target - idx))
  = if idx >= target then ()
    else begin
      // fwd(obj_idx) = 0UL by precondition => first disjunct of extend
      fields_match_minor_extend minor major fwd live_set idx;
      fields_match_minor_extend_zero minor major fwd live_set (idx + 1) target
    end
#pop-options

#restart-solver
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0 --split_queries always --z3refresh"
/// Step case helper: bridges the IH to the postcondition via promote_all_aux_step,
/// without needing fuel-based unfolding (prevents cascade).
private let promote_all_step_case
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      idx < Seq.length live_set /\
      (let obj = Seq.index live_set idx in
       let wz = minor_wosize minor obj in
       wz > 0 /\
       (let res = promote_object minor major obj fp wz in
        res.new_addr <> 0UL /\
        (let fwd' = extend_forwarding fwd obj res.new_addr in
         let r_next = promote_all_aux minor res.major_out res.fp_out live_set fwd' (idx + 1) in
         fields_match_minor minor r_next.major_final r_next.fwd_map live_set (Seq.length live_set)))))
    (ensures
      (let res = promote_all_aux minor major fp live_set fwd idx in
       fields_match_minor minor res.major_final res.fwd_map live_set (Seq.length live_set)))
  = promote_all_aux_step minor major fp live_set fwd idx
#pop-options

/// Predicate: all elements in live_set at positions >= idx are distinct from element at idx.
/// This is needed for the step case to maintain fwd_zero_from across extend_forwarding.
let fwd_zero_from (fwd: forwarding_map) (live_set: seq U64.t) (idx: nat) : prop =
  forall (k:nat). idx <= k /\ k < Seq.length live_set ==> fwd (Seq.index live_set k) = 0UL

/// Distinctness: no two positions in live_set share the same address.
let distinct_live_set (live_set: seq U64.t) : prop =
  forall (i j: nat). i < Seq.length live_set /\ j < Seq.length live_set /\ i <> j ==>
    Seq.index live_set i <> Seq.index live_set j

/// Main recursive proof — runs at fuel 0 to prevent cascade.
/// The key invariant is fwd_zero_from: unprocessed positions have fwd = 0.
#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0 --split_queries always --z3refresh"
private let rec promote_all_aux_preserves_fields
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      fields_match_minor minor major fwd live_set idx /\
      chain_all_inv minor major fp live_set fwd idx /\
      fwd_zero_from fwd live_set idx /\
      distinct_live_set live_set)
    (ensures
      (let res = promote_all_aux minor major fp live_set fwd idx in
       fields_match_minor minor res.major_final res.fwd_map live_set (Seq.length live_set)))
    (decreases (Seq.length live_set - idx))
  = if idx >= Seq.length live_set then begin
      promote_all_aux_base minor major fp live_set fwd idx;
      fields_match_minor_weaken minor major fwd live_set idx (Seq.length live_set)
    end
    else begin
      let obj = Seq.index live_set idx in
      let wz = minor_wosize minor obj in
      if wz = 0 then begin
        promote_all_aux_skip minor major fp live_set fwd idx;
        chain_all_inv_extend_skip minor major fp live_set fwd idx;
        fields_match_minor_extend minor major fwd live_set idx;
        promote_all_aux_preserves_fields minor major fp live_set fwd (idx + 1)
      end
      else begin
        let res = promote_object minor major obj fp wz in
        if res.new_addr = 0UL then begin
          promote_all_aux_oom minor major fp live_set fwd idx;
          // OOM: promote_all_aux returns state unchanged, fwd_map = fwd
          // For positions >= idx: fwd(obj_k) = 0UL by fwd_zero_from
          fields_match_minor_extend_zero minor major fwd live_set idx (Seq.length live_set)
        end
        else begin
          promote_step_preserves_invariant minor major fp live_set fwd idx;
          let fwd' = extend_forwarding fwd obj res.new_addr in
          promote_all_aux_preserves_fields minor res.major_out res.fp_out live_set fwd' (idx + 1);
          promote_all_step_case minor major fp live_set fwd idx
        end
      end
    end
#pop-options

#restart-solver
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let promote_all_preserves_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    distinct_live_set live_set)
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fields_match_minor minor res.major_final res.fwd_map
                                       live_set (Seq.length live_set)))
  = chain_all_inv_intro minor major fp live_set empty_forwarding 0;
    assert (fwd_zero_from empty_forwarding live_set 0);
    assert (fields_match_minor minor major empty_forwarding live_set 0)
      by (FStar.Tactics.norm [delta_only [`%fields_match_minor]; zeta; iota; primops];
          FStar.Tactics.trivial ());
    promote_all_aux_preserves_fields minor major fp live_set empty_forwarding 0
#pop-options
