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

/// `k < idx + 1` and `k <> idx` give `k < idx`, in an empty context.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let ne_idx_gives_lt (k idx: nat) : Lemma
  (requires k < idx + 1 /\ ~(k == idx)) (ensures k < idx) = ()
#pop-options

/// Helper: extend chain_all_inv from idx to idx+1 when wz=0 (vacuous case).
#restart-solver
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let chain_all_inv_extend_skip
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      chain_all_inv minor major fp live_set fwd idx /\
      idx < Seq.length live_set /\
      minor_wosize minor (Seq.index live_set idx) = 0)
    (ensures chain_all_inv minor major fp live_set fwd (idx + 1))
  = // Establish the body of `chain_all_inv`'s forall index by index: letting Z3
    // chain `chain_all_inv_elim`'s unpatterned forall into `chain_all_inv_intro`
    // diverges.
    let aux (k: nat) : Lemma
      (ensures k < idx + 1 /\ k < Seq.length live_set ==>
        (let obj = Seq.index live_set k in
         let wz_k = minor_wosize minor obj in
         fwd obj <> 0UL /\ wz_k > 0 /\ is_val_addr (fwd obj) ==>
         (Seq.mem ((fwd obj) <: obj_addr) (objects zero_addr major) /\
          U64.v (wosize_of_object ((fwd obj) <: obj_addr) major) >= wz_k /\
          AllocLemmas.chain_avoids major fp (fwd obj) heap_words = true)))
      = if k < idx + 1 && k < Seq.length live_set then begin
          let obj = Seq.index live_set k in
          if fwd obj <> 0UL && minor_wosize minor obj > 0 && is_val_addr (fwd obj) then begin
            if k = idx then ()  // contradicts minor_wosize minor (index live_set idx) = 0
            else begin
              ne_idx_gives_lt k idx;
              chain_all_inv_elim_at minor major fp live_set fwd idx k
            end
          end else ()
        end else ()
    in
    FStar.Classical.forall_intro aux;
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
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0 --z3refresh"
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

/// Main recursive proof — runs at fuel 0 to prevent cascade.
/// The key invariant is fwd_zero_from: unprocessed positions have fwd = 0.
#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0 --z3refresh"
private let rec promote_all_aux_preserves_fields
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
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
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
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
