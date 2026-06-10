/// Step lemma: one promote_object preserves the inductive invariant — implementation
module GC.Gen.PromoteUpdate.PromoteFields.Step

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas
open GC.Gen.PromoteUpdate.Obj
open GC.Gen.PromoteUpdate.Aux
open GC.Gen.PromoteUpdate.Header
open GC.Gen.PromoteUpdate.PromoteFields.ChainInv
open GC.Gen.PromoteUpdate.PromoteFields.ReadOther
open GC.Lib.Header

module AllocLemmas = GC.Spec.Allocator.Lemmas
module WriteBody = GC.Gen.WriteBodyLemmas

private let copy_fields_preserves_objects_aux = WriteBody.copy_fields_preserves_objects_aux
private let copy_fields_preserves_fl_valid_aux = WriteBody.copy_fields_preserves_fl_valid_aux
private let copy_fields_preserves_fl_chain_terminates = WriteBody.copy_fields_preserves_fl_chain_terminates
private let copy_fields_preserves_wfh_part1 = WriteBody.copy_fields_preserves_wfh_part1
private let chain_avoids_implies_not_in_fl_chain = WriteBody.chain_avoids_implies_not_in_fl_chain
private let copy_fields_preserves_chain_avoids_self = WriteBody.copy_fields_preserves_chain_avoids_self

/// Helper: explicitly eliminate the `fields_match_minor` quantifier for a given k and j.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let fields_match_minor_elim
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx: nat) (k: nat) (j: nat)
  (field_addr: hp_addr)
  : Lemma (requires
      fields_match_minor minor major fwd live_set idx /\
      k < idx /\ k < Seq.length live_set /\
      (let obj = Seq.index live_set k in
       let wz = minor_wosize minor obj in
       fwd obj <> 0UL /\ wz > 0 /\ j < wz /\
       U64.v (fwd obj) % 8 == 0 /\
       U64.v (fwd obj) + (wz - 1) * 8 + 8 <= heap_size /\
       field_addr == U64.uint_to_t (U64.v (fwd obj) + j * 8)))
    (ensures (let obj = Seq.index live_set k in
              read_word major field_addr == minor_read_field minor obj j))
  = fields_match_minor_elim_lemma minor major fwd live_set idx k j field_addr
#pop-options

/// Helper: prove field preservation for a single (k, j) pair when k < idx.
#restart-solver
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --split_queries no"
private let promote_step_one_field_other
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat) (k: nat) (j: nat)
  : Lemma (requires
      idx < Seq.length live_set /\
      k < idx /\ k < Seq.length live_set /\
      (let obj = Seq.index live_set idx in
       let wz = minor_wosize minor obj in
       wz > 0 /\
       (promote_object minor major obj fp wz).new_addr <> 0UL) /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      fields_match_minor minor major fwd live_set idx /\
      (let obj_k = Seq.index live_set k in
       let wz_k = minor_wosize minor obj_k in
       fwd obj_k <> 0UL /\ wz_k > 0 /\ j < wz_k /\
       is_val_addr (fwd obj_k) /\
       U64.v (fwd obj_k) + j * 8 + 8 <= heap_size /\
       U64.v (fwd obj_k) + (wz_k - 1) * 8 + 8 <= heap_size /\
       Seq.mem ((fwd obj_k) <: obj_addr) (objects zero_addr major) /\
       U64.v (wosize_of_object ((fwd obj_k) <: obj_addr) major) >= wz_k /\
       AllocLemmas.chain_avoids major fp (fwd obj_k) (heap_size / U64.v mword) = true))
    (ensures
      (let obj = Seq.index live_set idx in
       let wz = minor_wosize minor obj in
       let obj_k = Seq.index live_set k in
       read_word (promote_object minor major obj fp wz).major_out
                 (U64.uint_to_t (U64.v (fwd obj_k) + j * 8)) ==
       minor_read_field minor obj_k j))
  = let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    let obj_k = Seq.index live_set k in
    let prev_addr : obj_addr = fwd obj_k in
    let field_addr : hp_addr = U64.uint_to_t (U64.v prev_addr + j * 8) in
    fields_match_minor_elim_lemma minor major fwd live_set idx k j field_addr;
    promote_object_preserves_one_field minor major obj fp wz prev_addr j
#pop-options

/// Assemble: use fields_match_minor_intro_by_proof with a proof function.
#restart-solver
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0 --split_queries always"
private let promote_step_fields_forall
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      idx < Seq.length live_set /\
      (let obj = Seq.index live_set idx in
       let wz = minor_wosize minor obj in
       wz > 0 /\
       (promote_object minor major obj fp wz).new_addr <> 0UL) /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      fields_match_minor minor major fwd live_set idx /\
      chain_all_inv minor major fp live_set fwd idx)
    (ensures (let obj = Seq.index live_set idx in
              let wz = minor_wosize minor obj in
              let res = promote_object minor major obj fp wz in
              let fwd' = extend_forwarding fwd obj res.new_addr in
              fields_match_minor minor res.major_out fwd' live_set (idx + 1)))
  = let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    let res = promote_object minor major obj fp wz in
    let fwd' = extend_forwarding fwd obj res.new_addr in
    chain_all_inv_elim minor major fp live_set fwd idx;
    let aux (k:nat) (j:nat) : Lemma
      (requires k < idx + 1 /\ k < Seq.length live_set /\
        (let obj_k = Seq.index live_set k in
         let wz_k = minor_wosize minor obj_k in
         fwd' obj_k <> 0UL /\ wz_k > 0 /\ j < wz_k /\
         dst_fields_valid (fwd' obj_k) wz_k /\ U64.v (fwd' obj_k) % 8 == 0))
      (ensures (let obj_k = Seq.index live_set k in
         read_word res.major_out (U64.uint_to_t (U64.v (fwd' obj_k) + j * 8)) ==
         minor_read_field minor obj_k j))
    = let obj_k = Seq.index live_set k in
      if obj_k = obj then
        promote_preserves_fields minor major obj fp wz
      else begin
        // k < idx+1 and k <> idx (since obj_k <> obj = Seq.index live_set idx) → k < idx
        assert (k <= idx);
        assert (Seq.index live_set k <> Seq.index live_set idx);
        assert (k <> idx);
        assert (k < idx);
        assert (fwd' obj_k == fwd obj_k);
        let wz_k = minor_wosize minor obj_k in
        assert (fwd obj_k <> 0UL);
        assert (U64.v (fwd obj_k) % 8 == 0);
        assert (U64.v (fwd obj_k) >= U64.v mword);
        is_val_addr_spec (fwd obj_k);
        assert (is_val_addr (fwd obj_k));
        assert (Seq.mem ((fwd obj_k) <: obj_addr) (objects zero_addr major));
        assert (U64.v (wosize_of_object ((fwd obj_k) <: obj_addr) major) >= wz_k);
        assert (AllocLemmas.chain_avoids major fp (fwd obj_k) (heap_size / U64.v mword) = true);
        assert (U64.v (fwd obj_k) + j * 8 + 8 <= heap_size);
        assert (U64.v (fwd obj_k) + (wz_k - 1) * 8 + 8 <= heap_size);
        promote_step_one_field_other minor major fp live_set fwd idx k j
      end
    in
    fields_match_minor_intro_by_proof minor res.major_out fwd' live_set (idx + 1) aux
#pop-options

/// Prove basic properties (wfh, fl_valid, fl_chain_terminates, fields_match_minor).
#restart-solver
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0 --split_queries always"
private let promote_step_preserves_basic
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      idx < Seq.length live_set /\
      (let obj = Seq.index live_set idx in
       let wz = minor_wosize minor obj in
       wz > 0 /\
       (promote_object minor major obj fp wz).new_addr <> 0UL) /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      fields_match_minor minor major fwd live_set idx /\
      chain_all_inv minor major fp live_set fwd idx)
    (ensures (let obj = Seq.index live_set idx in
              let wz = minor_wosize minor obj in
              let res = promote_object minor major obj fp wz in
              let fwd' = extend_forwarding fwd obj res.new_addr in
              well_formed_heap_part1 res.major_out /\
              AllocLemmas.fl_valid res.major_out res.fp_out (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates res.major_out res.fp_out (heap_size / U64.v mword) /\
              fields_match_minor minor res.major_out fwd' live_set (idx + 1)))
  = let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    let fuel : nat = heap_size / U64.v mword in
    chain_all_inv_elim minor major fp live_set fwd idx;
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
    AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
    let dst_obj : obj_addr = alloc_res.obj_out in
    chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
    // promote_object preserves all allocator invariants including set_promoted_tag
    promote_object_preserves_alloc_invariants minor major obj fp wz;
    promote_step_fields_forall minor major fp live_set fwd idx
#pop-options

/// For all previous k, chain_avoids is preserved through promote_object.
#restart-solver
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"
private let promote_step_chain_forall
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      idx < Seq.length live_set /\
      (let obj = Seq.index live_set idx in
       let wz = minor_wosize minor obj in
       wz > 0 /\
       (promote_object minor major obj fp wz).new_addr <> 0UL) /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_all_inv minor major fp live_set fwd idx)
    (ensures (let obj = Seq.index live_set idx in
              let wz = minor_wosize minor obj in
              let res = promote_object minor major obj fp wz in
              let fuel : nat = heap_size / U64.v mword in
              forall (k:nat). k < idx /\ k < Seq.length live_set ==>
                (let prev_obj = Seq.index live_set k in
                 let prev_wz = minor_wosize minor prev_obj in
                 fwd prev_obj <> 0UL /\ prev_wz > 0 /\ is_val_addr (fwd prev_obj) /\
                 Seq.mem ((fwd prev_obj) <: obj_addr) (objects zero_addr major) /\
                 U64.v (wosize_of_object ((fwd prev_obj) <: obj_addr) major) >= prev_wz /\
                 AllocLemmas.chain_avoids major fp (fwd prev_obj) (heap_size / U64.v mword) = true ==>
                 AllocLemmas.chain_avoids res.major_out res.fp_out (fwd prev_obj) fuel = true)))
  = let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    chain_all_inv_elim minor major fp live_set fwd idx;
    let aux_chain (k:nat{k < idx /\ k < Seq.length live_set}) : Lemma
      (ensures (let prev_obj = Seq.index live_set k in
                let prev_wz = minor_wosize minor prev_obj in
                fwd prev_obj <> 0UL /\ prev_wz > 0 /\ is_val_addr (fwd prev_obj) /\
                Seq.mem ((fwd prev_obj) <: obj_addr) (objects zero_addr major) /\
                U64.v (wosize_of_object ((fwd prev_obj) <: obj_addr) major) >= prev_wz /\
                AllocLemmas.chain_avoids major fp (fwd prev_obj) (heap_size / U64.v mword) = true ==>
                AllocLemmas.chain_avoids (promote_object minor major obj fp wz).major_out
                                         (promote_object minor major obj fp wz).fp_out
                                         (fwd prev_obj) (heap_size / U64.v mword) = true))
    = let prev_obj = Seq.index live_set k in
      Classical.move_requires (promote_object_preserves_chain_avoids minor major obj fp wz) (fwd prev_obj)
    in
    FStar.Classical.forall_intro aux_chain
#pop-options

/// Wosize of objects that avoid the chain is preserved through promote_object.
#restart-solver
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let promote_object_wosize_preserved
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wz: nat{wz > 0}) (other: obj_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      Seq.mem other (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp other (heap_size / U64.v mword) = true)
    (ensures
      wosize_of_object other (promote_object minor major obj fp wz).major_out ==
      wosize_of_object other major)
  = let fuel : nat = heap_size / U64.v mword in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
    let new_major = alloc_res.heap_out in
    let new_addr = alloc_res.obj_out in
    assert (new_addr <> 0UL);
    GC.Gen.AllocProps.alloc_spec_obj_ne_excl major fp wz other;
    GC.Gen.AllocProps.alloc_spec_read_header_other_part1 major fp wz other;
    assert (read_word new_major (hd_address other) == read_word major (hd_address other));
    GC.Gen.AllocProps.alloc_search_obj_in_objects_pre_part1 major fp zero_addr fp
      (if wz = 0 then 1 else wz) fuel;
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
    assert (U64.v new_addr >= U64.v mword);
    let dst_obj : obj_addr = new_addr in
    GC.Gen.AllocProps.alloc_spec_obj_wosize_pre_part1 major fp wz;
    assert (U64.v (wosize_of_object dst_obj major) >= wz);
    hd_address_spec other;
    hd_address_spec dst_obj;
    let a = hd_address other in
    // dst_obj is in objects (from alloc_search_obj_in_objects_pre_part1 + new_addr <> 0UL)
    assert (Seq.mem dst_obj (objects zero_addr major));
    // Use wfh_part1_obj_bound to get dst_obj + wosize*8 <= heap_size
    wfh_part1_obj_bound major dst_obj;
    assert (U64.v dst_obj + wz * 8 <= heap_size);
    if U64.v other < U64.v new_addr then begin
      objects_separated zero_addr major other dst_obj;
      // Bridge: a + 8 = other <= dst_obj <= dst_obj + k*8 for all k
      assert (U64.v a + 8 = U64.v other);
      assert (U64.v other <= U64.v dst_obj);
      copy_fields_preserves_other minor new_major obj dst_obj 0 wz a;
      // a < dst_obj <= dst_obj + wz*8 (since wz >= 1), so a <> dst_obj + wz*8
      assert (U64.v a < U64.v dst_obj + wz * 8)
    end else begin
      objects_separated zero_addr major dst_obj other;
      // objects_separated: other > dst_obj + wosize_of_object_as_wosize(dst_obj,major)*8
      // wosize_of_object_as_wosize = wosize_of_object (with bound proof)
      wosize_of_object_spec dst_obj major;
      let ws = U64.v (wosize_of_object dst_obj major) in
      assert (U64.v other > U64.v dst_obj + ws * 8);
      assert (ws >= wz);
      // Alignment: other % 8 == 0, (dst_obj + ws*8) % 8 == 0, other > dst_obj + ws*8
      // ==> other >= dst_obj + ws*8 + 8 >= dst_obj + wz*8 + 8
      assert (U64.v other % 8 == 0);
      assert (U64.v dst_obj % 8 == 0);
      // Explicit: other - (dst_obj + ws*8) > 0 and is a multiple of 8, so >= 8
      assert ((U64.v other - (U64.v dst_obj + ws * 8)) % 8 == 0);
      assert (U64.v other >= U64.v dst_obj + ws * 8 + 8);
      assert (U64.v other >= U64.v dst_obj + wz * 8 + 8);
      // Now: a = other - 8, so a >= dst_obj + wz*8
      // For k < wz: dst_obj + k*8 + 8 <= dst_obj + (wz-1)*8 + 8 = dst_obj + wz*8 <= a
      assert (U64.v a = U64.v other - 8);
      assert (U64.v a >= U64.v dst_obj + wz * 8);
      copy_fields_preserves_other minor new_major obj dst_obj 0 wz a
    end;
    // Bridge: padding + set_promoted_tag preserve header of other (other ≠ dst_obj)
    promote_object_success minor major obj fp wz;
    let copied = copy_fields minor new_major obj dst_obj 0 wz in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    hd_address_injective other dst_obj;
    // Establish dst_fields_valid for copy_fields_frame
    dst_fields_valid_from_bounds dst_obj wz;
    // Padding frame for header of other
    copy_fields_frame minor new_major obj dst_obj 0 wz (hd_address dst_obj);
    wosize_of_object_spec dst_obj new_major;
    wosize_of_object_spec dst_obj copied;
    let actual_wz = U64.v (wosize_of_object dst_obj copied) in
    if actual_wz <= wz then
      zero_promote_padding_noop copied dst_obj wz
    else begin
      // Need: a <> dst_obj + wz * 8 for zero_promote_padding_frame.
      // Two cases based on relative position of other and dst_obj:
      if U64.v other < U64.v dst_obj then
        // a = other - 8 < other <= dst_obj, and dst_obj + wz*8 >= dst_obj (wz>=1)
        // So a < dst_obj <= dst_obj + wz*8
        assert (U64.v a < U64.v dst_obj + wz * 8)
      else begin
        // other > dst_obj. Use objects_separated on new_major where wosize(dst_obj) = actual_wz > wz
        AllocLemmas.alloc_spec_preserves_objects_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
        objects_separated zero_addr new_major dst_obj other;
        // objects_separated: other > dst_obj + actual_wz*8 >= dst_obj + (wz+1)*8
        // alignment: a = other - 8 >= dst_obj + actual_wz*8 >= dst_obj + wz*8 + 8
        wosize_of_object_spec dst_obj new_major;
        assert (U64.v other > U64.v dst_obj + actual_wz * 8);
        assert (U64.v a > U64.v dst_obj + wz * 8)
      end;
      zero_promote_padding_frame copied dst_obj wz a
    end;
    let padded = zero_promote_padding copied dst_obj wz in
    set_promoted_tag_read_frame padded dst_obj tag a;
    wosize_of_object_spec other major;
    wosize_of_object_spec other (promote_object minor major obj fp wz).major_out
#pop-options

/// Wosize of the newly allocated dst_obj is preserved through copy_fields
#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let promote_object_wosize_self
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wz: nat{wz > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (GC.Spec.Allocator.alloc_spec major fp wz).obj_out <> 0UL /\
      is_val_addr (GC.Spec.Allocator.alloc_spec major fp wz).obj_out)
    (ensures (let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
              let dst_obj : obj_addr = alloc_res.obj_out in
              let result = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
              U64.v (wosize_of_object dst_obj result) >= wz))
  = let fuel : nat = heap_size / U64.v mword in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
    GC.Gen.AllocProps.alloc_search_obj_in_objects_pre_part1 major fp zero_addr fp
      (if wz = 0 then 1 else wz) fuel;
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    assert (U64.v alloc_res.obj_out >= U64.v mword);
    let dst_obj : obj_addr = alloc_res.obj_out in
    assert (well_formed_heap_part1 alloc_res.heap_out);
    assert (Seq.mem dst_obj (objects zero_addr alloc_res.heap_out));
    hd_address_spec dst_obj;
    wosize_of_object_spec dst_obj alloc_res.heap_out;
    assert (U64.v dst_obj + U64.v (wosize_of_object dst_obj alloc_res.heap_out) * 8 <= heap_size);
    assert (U64.v dst_obj + (wz - 1) * 8 + 8 <= heap_size);
    copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz (hd_address dst_obj);
    wosize_of_object_spec dst_obj (copy_fields minor alloc_res.heap_out obj dst_obj 0 wz)
#pop-options

/// Helper for promote_step: for a previously promoted object, chain_avoids
/// and wosize are preserved through the current promotion step.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let promote_step_chain_k
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wz: nat{wz > 0}) (fwd_ok: obj_addr) (wz_k: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      Seq.mem fwd_ok (objects zero_addr major) /\
      U64.v (wosize_of_object fwd_ok major) >= wz_k /\
      U64.v (wosize_of_object fwd_ok major) >= 1 /\
      AllocLemmas.chain_avoids major fp fwd_ok (heap_size / U64.v mword) = true /\
      (promote_object minor major obj fp wz).new_addr <> 0UL)
    (ensures
      (let res = promote_object minor major obj fp wz in
       Seq.mem fwd_ok (objects zero_addr res.major_out) /\
       U64.v (wosize_of_object fwd_ok res.major_out) >= wz_k /\
       AllocLemmas.chain_avoids res.major_out res.fp_out fwd_ok (heap_size / U64.v mword) = true))
  = promote_object_wosize_preserved minor major obj fp wz fwd_ok;
    promote_object_preserves_chain_avoids minor major obj fp wz fwd_ok;
    promote_object_preserves_objects_part1 minor major obj fp wz
#pop-options

/// set_promoted_tag preserves read_word at object addresses ≠ dst_obj.
/// Used to transfer chain_avoids through set_promoted_tag.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0 --split_queries always"
private let set_tag_preserves_read_at_obj_step
  (major: heap) (dst_obj: obj_addr) (tag: nat{tag < 256})
  (a: obj_addr)
  : Lemma (requires Seq.mem a (objects zero_addr major) /\
                    Seq.mem dst_obj (objects zero_addr major) /\
                    U64.v (wosize_of_object a major) >= 1 /\
                    U64.v (hd_address a) + 16 <= heap_size /\
                    (a <: U64.t) <> (dst_obj <: U64.t))
          (ensures read_word (set_promoted_tag major dst_obj tag) a ==
                   read_word major a)
  = hd_address_spec a;
    hd_address_spec dst_obj;
    if U64.v a < U64.v dst_obj then
      objects_separated zero_addr major a dst_obj
    else ();
    set_promoted_tag_read_frame major dst_obj tag (a <: hp_addr)
#pop-options

/// chain_avoids for the newly allocated object is preserved through
/// the full promote_object (alloc + copy_fields + set_promoted_tag).
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0 --split_queries always"
private let promote_object_chain_avoids_self
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wz: nat{wz > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (promote_object minor major obj fp wz).new_addr <> 0UL)
    (ensures
      (let res = promote_object minor major obj fp wz in
       let fuel = heap_size / U64.v mword in
       AllocLemmas.chain_avoids res.major_out res.fp_out
         res.new_addr fuel = true))
  = let fuel = heap_size / U64.v mword in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    let dst_obj : obj_addr = alloc_res.obj_out in
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
    AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
    copy_fields_preserves_chain_avoids_self minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
    // Intermediate heap after copy_fields
    assert (well_formed_heap_part1 alloc_res.heap_out);
    assert (Seq.mem dst_obj (objects zero_addr alloc_res.heap_out));
    assert (U64.v (wosize_of_object dst_obj alloc_res.heap_out) >= wz);
    assert (AllocLemmas.fl_valid alloc_res.heap_out alloc_res.fp_out fuel);
    assert (AllocLemmas.fl_chain_terminates alloc_res.heap_out alloc_res.fp_out fuel);
    assert (not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel);
    copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
    copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
    copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
    copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
    let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
    let mtag = minor_tag minor obj in
    minor_tag_bound minor obj;
    promote_object_success minor major obj fp wz;
    // chain_avoids through zero_promote_padding
    zero_promote_padding_preserves_alloc_invariants copied dst_obj wz alloc_res.fp_out;
    let padded = zero_promote_padding copied dst_obj wz in
    // chain_avoids through set_promoted_tag
    set_promoted_tag_preserves_alloc_invariants padded dst_obj mtag alloc_res.fp_out;
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (set_tag_preserves_read_at_obj_step padded dst_obj mtag));
    // Transfer chain_avoids from copied through padding
    // Establish wosize(dst_obj, copied) >= wz for pad_read_helper
    wfh_part1_obj_bound alloc_res.heap_out dst_obj;
    dst_fields_valid_from_bounds dst_obj wz;
    hd_address_spec dst_obj;
    copy_fields_frame minor alloc_res.heap_out obj dst_obj 0 wz (hd_address dst_obj);
    wosize_of_object_spec dst_obj alloc_res.heap_out;
    wosize_of_object_spec dst_obj copied;
    assert (Seq.mem dst_obj (objects zero_addr copied));
    assert (U64.v (wosize_of_object dst_obj copied) >= wz);
    let pad_read_helper (a: obj_addr)
      : Lemma (requires Seq.mem a (objects zero_addr copied) /\
                        Seq.mem dst_obj (objects zero_addr copied) /\
                        U64.v (wosize_of_object dst_obj copied) >= wz /\
                        U64.v (wosize_of_object a copied) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size)
              (ensures read_word padded a == read_word copied a)
      = if (a <: U64.t) = (dst_obj <: U64.t) then
          // a == dst_obj: pad_pos = dst + wz*8, reading at dst. Since wz >= 1, they differ.
          zero_promote_padding_frame copied dst_obj wz (a <: hp_addr)
        else begin
          hd_address_spec a;
          hd_address_spec dst_obj;
          if U64.v a < U64.v dst_obj then begin
            objects_separated zero_addr copied a dst_obj;
            // a < dst_obj <= dst_obj + wz*8 (wz >= 1)
            assert (U64.v (a <: U64.t) < U64.v dst_obj + wz * 8)
          end else begin
            objects_separated zero_addr copied dst_obj a;
            // a > dst_obj + ws*8 where ws = wosize_of_object_as_wosize dst_obj copied >= wz
            // Hence a > dst_obj + wz*8
            assert (U64.v (a <: U64.t) > U64.v dst_obj + wz * 8)
          end;
          zero_promote_padding_frame copied dst_obj wz (a <: hp_addr)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires pad_read_helper);
    AllocLemmas.chain_avoids_transfer copied padded
      alloc_res.fp_out dst_obj fuel;
    AllocLemmas.chain_avoids_transfer padded (set_promoted_tag padded dst_obj mtag)
      alloc_res.fp_out dst_obj fuel
#pop-options

/// set_promoted_tag preserves wosize_of_object at the same obj_addr.
/// Key: set_promoted_tag writes makeHeader with the SAME getWosize, so the
/// wosize field (bits 10-63) of the header is unchanged.
#restart-solver
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let set_promoted_tag_preserves_wosize_self
  (h: heap) (obj: obj_addr) (tag: nat{tag < 256})
  : Lemma (requires Seq.mem obj (objects zero_addr h))
          (ensures wosize_of_object obj (set_promoted_tag h obj tag) ==
                   wosize_of_object obj h)
  = set_promoted_tag_unfold h obj tag;
    wosize_of_object_spec obj h;
    let hdr = read_word h (hd_address obj) in
    let new_hdr = makeHeader (getWosize hdr) White (U64.uint_to_t tag) in
    read_write_same h (hd_address obj) new_hdr;
    makeHeader_getWosize (getWosize hdr) White (U64.uint_to_t tag);
    wosize_of_object_spec obj (set_promoted_tag h obj tag)
#pop-options

/// Wosize of the promoted object through the FULL promote_object pipeline
/// (alloc + copy_fields + set_promoted_tag).
#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let promote_object_wosize_self_full
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wz: nat{wz > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (promote_object minor major obj fp wz).new_addr <> 0UL)
    (ensures (let res = promote_object minor major obj fp wz in
              is_val_addr res.new_addr /\
              U64.v (wosize_of_object (res.new_addr <: obj_addr) res.major_out) >= wz))
  = let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
    let dst_obj : obj_addr = alloc_res.obj_out in
    // Establish alloc_res.heap_out properties FIRST
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    // Wosize through copy_fields
    promote_object_wosize_self minor major obj fp wz;
    // Objects preserved through copy_fields
    copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
    let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
    // Wosize preserved through zero_promote_padding (writes at field wz, not header)
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
    wfh_part1_obj_bound alloc_res.heap_out dst_obj;
    dst_fields_valid_from_bounds dst_obj wz;
    hd_address_spec dst_obj;
    zero_promote_padding_frame copied dst_obj wz (hd_address dst_obj);
    wosize_of_object_spec dst_obj copied;
    let padded = zero_promote_padding copied dst_obj wz in
    wosize_of_object_spec dst_obj padded;
    // Objects preserved through zero_promote_padding
    assert (Seq.mem dst_obj (objects zero_addr copied));
    zero_promote_padding_preserves_objects copied dst_obj wz;
    assert (Seq.mem dst_obj (objects zero_addr padded));
    // Wosize preserved through set_promoted_tag
    promote_object_success minor major obj fp wz;
    let mtag = minor_tag minor obj in
    minor_tag_bound minor obj;
    set_promoted_tag_preserves_wosize_self padded dst_obj mtag
#pop-options

/// Single-k proof for chain_all_inv_intro: proves the body of the forall
/// for a specific index k. TOP-LEVEL to avoid context pollution.
#restart-solver
#push-options "--z3rlimit 150 --fuel 0 --ifuel 0 --split_queries always"
private let promote_step_chain_one_k
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  (k: nat)
  : Lemma (requires
      idx < Seq.length live_set /\
      k < idx + 1 /\ k < Seq.length live_set /\
      (let obj = Seq.index live_set idx in
       let wz = minor_wosize minor obj in
       wz > 0 /\
       (promote_object minor major obj fp wz).new_addr <> 0UL) /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_all_inv minor major fp live_set fwd idx)
    (ensures (let obj = Seq.index live_set idx in
              let wz = minor_wosize minor obj in
              let res = promote_object minor major obj fp wz in
              let fwd' = extend_forwarding fwd obj res.new_addr in
              let ok = Seq.index live_set k in
              let wz_k = minor_wosize minor ok in
              fwd' ok <> 0UL /\ wz_k > 0 /\ is_val_addr (fwd' ok) ==>
              (Seq.mem ((fwd' ok) <: obj_addr) (objects zero_addr res.major_out) /\
               U64.v (wosize_of_object ((fwd' ok) <: obj_addr) res.major_out) >= wz_k /\
               AllocLemmas.chain_avoids res.major_out res.fp_out (fwd' ok) (heap_size / U64.v mword) = true)))
  = let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    let ok = Seq.index live_set k in
    let res = promote_object minor major obj fp wz in
    let fwd' = extend_forwarding fwd obj res.new_addr in
    if ok = obj then begin
      promote_object_chain_avoids_self minor major obj fp wz;
      promote_object_wosize_self_full minor major obj fp wz;
      // Establish that res.new_addr is in objects of the final heap:
      // alloc puts it in alloc_res.heap_out; copy_fields and set_promoted_tag preserve objects
      let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
      GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
      GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
      GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
      let dst_obj : obj_addr = alloc_res.obj_out in
      copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
      promote_object_success minor major obj fp wz;
      let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
      // zero_promote_padding preserves objects
      AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
      copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
      zero_promote_padding_preserves_objects copied dst_obj wz;
      let padded = zero_promote_padding copied dst_obj wz in
      let mtag = minor_tag minor obj in
      minor_tag_bound minor obj;
      set_promoted_tag_preserves_objects padded dst_obj mtag;
      assert (Seq.mem dst_obj (objects zero_addr res.major_out))
    end
    else begin
      chain_all_inv_elim minor major fp live_set fwd idx;
      let wz_k = minor_wosize minor ok in
      if fwd ok <> 0UL && wz_k > 0 && is_val_addr (fwd ok) then begin
        assert (Seq.mem ((fwd ok) <: obj_addr) (objects zero_addr major));
        assert (U64.v (wosize_of_object ((fwd ok) <: obj_addr) major) >= wz_k);
        assert (AllocLemmas.chain_avoids major fp (fwd ok) (heap_size / U64.v mword) = true);
        promote_step_chain_k minor major obj fp wz ((fwd ok) <: obj_addr) wz_k
      end else ()
    end
#pop-options

/// Establish chain_all_inv for idx+1 after promote_object.
/// Separated from promote_step_preserves_invariant to keep the solver context
/// clean (avoiding the "incomplete quantifiers" issue from context pollution).
#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let promote_step_establish_chain_all
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      idx < Seq.length live_set /\
      (let obj = Seq.index live_set idx in
       let wz = minor_wosize minor obj in
       wz > 0 /\
       (promote_object minor major obj fp wz).new_addr <> 0UL) /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_all_inv minor major fp live_set fwd idx)
    (ensures (let obj = Seq.index live_set idx in
              let wz = minor_wosize minor obj in
              let res = promote_object minor major obj fp wz in
              let fwd' = extend_forwarding fwd obj res.new_addr in
              chain_all_inv minor res.major_out res.fp_out live_set fwd' (idx + 1)))
  = let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    let res = promote_object minor major obj fp wz in
    let fwd' = extend_forwarding fwd obj res.new_addr in
    let step_k (k:nat{k < idx + 1 /\ k < Seq.length live_set}) : Lemma
      (ensures (let ok = Seq.index live_set k in
                let wz_k = minor_wosize minor ok in
                fwd' ok <> 0UL /\ wz_k > 0 /\ is_val_addr (fwd' ok) ==>
                (Seq.mem ((fwd' ok) <: obj_addr) (objects zero_addr res.major_out) /\
                 U64.v (wosize_of_object ((fwd' ok) <: obj_addr) res.major_out) >= wz_k /\
                 AllocLemmas.chain_avoids res.major_out res.fp_out (fwd' ok) (heap_size / U64.v mword) = true)))
    = promote_step_chain_one_k minor major fp live_set fwd idx k
    in
    FStar.Classical.forall_intro step_k;
    chain_all_inv_intro minor res.major_out res.fp_out live_set fwd' (idx + 1)
#pop-options

/// Top-level step: combines basic + chain_all_inv
#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let promote_step_preserves_invariant
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      idx < Seq.length live_set /\
      (let obj = Seq.index live_set idx in
       let wz = minor_wosize minor obj in
       wz > 0 /\
       (promote_object minor major obj fp wz).new_addr <> 0UL) /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      fields_match_minor minor major fwd live_set idx /\
      chain_all_inv minor major fp live_set fwd idx)
    (ensures (let obj = Seq.index live_set idx in
              let wz = minor_wosize minor obj in
              let res = promote_object minor major obj fp wz in
              let fwd' = extend_forwarding fwd obj res.new_addr in
              well_formed_heap_part1 res.major_out /\
              AllocLemmas.fl_valid res.major_out res.fp_out (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates res.major_out res.fp_out (heap_size / U64.v mword) /\
              fields_match_minor minor res.major_out fwd' live_set (idx + 1) /\
              chain_all_inv minor res.major_out res.fp_out live_set fwd' (idx + 1)))
  = promote_step_preserves_basic minor major fp live_set fwd idx;
    promote_step_establish_chain_all minor major fp live_set fwd idx
#pop-options
