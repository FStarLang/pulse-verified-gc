/// ---------------------------------------------------------------------------
/// GC.Gen.Cheney — Implementation of Cheney-style BFS copying collector spec
/// ---------------------------------------------------------------------------

module GC.Gen.Cheney

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Object = GC.Spec.Object
module Heap = GC.Spec.Heap

/// ---------------------------------------------------------------------------
/// cheney_forward_normal: forward a single non-infix object
/// ---------------------------------------------------------------------------

let cheney_forward_normal (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then cs
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then cs
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then cs  // OOM — leave state unchanged
      else
        { cs_major = res.major_out;
          cs_fp    = res.fp_out;
          cs_fwd   = extend_forwarding cs.cs_fwd addr res.new_addr;
          cs_queue = Seq.append cs.cs_queue (Seq.create 1 addr) }

/// ---------------------------------------------------------------------------
/// cheney_forward_one: infix-aware forwarding
/// ---------------------------------------------------------------------------

let cheney_forward_one (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  =
  if cs.cs_fwd addr <> 0UL then cs
  else if is_infix_in_minor minor addr then
    let parent = infix_parent minor addr in
    let cs' = cheney_forward_normal minor cs parent in
    if cs'.cs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then
      let delta = U64.v addr - U64.v parent in
      { cs' with cs_fwd = extend_forwarding cs'.cs_fwd addr
                             (U64.uint_to_t (U64.v (cs'.cs_fwd parent) + delta)) }
    else cs'
  else
    cheney_forward_normal minor cs addr

/// Unfold lemmas for cheney_forward_normal

let cheney_forward_normal_noop (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

let cheney_forward_normal_noop_wz0 (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

let cheney_forward_normal_noop_oom (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

let cheney_forward_normal_success (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

/// For any y <> addr, cheney_forward_normal on addr leaves cs_fwd y unchanged
let cheney_forward_normal_other_fwd (minor: minor_state) (cs: cheney_state) (addr: U64.t) (y: U64.t)
  = ()

/// Unfold lemmas for cheney_forward_one (infix-aware)
/// (`--fuel 0`: `cheney_forward_one` is not recursive; with fuel, Z3 5.1.0
/// unrolls the bitvector definitions under `infix_parent` and times out.)
#push-options "--fuel 0 --ifuel 0"

let cheney_forward_one_noop (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

let cheney_forward_one_normal (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

let cheney_forward_one_infix (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

/// For any y <> addr, the infix case preserves cs_fwd y from the parent forwarding
let cheney_forward_one_infix_fwd (minor: minor_state) (cs: cheney_state) (addr: U64.t) (y: U64.t)
  = ()

/// In the infix case, if the guard passes, the stored value for addr is parent_fwd + delta < heap_size
let cheney_forward_one_infix_bounded (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

/// In the infix case, when the bounded guard fails, cheney_forward_one returns cs'
let cheney_forward_one_infix_guard_fail (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

/// In the infix case, when the bounded guard passes, the result's cs_fwd is
/// extend_forwarding cs'.cs_fwd addr val, where val = parent_fwd + delta
let cheney_forward_one_infix_guard_pass (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()
#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_fields: forward all children of an object
/// ---------------------------------------------------------------------------

let rec cheney_forward_fields (minor: minor_state) (cs: cheney_state)
                              (parent: U64.t) (idx: nat) (wosize: nat)
  : GTot cheney_state
    (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then cs
  else
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields minor cs' parent (idx + 1) wosize

let cheney_forward_fields_base
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  = ()

let cheney_forward_fields_step
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  = ()

/// ---------------------------------------------------------------------------
/// cheney_forward_roots: forward all roots
/// ---------------------------------------------------------------------------

let rec cheney_forward_roots (minor: minor_state) (cs: cheney_state)
                             (roots: seq U64.t) (idx: nat)
  : GTot cheney_state
    (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then cs
  else
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots minor cs' roots (idx + 1)

let cheney_forward_roots_base
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  = ()

let cheney_forward_roots_step
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  = ()

/// ---------------------------------------------------------------------------
/// cheney_scan: BFS scan loop
/// ---------------------------------------------------------------------------

let rec cheney_scan (minor: minor_state) (cs: cheney_state)
                    (scan: nat) (fuel: nat)
  : GTot cheney_state
    (decreases fuel)
  =
  if fuel < 1 || scan >= Seq.length cs.cs_queue then cs
  else
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_scan_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_scan minor cs' (scan + 1) (fuel - 1)

let cheney_scan_base
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  = ()

let cheney_scan_step
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  = ()

/// ---------------------------------------------------------------------------
/// cheney_fuel: sufficient fuel for BFS completion
/// ---------------------------------------------------------------------------

/// Each minor object is forwarded at most once (fwd prevents re-enqueue).
/// So the total queue length is bounded by |minor_objects|.
/// Each scan step advances scan by 1, so fuel = |minor_objects| suffices.
let cheney_fuel (minor: minor_state) : GTot nat =
  Seq.length (minor_objects minor)

let cheney_fuel_eq (minor: minor_state)
  = ()

/// ---------------------------------------------------------------------------
/// update_walk_preserves_fl_valid
/// ---------------------------------------------------------------------------

/// Key insight: the pointer update only modifies field data of non-blue objects.
/// Blue objects (free-list entries) are skipped entirely by the update.
/// Therefore, free-list structure (headers + next pointers in field 0 of blue objects)
/// is unchanged, preserving fl_valid.

/// Recursive helper: by induction on fuel, show fl_valid and fl_chain_terminates
/// are preserved in the updated heap.  The avoids hypothesis generalises
/// chain_objects_blue to arbitrary fuel so that it shrinks in lock-step with
/// fl_valid / fl_chain_terminates.

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let rec update_preserves_fl_valid_aux
  (major: heap) (upd: obj_addr -> GTot bool) (fwd: forwarding_map) (fp: U64.t) (fuel: nat)
  : Lemma
    (requires
      blocks_fit major /\
      walk_ok major upd /\
      AllocLemmas.fl_valid major fp fuel /\
      AllocLemmas.fl_chain_terminates major fp fuel /\
      (forall (obj: obj_addr).
        Seq.mem obj (objects zero_addr major) /\ Object.is_blue obj major = false ==>
        AllocLemmas.chain_avoids major fp obj fuel = true))
    (ensures (let m' = update_walk major upd fwd in
              AllocLemmas.fl_valid m' fp fuel /\
              AllocLemmas.fl_chain_terminates m' fp fuel))
    (decreases fuel)
  =
  let m' = update_walk major upd fwd in
  update_walk_preserves_objects major upd fwd;

  // Terminal fp: fl_valid and fl_chain_terminates hold for any heap/fuel
  if fp = 0UL || U64.v fp < U64.v mword || U64.v fp >= heap_size || U64.v fp % U64.v mword <> 0
  then begin
    (if fuel < 1 then AllocLemmas.fl_valid_zero m' fp
     else AllocLemmas.fl_valid_terminal m' fp fuel);
    AllocLemmas.fl_chain_terminates_terminal m' fp fuel
  end
  // fuel = 0, valid fp: fl_chain_terminates major fp 0 = false (contradicting precondition)
  else if fuel < 1 then
    AllocLemmas.fl_chain_terminates_valid_zero major fp
  else begin
    // Inductive case: fuel > 0, valid fp
    let fp_obj : obj_addr = fp in

    // Step 1: chain_avoids major fp fp fuel = false (by contradiction)
    // If chain_avoids were true, chain_avoids_head_ne would give fp ≠ fp
    (if AllocLemmas.chain_avoids major fp fp fuel then
       AllocLemmas.chain_avoids_head_ne major fp fp fuel
     else ());

    // Step 2: fp is blue (contrapositive of the forall)
    // mem fp objects ∧ ¬is_blue  ⟹  chain_avoids = true  (from forall)
    // But chain_avoids = false  ⟹  contradiction
    // Therefore is_blue = true
    AllocLemmas.fl_valid_gives_mem major fp fuel;

    // Step 3: header preserved → wosize preserved
    update_walk_preserves_header major upd fwd fp_obj;
    Object.wosize_of_object_spec fp_obj m';
    Object.wosize_of_object_spec fp_obj major;

    // Step 4: wosize >= 1 (from fl_valid)
    AllocLemmas.fl_valid_gives_wosize major fp fuel;

    // Step 5: hd_address arithmetic
    Heap.hd_address_spec fp_obj;
    let hd = Heap.hd_address fp_obj in

    if U64.v hd + 16 > heap_size then begin
      // hd + 16 > heap_size: implication premises false → use intro lemmas
      AllocLemmas.fl_valid_step m' fp fuel;
      AllocLemmas.fl_chain_terminates_step m' fp fuel
    end
    else begin
      // hd + 16 ≤ heap_size

      // Step 6: field 0 preserved (blue object, j = 0)
      update_walk_preserves_skipped_field major upd fwd fp_obj 0;

      // Step 7: Eliminate fl_valid/fl_chain_terminates on major
      AllocLemmas.fl_valid_elim major fp fuel;
      AllocLemmas.fl_chain_terminates_elim major fp fuel;
      let next_fp = Heap.read_word major fp in

      // Step 8: avoids hypothesis for tail (∀ non-blue obj, chain_avoids at next_fp)
      let avoids_next (obj: obj_addr) : Lemma
        (requires Seq.mem obj (objects zero_addr major) /\ Object.is_blue obj major = false)
        (ensures AllocLemmas.chain_avoids major next_fp obj (fuel - 1) = true)
        = AllocLemmas.chain_avoids_tail major fp obj fuel
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires avoids_next);

      // Step 9: recurse on next_fp with fuel - 1
      update_preserves_fl_valid_aux major upd fwd next_fp (fuel - 1);

      // Step 10: Build fl_valid and fl_chain_terminates on m'
      AllocLemmas.fl_valid_step m' fp fuel;
      AllocLemmas.fl_chain_terminates_step m' fp fuel
    end
  end

#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

let update_walk_preserves_fl_valid
  (major: heap) (upd: obj_addr -> GTot bool) (fwd: forwarding_map) (fp: U64.t)
  =
  let fuel = heap_words in
  reveal_opaque (`%chain_objects_blue) chain_objects_blue;
  update_preserves_fl_valid_aux major upd fwd fp fuel

#pop-options

