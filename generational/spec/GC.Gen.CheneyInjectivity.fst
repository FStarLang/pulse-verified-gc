/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyInjectivity — Implementation
/// ---------------------------------------------------------------------------

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
module AllocProps = GC.Gen.AllocProps
module ReadOther = GC.Gen.PromoteUpdate.PromoteFields.ReadOther
module BlueProm = GC.Gen.PromoteUpdate.BlueProm
module PromStep = GC.Gen.PromoteUpdate.PromoteFields.Step

/// ---------------------------------------------------------------------------
/// Helper: extend_forwarding preserves injectivity
/// ---------------------------------------------------------------------------

/// If fwd is injective, fwd(addr) == 0 (addr is fresh), and new_addr is not
/// in the range of fwd, then extend_forwarding fwd addr new_addr is injective.
private let extend_forwarding_preserves_injective
  (fwd: forwarding_map) (addr: U64.t) (new_addr: U64.t)
  : Lemma
    (requires
      fwd_injective fwd /\
      fwd addr == 0UL /\
      new_addr <> 0UL /\
      (forall (x: U64.t). fwd x <> 0UL ==> fwd x <> new_addr))
    (ensures fwd_injective (extend_forwarding fwd addr new_addr))
  = let fwd' = extend_forwarding fwd addr new_addr in
    let aux (a b: U64.t) : Lemma
      (requires fwd' a <> 0UL /\ fwd' b <> 0UL /\ fwd' a == fwd' b)
      (ensures a == b)
    = // extend_forwarding maps addr→new_addr, all others→fwd(others)
      // Definition: fun x -> if x = addr then new_addr else fwd x
      if a = addr then begin
        // fwd'(a) = new_addr
        if b = addr then () // a = b = addr
        else begin
          // fwd'(b) = fwd(b), and fwd(b) = new_addr contradicts hypothesis
          assert (fwd b == new_addr);
          assert (fwd b <> 0UL);
          ()  // contradiction: fwd b <> new_addr by hypothesis
        end
      end else begin
        // fwd'(a) = fwd(a)
        if b = addr then begin
          // fwd'(b) = new_addr = fwd(a), contradicts hypothesis
          assert (fwd a == new_addr);
          assert (fwd a <> 0UL);
          ()  // contradiction
        end else begin
          // Both fwd'(a) = fwd(a) and fwd'(b) = fwd(b), use original injectivity
          ()
        end
      end
    in
    Classical.forall_intro_2 (fun a -> Classical.move_requires (aux a))


/// ---------------------------------------------------------------------------
/// cheney_forward_one preserves injectivity invariant
/// ---------------------------------------------------------------------------

/// Helper for `a = addr` case of fwd_targets_avoid_chain preservation
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let fwd_targets_new_addr
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires
      cheney_inj_invariant cs /\
      Seq.mem addr (minor_objects minor) /\
      cs.cs_fwd addr = 0UL /\
      minor_wosize minor addr > 0 /\
      (promote_object minor cs.cs_major addr cs.cs_fp (minor_wosize minor addr)).new_addr <> 0UL)
    (ensures (let wz = minor_wosize minor addr in
              let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
              let new_addr = res.new_addr in
              U64.v new_addr >= U64.v mword /\
              U64.v new_addr < heap_size /\
              U64.v new_addr % U64.v mword == 0 /\
              Seq.mem (new_addr <: obj_addr) (objects zero_addr res.major_out) /\
              U64.v (wosize_of_object (new_addr <: obj_addr) res.major_out) >= 1 /\
              AllocLemmas.chain_avoids res.major_out res.fp_out new_addr
                (heap_size / U64.v mword) = true))
  = let wz = minor_wosize minor addr in
    let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
    let new_addr = res.new_addr in
    // Validity
    promote_object_success minor cs.cs_major addr cs.cs_fp wz;
    AllocProps.alloc_spec_obj_valid cs.cs_major cs.cs_fp wz;
    // Membership
    AllocProps.alloc_search_obj_in_objects_pre_part1
      cs.cs_major cs.cs_fp 0UL cs.cs_fp wz (heap_size / U64.v mword);
    promote_object_preserves_objects_part1 minor cs.cs_major addr cs.cs_fp wz;
    // Wosize >= 1
    PromStep.promote_object_new_addr_wosize minor cs.cs_major addr cs.cs_fp wz;
    // Chain avoidance (directly from BlueProm)
    BlueProm.promote_object_new_addr_chain_avoids minor cs.cs_major addr cs.cs_fp wz
#pop-options

/// Helper for `a <> addr` case of fwd_targets_avoid_chain preservation
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let fwd_targets_old_addr
  (minor: minor_state) (cs: cheney_state) (addr: U64.t) (a: U64.t)
  : Lemma (requires
      cheney_inj_invariant cs /\
      Seq.mem addr (minor_objects minor) /\
      cs.cs_fwd addr = 0UL /\
      minor_wosize minor addr > 0 /\
      (promote_object minor cs.cs_major addr cs.cs_fp (minor_wosize minor addr)).new_addr <> 0UL /\
      a <> addr /\
      cs.cs_fwd a <> 0UL)
    (ensures (let wz = minor_wosize minor addr in
              let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
              let t = cs.cs_fwd a in
              U64.v t >= U64.v mword /\
              U64.v t < heap_size /\
              U64.v t % U64.v mword == 0 /\
              Seq.mem (t <: obj_addr) (objects zero_addr res.major_out) /\
              U64.v (wosize_of_object (t <: obj_addr) res.major_out) >= 1 /\
              AllocLemmas.chain_avoids res.major_out res.fp_out t
                (heap_size / U64.v mword) = true))
  = let wz = minor_wosize minor addr in
    let t = cs.cs_fwd a in
    // Old invariant gives all 6 properties on (cs.cs_major, cs.cs_fp)
    // Membership preserved
    promote_object_preserves_objects_part1 minor cs.cs_major addr cs.cs_fp wz;
    // Wosize preserved
    PromStep.promote_object_wosize_preserved minor cs.cs_major addr cs.cs_fp wz (t <: obj_addr);
    // Chain avoidance preserved
    ReadOther.promote_object_preserves_chain_avoids
      minor cs.cs_major addr cs.cs_fp wz t
#pop-options

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let cheney_forward_one_preserves_inj_invariant
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires cheney_inj_invariant cs)
          (ensures cheney_inj_invariant (cheney_forward_one minor cs addr))
  = let cs' = cheney_forward_one minor cs addr in
    // Case 1: addr not in minor_objects → noop
    if not (Seq.mem addr (minor_objects minor)) then begin
      cheney_forward_one_noop minor cs addr;
      assert (cs' == cs)
    end
    // Case 2: already forwarded → noop
    else if cs.cs_fwd addr <> 0UL then begin
      cheney_forward_one_noop minor cs addr;
      assert (cs' == cs)
    end
    // Case 3: wosize = 0 → noop
    else if minor_wosize minor addr = 0 then begin
      cheney_forward_one_noop_wz0 minor cs addr;
      assert (cs' == cs)
    end
    else begin
      let wz = minor_wosize minor addr in
      assert (wz > 0);
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      // Case 4: OOM → noop
      if res.new_addr = 0UL then begin
        cheney_forward_one_noop_oom minor cs addr;
        assert (cs' == cs)
      end
      // Case 5: success → must prove invariant for extended state
      else begin
        cheney_forward_one_success minor cs addr;
        let new_addr = res.new_addr in
        let new_fwd = extend_forwarding cs.cs_fwd addr new_addr in

        // Key equality: cs' fields match res fields
        assert (cs'.cs_major == res.major_out);
        assert (cs'.cs_fp == res.fp_out);
        assert (cs'.cs_fwd == new_fwd);

        // (1) wfh_part1, fl_valid, fl_chain_terminates for cs'
        cheney_forward_one_preserves_wfh_part1 minor cs addr;

        // (2) chain_objects_blue for cs'
        BlueProm.promote_object_preserves_chain_objects_blue
          minor cs.cs_major addr cs.cs_fp wz;

        // (3) Injectivity
        let aux_fresh (x: U64.t) : Lemma
          (requires cs.cs_fwd x <> 0UL)
          (ensures cs.cs_fwd x <> new_addr)
        = AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz (cs.cs_fwd x);
          promote_object_success minor cs.cs_major addr cs.cs_fp wz
        in
        Classical.forall_intro (Classical.move_requires aux_fresh);
        extend_forwarding_preserves_injective cs.cs_fwd addr new_addr;

        // (4) fwd_targets_avoid_chain for cs'
        let aux_all (a: U64.t) : Lemma
          (requires cs'.cs_fwd a <> 0UL)
          (ensures (let t = cs'.cs_fwd a in
            U64.v t >= U64.v mword /\
            U64.v t < heap_size /\
            U64.v t % U64.v mword == 0 /\
            Seq.mem (t <: obj_addr) (objects zero_addr cs'.cs_major) /\
            U64.v (wosize_of_object (t <: obj_addr) cs'.cs_major) >= 1 /\
            AllocLemmas.chain_avoids cs'.cs_major cs'.cs_fp t
              (heap_size / U64.v mword) = true))
        = if a = addr then fwd_targets_new_addr minor cs addr
          else fwd_targets_old_addr minor cs addr a
        in
        Classical.forall_intro (Classical.move_requires aux_all);
        ()
      end
    end
#pop-options


/// ---------------------------------------------------------------------------
/// cheney_forward_fields preserves injectivity (induction on fields)
/// ---------------------------------------------------------------------------

let rec cheney_forward_fields_preserves_inj_invariant
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires cheney_inj_invariant cs)
          (ensures cheney_inj_invariant (cheney_forward_fields minor cs parent idx wosize))
          (decreases (wosize - idx))
  = if idx >= wosize then
      cheney_forward_fields_base minor cs parent idx wosize
    else begin
      cheney_forward_fields_step minor cs parent idx wosize;
      let field_val = minor_read_field minor parent idx in
      let cs' = cheney_forward_one minor cs field_val in
      cheney_forward_one_preserves_inj_invariant minor cs field_val;
      cheney_forward_fields_preserves_inj_invariant minor cs' parent (idx + 1) wosize
    end


/// ---------------------------------------------------------------------------
/// cheney_forward_roots preserves injectivity (induction on roots)
/// ---------------------------------------------------------------------------

let rec cheney_forward_roots_preserves_inj_invariant
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires cheney_inj_invariant cs)
          (ensures cheney_inj_invariant (cheney_forward_roots minor cs roots idx))
          (decreases (Seq.length roots - idx))
  = if idx >= Seq.length roots then
      cheney_forward_roots_base minor cs roots idx
    else begin
      cheney_forward_roots_step minor cs roots idx;
      let r = Seq.index roots idx in
      let cs' = cheney_forward_one minor cs r in
      cheney_forward_one_preserves_inj_invariant minor cs r;
      cheney_forward_roots_preserves_inj_invariant minor cs' roots (idx + 1)
    end


/// ---------------------------------------------------------------------------
/// cheney_scan preserves injectivity (induction on fuel)
/// ---------------------------------------------------------------------------

let rec cheney_scan_preserves_inj_invariant
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires cheney_inj_invariant cs)
          (ensures cheney_inj_invariant (cheney_scan minor cs scan fuel))
          (decreases fuel)
  = if fuel = 0 then
      cheney_scan_base minor cs scan fuel
    else if scan >= Seq.length cs.cs_queue then
      cheney_scan_base minor cs scan fuel
    else begin
      cheney_scan_step minor cs scan fuel;
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' = cheney_forward_fields minor cs obj 0 wz in
      cheney_forward_fields_preserves_inj_invariant minor cs obj 0 wz;
      cheney_scan_preserves_inj_invariant minor cs' (scan + 1) (fuel - 1)
    end


/// ---------------------------------------------------------------------------
/// Top-level theorem
/// ---------------------------------------------------------------------------

let cheney_promote_fwd_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp)
    (ensures
      fwd_injective (cheney_promote minor major fp roots).fwd_map)
  = // Initial state satisfies invariant
    let cs0 : cheney_state =
      { cs_major = major; cs_fp = fp;
        cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
    // empty_forwarding is trivially injective
    assert (fwd_injective cs0.cs_fwd);
    // empty_forwarding targets trivially avoid chain (no targets)
    assert (fwd_targets_avoid_chain cs0);
    // well_formed_heap implies well_formed_heap_part1
    reveal_opaque (`%well_formed_heap) well_formed_heap;
    assert (well_formed_heap_part1 cs0.cs_major);
    assert (cheney_inj_invariant cs0);
    // Forward roots preserves invariant
    cheney_forward_roots_preserves_inj_invariant minor cs0 roots 0;
    let cs1 = cheney_forward_roots minor cs0 roots 0 in
    // Scan preserves invariant
    cheney_scan_preserves_inj_invariant minor cs1 0 (cheney_fuel minor);
    let cs2 = cheney_scan minor cs1 0 (cheney_fuel minor) in
    // Extract injectivity from final invariant
    assert (fwd_injective cs2.cs_fwd)

/// The fwd_targets_avoid_chain invariant gives us target validity as a corollary.
let cheney_promote_fwd_targets_valid
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      forall (a: U64.t). prom.fwd_map a <> 0UL ==>
        (U64.v (prom.fwd_map a) >= U64.v mword /\
         U64.v (prom.fwd_map a) < heap_size /\
         U64.v (prom.fwd_map a) % U64.v mword == 0 /\
         Seq.mem ((prom.fwd_map a) <: obj_addr) (objects zero_addr prom.major_final))))
  = let cs0 : cheney_state =
      { cs_major = major; cs_fp = fp;
        cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
    assert (fwd_targets_avoid_chain cs0);
    reveal_opaque (`%well_formed_heap) well_formed_heap;
    assert (cheney_inj_invariant cs0);
    cheney_forward_roots_preserves_inj_invariant minor cs0 roots 0;
    let cs1 = cheney_forward_roots minor cs0 roots 0 in
    cheney_scan_preserves_inj_invariant minor cs1 0 (cheney_fuel minor);
    let cs2 = cheney_scan minor cs1 0 (cheney_fuel minor) in
    assert (fwd_targets_avoid_chain cs2)
