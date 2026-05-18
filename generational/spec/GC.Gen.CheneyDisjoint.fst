/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyDisjoint — Implementation
/// ---------------------------------------------------------------------------

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
module AllocProps = GC.Gen.AllocProps
module ReadOther = GC.Gen.PromoteUpdate.PromoteFields.ReadOther
module BlueProm = GC.Gen.PromoteUpdate.BlueProm
module PromStep = GC.Gen.PromoteUpdate.PromoteFields.Step

/// ---------------------------------------------------------------------------
/// Helper: orig_nonblue_props preserved through promote_object
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let orig_nonblue_props_preserved
  (minor: minor_state) (cs: cheney_state) (addr: U64.t) (major_orig: heap)
  (obj: obj_addr)
  : Lemma (requires
      cheney_disjoint_invariant cs major_orig /\
      Seq.mem addr (minor_objects minor) /\
      cs.cs_fwd addr = 0UL /\
      minor_wosize minor addr > 0 /\
      (promote_object minor cs.cs_major addr cs.cs_fp (minor_wosize minor addr)).new_addr <> 0UL /\
      Seq.mem obj (objects zero_addr major_orig) /\
      ~(is_blue obj major_orig))
    (ensures (let wz = minor_wosize minor addr in
              let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
              Seq.mem obj (objects zero_addr res.major_out) /\
              U64.v (wosize_of_object obj res.major_out) >= 1 /\
              AllocLemmas.chain_avoids res.major_out res.fp_out obj
                (heap_size / U64.v mword) = true))
  = let wz = minor_wosize minor addr in
    let t = (obj <: U64.t) in
    // From orig_nonblue_props: obj has chain_avoids, membership, wosize in cs
    // Membership preserved
    promote_object_preserves_objects_part1 minor cs.cs_major addr cs.cs_fp wz;
    // Wosize preserved
    PromStep.promote_object_wosize_preserved minor cs.cs_major addr cs.cs_fp wz obj;
    // Chain avoidance preserved
    ReadOther.promote_object_preserves_chain_avoids
      minor cs.cs_major addr cs.cs_fp wz t
#pop-options

/// ---------------------------------------------------------------------------
/// Single step: cheney_forward_one preserves cheney_disjoint_invariant
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 150 --fuel 0 --ifuel 0"
let cheney_forward_one_preserves_disjoint_invariant
  (minor: minor_state) (cs: cheney_state) (addr: U64.t) (major_orig: heap)
  : Lemma (requires cheney_disjoint_invariant cs major_orig)
          (ensures cheney_disjoint_invariant (cheney_forward_one minor cs addr) major_orig)
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
        let new_addr = res.new_addr in
        let new_fwd = extend_forwarding cs.cs_fwd addr new_addr in
        cheney_forward_one_success minor cs addr;

        assert (cs'.cs_major == res.major_out);
        assert (cs'.cs_fp == res.fp_out);
        assert (cs'.cs_fwd == new_fwd);

        // (1) wfh_part1, fl_valid, fl_chain_terminates for cs'
        cheney_forward_one_preserves_wfh_part1 minor cs addr;

        // (2) chain_objects_blue for cs'
        BlueProm.promote_object_preserves_chain_objects_blue
          minor cs.cs_major addr cs.cs_fp wz;

        // (3) orig_nonblue_props for cs': preserved through promote
        let aux_props (obj: obj_addr) : Lemma
          (requires Seq.mem obj (objects zero_addr major_orig) /\ ~(is_blue obj major_orig))
          (ensures Seq.mem obj (objects zero_addr cs'.cs_major) /\
                   U64.v (wosize_of_object obj cs'.cs_major) >= 1 /\
                   AllocLemmas.chain_avoids cs'.cs_major cs'.cs_fp obj
                     (heap_size / U64.v mword) = true)
        = orig_nonblue_props_preserved minor cs addr major_orig obj
        in
        Classical.forall_intro (Classical.move_requires aux_props);

        // (4) fwd_disjoint_nonblue for cs': new_addr ≠ non-blue objects
        let aux_disjoint (a: U64.t) (obj: obj_addr) : Lemma
          (requires cs'.cs_fwd a <> 0UL /\
                    Seq.mem obj (objects zero_addr major_orig) /\
                    ~(is_blue obj major_orig))
          (ensures cs'.cs_fwd a <> (obj <: U64.t))
        = if a = addr then begin
            // new_addr case: use alloc_spec_obj_ne_excl
            // From orig_nonblue_props: chain_avoids cs.cs_major cs.cs_fp obj
            AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz (obj <: U64.t);
            promote_object_success minor cs.cs_major addr cs.cs_fp wz
          end else
            // old target case: inequality preserved (cs'.cs_fwd a = cs.cs_fwd a)
            ()
        in
        let aux_outer (a: U64.t) : Lemma
          (forall (obj: obj_addr).
            cs'.cs_fwd a <> 0UL /\
            Seq.mem obj (objects zero_addr major_orig) /\
            ~(is_blue obj major_orig) ==>
            cs'.cs_fwd a <> (obj <: U64.t))
        = Classical.forall_intro (Classical.move_requires (aux_disjoint a))
        in
        Classical.forall_intro aux_outer;
        ()
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Inductive: cheney_forward_fields preserves cheney_disjoint_invariant
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let rec cheney_forward_fields_preserves_disjoint_invariant
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  (major_orig: heap)
  : Lemma (requires cheney_disjoint_invariant cs major_orig)
          (ensures cheney_disjoint_invariant
            (cheney_forward_fields minor cs parent idx wosize) major_orig)
          (decreases (wosize - idx))
  = if idx >= wosize then
      cheney_forward_fields_base minor cs parent idx wosize
    else begin
      cheney_forward_fields_step minor cs parent idx wosize;
      let field_val = minor_read_field minor parent idx in
      let cs' = cheney_forward_one minor cs field_val in
      cheney_forward_one_preserves_disjoint_invariant minor cs field_val major_orig;
      cheney_forward_fields_preserves_disjoint_invariant minor cs' parent (idx + 1) wosize major_orig
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Inductive: cheney_forward_roots preserves cheney_disjoint_invariant
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let rec cheney_forward_roots_preserves_disjoint_invariant
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  (major_orig: heap)
  : Lemma (requires cheney_disjoint_invariant cs major_orig)
          (ensures cheney_disjoint_invariant
            (cheney_forward_roots minor cs roots idx) major_orig)
          (decreases (Seq.length roots - idx))
  = if idx >= Seq.length roots then
      cheney_forward_roots_base minor cs roots idx
    else begin
      cheney_forward_roots_step minor cs roots idx;
      let r = Seq.index roots idx in
      let cs' = cheney_forward_one minor cs r in
      cheney_forward_one_preserves_disjoint_invariant minor cs r major_orig;
      cheney_forward_roots_preserves_disjoint_invariant minor cs' roots (idx + 1) major_orig
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Inductive: cheney_scan preserves cheney_disjoint_invariant
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let rec cheney_scan_preserves_disjoint_invariant
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  (major_orig: heap)
  : Lemma (requires cheney_disjoint_invariant cs major_orig)
          (ensures cheney_disjoint_invariant
            (cheney_scan minor cs scan fuel) major_orig)
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
      cheney_forward_fields_preserves_disjoint_invariant minor cs obj 0 wz major_orig;
      cheney_scan_preserves_disjoint_invariant minor cs' (scan + 1) (fuel - 1) major_orig
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Top-level composition: cheney_promote establishes fwd_disjoint_nonblue
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 150 --fuel 0 --ifuel 0"
let cheney_promote_fwd_disjoint_nonblue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      nonblue_wosize_positive major)
    (ensures
      (let prom = cheney_promote minor major fp roots in
       fwd_map_disjoint_nonblue prom.fwd_map major))
  = // Initial state
    let cs0 : cheney_state =
      { cs_major = major; cs_fp = fp;
        cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
    // Base case: establish cheney_disjoint_invariant for cs0
    // fwd_disjoint_nonblue: vacuously true (empty_forwarding = fun _ -> 0UL)
    assert (fwd_disjoint_nonblue cs0 major);
    // orig_nonblue_props: from chain_objects_blue + nonblue_wosize_positive
    reveal_opaque (`%chain_objects_blue) chain_objects_blue;
    reveal_opaque (`%well_formed_heap) well_formed_heap;
    assert (well_formed_heap_part1 cs0.cs_major);
    assert (orig_nonblue_props cs0 major);
    assert (cheney_disjoint_invariant cs0 major);
    // Forward roots preserves invariant
    cheney_forward_roots_preserves_disjoint_invariant minor cs0 roots 0 major;
    let cs1 = cheney_forward_roots minor cs0 roots 0 in
    // Scan preserves invariant
    cheney_scan_preserves_disjoint_invariant minor cs1 0 (cheney_fuel minor) major;
    let cs2 = cheney_scan minor cs1 0 (cheney_fuel minor) in
    // Extract fwd_disjoint_nonblue from final invariant → fwd_map_disjoint_nonblue
    assert (fwd_disjoint_nonblue cs2 major);
    assert (fwd_map_disjoint_nonblue cs2.cs_fwd major)
#pop-options
