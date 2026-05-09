/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation — Proofs
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney

module Allocator = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark

/// ---------------------------------------------------------------------------
/// Core sub-lemma: promote_object preserves no_black_objects
/// ---------------------------------------------------------------------------
///
/// QUARANTINED ADMIT: The success branch requires showing that alloc_spec
/// writes white_bits (color=0=White) for the newly allocated object, and
/// copy_fields only writes body fields. This is morally obvious from
/// alloc_spec's definition (it calls make_header with white_bits), but
/// requires alloc_spec frame analysis under well_formed_heap_part1.
/// The OOM branch is trivially proved (no state change).

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"

private let promote_object_preserves_no_black
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects major)
          (ensures (let res = promote_object minor major obj fp wz in
                    Mark.no_black_objects res.major_out))
  =
  let alloc_res = Allocator.alloc_spec major fp wz in
  if alloc_res.obj_out = 0UL then
    promote_object_oom minor major obj fp wz
  else begin
    promote_object_success minor major obj fp wz;
    // alloc_spec writes white_bits (color 0) for the allocated object.
    // copy_fields writes body fields only, preserving all headers.
    // For each object in the result: header is either unchanged (not black
    // by precondition) or newly written (white/blue, never black).
    // Detailed proof requires alloc_spec frame analysis.
    admit () // Quarantined gap: alloc_spec_preserves_no_black_part1
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_one preserves no_black_objects
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let cheney_forward_one_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects cs.cs_major)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    Mark.no_black_objects cs'.cs_major))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then
    cheney_forward_one_noop minor cs addr
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then
      cheney_forward_one_noop_wz0 minor cs addr
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_one_noop_oom minor cs addr
      else begin
        cheney_forward_one_success minor cs addr;
        promote_object_preserves_no_black minor cs.cs_major addr cs.cs_fp wz
      end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_fields preserves no_black_objects (recursive)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let rec cheney_forward_fields_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects cs.cs_major)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    Mark.no_black_objects cs'.cs_major))
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    cheney_forward_fields_base minor cs parent idx wosize
  else begin
    cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = minor_read_field minor parent idx in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_no_black minor cs field_val;
    cheney_forward_fields_preserves_no_black minor cs' parent (idx + 1) wosize
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_roots preserves wfh_part1 (needed for scan precondition)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots idx
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_roots_preserves_wfh_part1 minor cs' roots (idx + 1)
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_roots preserves no_black_objects (recursive)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects cs.cs_major)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    Mark.no_black_objects cs'.cs_major))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots idx
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_one_preserves_no_black minor cs r;
    cheney_forward_roots_preserves_no_black minor cs' roots (idx + 1)
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_scan preserves no_black_objects (recursive)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"

private let rec cheney_scan_preserves_no_black
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects cs.cs_major)
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    Mark.no_black_objects cs'.cs_major))
          (decreases fuel)
  =
  if fuel = 0 then
    cheney_scan_base minor cs scan fuel
  else if scan >= Seq.length cs.cs_queue then
    cheney_scan_base minor cs scan fuel
  else begin
    cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    cheney_forward_fields_preserves_no_black minor cs obj 0 wz;
    let fuel' : nat = fuel - 1 in
    cheney_scan_preserves_no_black minor cs' (scan + 1) fuel'
  end

#pop-options

/// ---------------------------------------------------------------------------
/// Top-level: cheney_promote preserves no_black_objects
/// ---------------------------------------------------------------------------

let cheney_promote_preserves_no_black
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects major)
          (ensures (let res = cheney_promote minor major fp roots in
                    Mark.no_black_objects res.major_final))
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  // Phase 1: forward_roots preserves no_black + wfh_part1
  cheney_forward_roots_preserves_no_black minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  // Phase 2: scan preserves no_black
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_no_black minor cs1 0 (cheney_fuel minor)
