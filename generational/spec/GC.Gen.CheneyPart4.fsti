/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPart4 — Cheney promote preserves well_formed_heap_part4
/// ---------------------------------------------------------------------------
///
/// Proves that the Cheney BFS promotion loop preserves the part4 invariant
/// (no infix objects) through each step. Structure mirrors the part1 proof
/// in GC.Gen.Cheney.fst.
///
/// Key insight: part4 = "no object header has infix_tag". Each BFS step is
/// a promote_object = alloc + copy_fields + zero_padding + set_promoted_tag.
///   - alloc_spec: allocated block gets tag 0 or blue → not infix
///   - copy_fields: writes only body words → headers unchanged → part4 preserved
///   - zero_promote_padding: writes body → part4 preserved (exported lemma)
///   - set_promoted_tag: writes minor's tag (≠ infix_tag) → part4 preserved
///
/// Precondition: all minor objects have non-infix tag (minor_all_no_infix).
/// This is a standard structural invariant — minor objects are independently
/// allocated, never infix sub-objects of closures.

module GC.Gen.CheneyPart4

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneySpec = GC.Gen.Cheney

/// All minor objects have non-infix tag (standard for bump-allocated minor heap)
let minor_all_no_infix (minor: minor_state) : prop =
  forall (addr: U64.t).
    Seq.mem addr (minor_objects minor) ==>
    minor_tag minor addr <> U64.v GC.Spec.Object.infix_tag

/// promote_object preserves well_formed_heap_part4 when the promoted object
/// has a non-infix tag.
val promote_object_preserves_wfh_part4
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      well_formed_heap_part4 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      minor_tag minor obj <> U64.v GC.Spec.Object.infix_tag)
    (ensures
      well_formed_heap_part4 (promote_object minor major obj fp wz).major_out)

/// cheney_forward_one preserves wfh_part4
val cheney_forward_one_preserves_wfh_part4
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      well_formed_heap_part4 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      minor_all_no_infix minor)
    (ensures
      (let cs' = CheneySpec.cheney_forward_one minor cs addr in
       well_formed_heap_part4 cs'.cs_major))

/// cheney_forward_fields preserves wfh_part1 + wfh_part4 + fl_valid + fl_chain_terminates
val cheney_forward_fields_preserves_wfh_part4
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      well_formed_heap_part4 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      minor_all_no_infix minor)
    (ensures
      (let cs' = CheneySpec.cheney_forward_fields minor cs parent idx wosize in
       well_formed_heap_part1 cs'.cs_major /\
       well_formed_heap_part4 cs'.cs_major /\
       AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
       AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))
    (decreases (if idx < wosize then wosize - idx else 0))

/// cheney_forward_roots preserves wfh_part1 + wfh_part4 + fl_valid + fl_chain_terminates
val cheney_forward_roots_preserves_wfh_part4
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (roots: seq U64.t) (idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      well_formed_heap_part4 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      minor_all_no_infix minor)
    (ensures
      (let cs' = CheneySpec.cheney_forward_roots minor cs roots idx in
       well_formed_heap_part1 cs'.cs_major /\
       well_formed_heap_part4 cs'.cs_major /\
       AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
       AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))
    (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))

/// cheney_scan preserves wfh_part4
val cheney_scan_preserves_wfh_part4
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (fuel: nat)
  : Lemma
    (requires
      well_formed_heap_part1 cs.cs_major /\
      well_formed_heap_part4 cs.cs_major /\
      AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
      minor_all_no_infix minor)
    (ensures
      (let cs' = CheneySpec.cheney_scan minor cs scan fuel in
       well_formed_heap_part4 cs'.cs_major))
    (decreases fuel)

/// Main theorem: cheney_promote preserves well_formed_heap_part4
val cheney_promote_preserves_wfh_part4
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      minor_all_no_infix minor)
    (ensures
      well_formed_heap_part4 (CheneySpec.cheney_promote minor major fp roots).major_final)
