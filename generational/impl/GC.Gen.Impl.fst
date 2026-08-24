(*
   Pulse GC (Generational) - Top-Level Entry Point Implementation

   Routes allocations by size and implements minor collection
   using Cheney-style BFS (promotes only reachable objects).
*)

module GC.Gen.Impl

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.Impl.Promote
open GC.Gen.Impl.UpdatePtrs
open GC.Gen.Impl.Cheney
open GC.Impl.Heap
open GC.Impl.Stack
module SpecFields = GC.Spec.Fields
module SpecObj = GC.Spec.Object
module Alloc = GC.Impl.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneySpec = GC.Gen.Cheney
module ML = FStar.Math.Lemmas
module MajorGC = GC.Impl
module MarkBoundedImpl = GC.Impl.MarkBounded
module MBP = GC.Impl.MarkBoundedPrecondition
module GMP = GC.Gen.MajorPrecondition
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module SpecGCPost = GC.Spec.Correctness
module Mark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module CheneyCorr = GC.Gen.CheneyCorrectness
module TwoPass = GC.Gen.TwoPassEquiv
module GenInv = GC.Gen.HeapInvariant
module FreeListShape = GC.Gen.FreeListShape
module MinorFwd = GC.Gen.MinorCollectForwarding
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module RBridge = GC.Gen.ReachabilityBridge
module CheneyBFS = GC.Gen.CheneyBFS
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module Cheney = GC.Gen.Impl.Cheney

/// Two transports in one: `GC.Gen.MajorPrecondition` carries the pre-minor facts
/// across the minor collection to `darken_precondition`, and
/// `MarkBoundedPrecondition` carries that across root darkening to the
/// obligation `GC.Impl.collect_with_roots` actually demands.  Neither step is
/// the caller's business.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let gen_gc_major_precondition_elim minor major fp roots st cap
  = let result = CheneySpec.cheney_collect_spec minor major fp roots in
    assert (Seq.equal st (Seq.empty #obj_addr));
    GMP.darken_precondition_after_minor minor major fp roots cap;
    MBP.darken_establishes_precondition result.mc_major st result.mc_roots result.mc_fp cap;
    MBP.darken_roots_match_stack result.mc_major st result.mc_roots result.mc_fp cap
#pop-options

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

/// Allocate: try minor first (if small enough), fall back to major.
#push-options "--z3rlimit 10"
fn gen_alloc (gh: gen_heap_t) (wosize: U64.t) (tag: U64.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pure (U64.v wosize > 0 /\ U64.v tag < 256 /\
                 SpecFields.well_formed_heap 's)
  returns obj: U64.t
  ensures exists* d2 b2 s2 fp2. is_gen_heap gh d2 b2 s2 fp2
{
  unfold is_gen_heap;
  if U64.lte wosize max_young_wosize_u64 {
    // Small object → try minor heap
    let obj = minor_alloc gh.minor wosize tag;
    if U64.eq obj 0UL {
      // Minor full — allocate directly from major
      let fp = R.op_Bang gh.fp_ref;
      let res = Alloc.allocate gh.major fp wosize;
      R.op_Colon_Equals gh.fp_ref (fst res);
      fold (is_gen_heap gh _ _ _ _);
      snd res
    } else {
      fold (is_gen_heap gh _ _ _ _);
      obj
    }
  } else {
    // Large object → major heap directly
    let fp = R.op_Bang gh.fp_ref;
    let res = Alloc.allocate gh.major fp wosize;
    R.op_Colon_Equals gh.fp_ref (fst res);
    fold (is_gen_heap gh _ _ _ _);
    snd res
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Minor Collection — Full Implementation
/// ---------------------------------------------------------------------------

module PromoteSpec = GC.Gen.Promote
open GC.Gen.PromoteUpdate

let minor_heap_no_scan_invariant_elim (d: minor_heap) (b: U64.t)
  : Lemma (requires minor_heap_no_scan_invariant d b)
          (ensures PromoteSpec.minor_no_scan_invariant ({ data = d; bump = b }))
  = reveal_opaque (`%minor_heap_no_scan_invariant) (minor_heap_no_scan_invariant d b)

/// Helper: advancing by a multiple of 8 preserves 8-alignment
let advance_aligned (p tw: nat)
  : Lemma (requires p % 8 == 0)
          (ensures (p + tw * 8) % 8 == 0)
  = FStar.Math.Lemmas.lemma_mod_plus p tw 8

/// Helper: total_words * 8 doesn't overflow U64
/// (since total_words <= minor_heap_size < pow2 57, so tw*8 < pow2 60 < pow2 64)
let mul8_no_overflow (tw: nat)
  : Lemma (requires tw <= minor_heap_size)
          (ensures tw * 8 < pow2 64)
  = FStar.Math.Lemmas.lemma_mult_le_right 8 tw minor_heap_size;
    FStar.Math.Lemmas.lemma_mult_le_right 8 minor_heap_size (pow2 57);
    assert_norm (pow2 57 * 8 < pow2 64)

/// Helper: p + total_bytes doesn't overflow U64
/// (p <= minor_heap_size < pow2 57, total_bytes <= minor_heap_size * 8 < pow2 60)
let add_no_overflow (p tw: nat)
  : Lemma (requires p <= minor_heap_size /\ tw <= minor_heap_size)
          (ensures p + tw * 8 < pow2 64)
  = mul8_no_overflow tw;
    assert (tw * 8 < pow2 64);
    assert (p < pow2 57);
    assert_norm (pow2 57 + pow2 57 * 8 < pow2 64);
    FStar.Math.Lemmas.lemma_mult_le_right 8 tw minor_heap_size;
    assert (tw * 8 <= minor_heap_size * 8);
    FStar.Math.Lemmas.lemma_mult_le_right 8 minor_heap_size (pow2 57);
    assert (minor_heap_size * 8 <= pow2 57 * 8)

/// `minor_wosize` of the object at `p + 8` is the wosize field of the header word
/// stored at `p`.  Both sides unfold to the same thing, but the `U64.uint_to_t`
/// round-trip inside `minor_wosize` is a goal Z3 4.15.3 will not discharge under the
/// hypothesis load of `promote_phase`'s loop, so it is proved here instead.
let minor_wosize_at (p obj_addr: U64.t)
  : Lemma (requires U64.v obj_addr == U64.v p + 8 /\
                    U64.v p % 8 == 0 /\
                    U64.v obj_addr < minor_heap_size)
          (ensures forall (ms: minor_state).
                     minor_wosize ms obj_addr ==
                     U64.v (U64.shift_right (minor_read_word_t ms.data p) 10ul))
  = ()

/// `p + (wosize + 1) * 8 <= bump` gives the bound `promote_one` asks for on the
/// object body.  Trivial, and trivially out of reach inside the loop.
let promote_body_bound (p wosize bump: nat)
  : Lemma (requires p + (wosize + 1) * 8 <= bump)
          (ensures (p + 8) + wosize * 8 <= bump)
  = ()

/// Phase 1: Promote all minor objects and fill forwarding array.
/// Walks minor heap linearly from 0 to bump, promoting each object.
/// Records forwarding: fwd_arr[obj/8] := new_major_addr.
#push-options "--z3rlimit 12 --fuel 4 --ifuel 1"
fn promote_phase (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
                 (fwd_arr: array U64.t)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pure (SpecFields.well_formed_heap_part1 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp heap_words /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp heap_words /\
                 Seq.length 'farr == fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL))
  ensures exists* md2 mb2 ms2 fp2 farr2.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pts_to fwd_arr farr2 **
    pure (md2 == 'md /\ mb2 == 'mb /\
          SpecFields.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 heap_words /\
          AllocLemmas.fl_chain_terminates ms2 fp2 heap_words /\
          Seq.length farr2 == fwd_array_size)
{
  // Read bump pointer
  unfold is_minor minor 'md 'mb;
  let bump = R.op_Bang minor.bump_ref;
  fold (is_minor minor 'md bump);
  let mut pos = 0UL;
  while (U64.lt !pos bump)
    invariant exists* md_i mb_i ms_i fp_i farr_i p_i.
      is_minor minor md_i mb_i **
      is_heap major ms_i **
      R.pts_to fp_ref fp_i **
      pts_to fwd_arr farr_i **
      R.pts_to pos p_i **
      pure (U64.v p_i <= U64.v bump /\
            U64.v p_i % 8 == 0 /\
            U64.v bump <= minor_heap_size /\
            U64.v bump % 8 == 0 /\
            md_i == 'md /\ mb_i == bump /\
            SpecFields.well_formed_heap_part1 ms_i /\
            AllocLemmas.fl_valid ms_i fp_i heap_words /\
            AllocLemmas.fl_chain_terminates ms_i fp_i heap_words /\
            Seq.length farr_i == Seq.length 'farr)
    decreases (Prims.op_Subtraction (U64.v bump) (U64.v !pos))
  {
    let p = !pos;
    if U64.gte (U64.add p 8UL) bump {
      pos := bump
    } else {
      let hdr = minor_read minor p;
      let wosize = U64.shift_right hdr 10ul;
      if U64.eq wosize 0UL {
        advance_aligned (U64.v p) 1;
        pos := U64.add p 8UL
      } else {
        let obj_addr = U64.add p 8UL;
        if U64.gte wosize minor_heap_size_u64 {
          pos := bump
        } else {
          // wosize < minor_heap_size, so (wosize+1)*8 fits in U64
          let total_words = U64.add wosize 1UL;
          mul8_no_overflow (U64.v total_words);
          let total_bytes = U64.mul total_words 8UL;
          add_no_overflow (U64.v p) (U64.v total_words);
          if U64.gt (U64.add p total_bytes) bump {
            pos := bump
          } else {
            // Establish promote_one preconditions one by one
            // obj_addr alignment: p % 8 == 0 implies (p+8) % 8 == 0
            advance_aligned (U64.v p) 1;
            minor_wosize_at p obj_addr;
            promote_body_bound (U64.v p) (U64.v wosize) (U64.v bump);
            // obj_addr bounds: p + total_bytes <= bump <= minor_heap_size
            // so obj_addr = p+8 < p + total_bytes <= bump <= minor_heap_size
            // and obj_addr + wosize * 8 = (p+8) + wosize*8
            //   = p + (wosize+1)*8 = p + total_bytes <= bump <= minor_heap_size
            let new_addr = promote_one minor major fp_ref obj_addr;
            with farr_pre. assert (pts_to fwd_arr farr_pre);
            let idx = SZ.uint64_to_sizet (U64.div obj_addr 8UL);
            fwd_arr.(idx) <- new_addr;
            // Prove next pos is aligned
            advance_aligned (U64.v p) (U64.v total_words);
            pos := U64.add p total_bytes
          }
        }
      }
    }
  }
}
#pop-options

/// Helper: extract wfh_part1 from well_formed_heap
let wfh_implies_part1 (g: heap_state)
  : Lemma (requires SpecFields.well_formed_heap g)
          (ensures SpecFields.well_formed_heap_part1 g)
  = reveal_opaque (`%SpecFields.well_formed_heap) SpecFields.well_formed_heap

/// Lemma: unfold cheney_collect_spec in terms of cheney_promote
let cheney_collect_spec_unfold (minor: minor_state) (major: heap_state) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma (let prom = CheneySpec.cheney_promote minor major fp roots in
           let res = CheneySpec.cheney_collect_spec minor major fp roots in
           res.mc_major == PromoteSpec.update_major_pointers prom.major_final prom.fwd_map /\
           res.mc_fp == prom.fp_final /\
           res.mc_roots == PromoteSpec.rewrite_roots roots prom.fwd_map)
  = ()

/// Bridge lemma: fwd_bounded + represents_fwd implies valid_fwd_entries.
/// fwd_bounded gives: fwd(x) != 0 ==> >= mword /\ < heap_size /\ % mword == 0
/// represents_fwd: farr[i] == fwd(i*8)
/// valid_fwd_entries: farr[i] == 0 \/ (>= 8 /\ % 8 == 0 /\ <= heap_size)
let fwd_bounded_implies_valid_fwd_entries
  (farr: Seq.seq U64.t) (fwd: PromoteSpec.forwarding_map)
  : Lemma (requires CheneySpec.fwd_bounded fwd /\
                    represents_fwd farr fwd)
          (ensures valid_fwd_entries farr)
  = let aux (i: nat{i < fwd_array_size}) : Lemma
      (ensures (let addr = Seq.index farr i in
                addr == 0UL \/
                (U64.v addr >= 8 /\ U64.v addr % 8 == 0 /\
                 U64.v addr <= heap_size)))
    = assert (Seq.length farr == fwd_array_size);
      let addr = Seq.index farr i in
      assert (addr == fwd (U64.uint_to_t (i * 8)));
      if addr <> 0UL then begin
        assert (U64.v addr >= U64.v mword);
        assert (U64.v addr < heap_size);
        assert (U64.v addr % U64.v mword == 0)
      end
    in
    Classical.forall_intro aux

/// Derivation: fwd_above_zero_addr + fwd_bounded implies fwd_targets_stable.
/// Since targets > zero_addr >= minor_heap_size and aligned, to_minor_offset is identity
/// and is_minor_pointer is false — so the fwd_targets_stable condition holds.
let derive_fwd_targets_stable (fwd: PromoteSpec.forwarding_map)
  : Lemma (requires CheneySpec.fwd_above_zero_addr fwd /\ CheneySpec.fwd_bounded fwd)
          (ensures fwd_targets_stable fwd)
  =
  reveal_opaque (`%fwd_targets_stable) (fwd_targets_stable fwd);
  // For all x: fwd x <> 0 ==> U64.v(fwd x) > U64.v zero_addr >= minor_heap_size
  // to_minor_offset(fwd x) = fwd x (since target >= minor_heap_size, condition v < minor_heap_size fails)
  // is_minor_pointer(fwd x) = false (requires U64.v < minor_heap_size)
  // Hence ~(is_minor_pointer(...) /\ ...) trivially
  let aux (x: U64.t)
    : Lemma (requires fwd x <> 0UL)
            (ensures (let target = fwd x in
                      let target_as_minor = to_minor_offset target in
                      ~(PromoteSpec.is_minor_pointer target_as_minor /\ fwd target_as_minor <> 0UL)))
    = let target = fwd x in
      zero_addr_above_minor ();
      // From fwd_above_zero_addr: U64.v target > U64.v zero_addr >= minor_heap_size
      assert (U64.v target > U64.v zero_addr);
      assert (U64.v target >= minor_heap_size);
      // From fwd_bounded: target % 8 == 0
      assert (U64.v target % 8 == 0);
      // to_minor_offset_stable: target >= minor_heap_size /\ target % 8 == 0 ==> to_minor_offset target = target
      to_minor_offset_stable_above_minor target;
      assert (to_minor_offset target == target);
      // is_minor_pointer target requires U64.v target < minor_heap_size — contradiction
      assert (~(PromoteSpec.is_minor_pointer target))
  in
  Classical.forall_intro (Classical.move_requires aux)

module CheneyPres = GC.Gen.CheneyPreservation
module SpecObj = GC.Spec.Object
module IndDesc = FStar.IndefiniteDescription
module Sim = GC.Gen.Cheney.Sim

/// Derivation: fwd_valid_or_infix + wfh_part1 + fwd_bounded + represents_fwd
/// implies promoted_entries_valid_from.
/// Each non-zero farr entry fwd(i*8) has valid bounds (from fwd_bounded),
/// and is either in objects (with wosize bounds from wfh_part1) or is_infix.
#push-options "--z3rlimit 15 --fuel 0 --ifuel 0"
let derive_promoted_entries_valid_from
  (major: heap_state) (farr: Seq.seq U64.t) (fwd: PromoteSpec.forwarding_map)
  : Lemma (requires
      Seq.length farr == fwd_array_size /\
      (forall (i:nat). i < fwd_array_size ==> Seq.index farr i == fwd (U64.uint_to_t (i * 8))) /\
      CheneyPres.fwd_valid_or_infix fwd major /\
      CheneySpec.fwd_bounded fwd /\
      SpecFields.well_formed_heap_part1 major)
    (ensures promoted_entries_valid_from major farr 0)
  =
  let aux (i: nat{i < fwd_array_size}) : Lemma
    (ensures (let obj = Seq.index farr i in
              obj = 0UL \/
              (U64.v obj >= U64.v mword /\ U64.v obj % 8 == 0 /\ U64.v obj < heap_size /\
               SpecObj.is_infix obj major) \/
              (U64.v obj >= U64.v mword /\ U64.v obj % 8 == 0 /\ U64.v obj < heap_size /\
               Seq.mem obj (SpecFields.objects zero_addr major) /\
               (let wz = U64.v (SpecObj.wosize_of_object obj major) in
                U64.v obj + wz * 8 <= heap_size /\
                (forall (k:nat). k < wz ==>
                  (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0))))))
  = let obj = Seq.index farr i in
    if obj = 0UL then ()
    else begin
      // obj = fwd(i*8), and obj <> 0UL
      // From fwd_bounded: bounds hold
      assert (U64.v obj >= U64.v mword /\ U64.v obj < heap_size /\ U64.v obj % U64.v mword == 0);
      // From fwd_valid_or_infix: Seq.mem obj objects \/ is_infix obj major
      if SpecObj.is_infix obj major then ()
      else begin
        // obj is in objects — derive wosize bounds from wfh_part1
        assert (Seq.mem obj (SpecFields.objects zero_addr major));
        SpecFields.wfh_part1_obj_bound major obj
      end
    end
  in
  Classical.forall_intro aux
#pop-options

/// Derivation: fwd_valid_or_infix + wfh_part1 + well_formed_heap_part4
/// implies promoted_entries_disjoint.
/// Non-infix entries are in objects (by exclusion from fwd_valid_or_infix + part4),
/// and objects_separated gives body disjointness.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let derive_promoted_entries_disjoint
  (major: heap_state) (farr: Seq.seq U64.t) (fwd: PromoteSpec.forwarding_map)
  : Lemma (requires
      Seq.length farr == fwd_array_size /\
      (forall (i:nat). i < fwd_array_size ==> Seq.index farr i == fwd (U64.uint_to_t (i * 8))) /\
      CheneyPres.fwd_valid_or_infix fwd major /\
      CheneyPres.fwd_normal_injective fwd major /\
      CheneySpec.fwd_bounded fwd /\
      SpecFields.well_formed_heap_part1 major)
    (ensures promoted_entries_disjoint major farr)
  =
  let aux (i1 i2: nat) : Lemma
    (ensures (i1 < fwd_array_size /\ i2 < fwd_array_size /\ i1 <> i2 ==>
      (let o1 = Seq.index farr i1 in
       let o2 = Seq.index farr i2 in
       o1 <> 0UL /\ o2 <> 0UL /\
       U64.v o1 >= 8 /\ U64.v o2 >= 8 /\
       U64.v o1 % 8 == 0 /\ U64.v o2 % 8 == 0 /\
       U64.v o1 < heap_size /\ U64.v o2 < heap_size /\
       SpecObj.is_infix o1 major = false /\
       SpecObj.is_infix o2 major = false ==>
       (U64.v o1 + U64.v (SpecObj.wosize_of_object o1 major) * 8 <= U64.v o2 \/
        U64.v o2 + U64.v (SpecObj.wosize_of_object o2 major) * 8 <= U64.v o1))))
  = if not (i1 < fwd_array_size && i2 < fwd_array_size && i1 <> i2) then ()
    else
    let o1 = Seq.index farr i1 in
    let o2 = Seq.index farr i2 in
    if o1 = 0UL || o2 = 0UL then ()
    else if not (U64.v o1 >= 8 && U64.v o2 >= 8 && U64.v o1 % 8 = 0 && U64.v o2 % 8 = 0 &&
                 U64.v o1 < heap_size && U64.v o2 < heap_size) then ()
    else if SpecObj.is_infix o1 major || SpecObj.is_infix o2 major then ()
    else begin
      // Both non-infix: from fwd_valid_or_infix, they're in objects
      assert (Seq.mem o1 (SpecFields.objects zero_addr major));
      assert (Seq.mem o2 (SpecFields.objects zero_addr major));
      // objects_separated gives body disjointness
      if U64.v o1 < U64.v o2 then
        SpecFields.objects_separated zero_addr major o1 o2
      else if U64.v o2 < U64.v o1 then
        SpecFields.objects_separated zero_addr major o2 o1
      else begin
        // o1 = o2: from fwd_normal_injective, fwd is injective on non-infix targets
        // o1 = fwd(i1*8), o2 = fwd(i2*8), both non-zero, both non-infix, and equal
        // => i1*8 = i2*8 => i1 = i2, contradicting i1 <> i2
        let addr1 = U64.uint_to_t (i1 * 8) in
        let addr2 = U64.uint_to_t (i2 * 8) in
        assert (fwd addr1 <> 0UL);
        assert (fwd addr2 <> 0UL);
        assert (SpecObj.is_infix (fwd addr1) major = false);
        assert (SpecObj.is_infix (fwd addr2) major = false);
        assert (fwd addr1 = fwd addr2);
        // From fwd_normal_injective: addr1 = addr2
        assert (addr1 = addr2);
        // Therefore i1 * 8 = i2 * 8, so i1 = i2 — contradiction with i1 <> i2
        assert (i1 * 8 = i2 * 8);
        assert (i1 = i2)
        // Contradiction reached: this branch is unreachable
      end
    end
  in
  Classical.forall_intro_2 aux
#pop-options

/// Derivation: farr represents a Cheney forwarding map whose normal targets are
/// non-blue, hence every non-zero non-infix farr entry is non-blue.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let derive_promoted_entries_not_blue
  (major: heap_state) (farr: Seq.seq U64.t) (fwd: PromoteSpec.forwarding_map)
  : Lemma (requires
      Seq.length farr == fwd_array_size /\
      represents_fwd farr fwd /\
      CheneyPres.fwd_targets_not_blue fwd major)
    (ensures promoted_entries_not_blue major farr)
  =
    let aux (i: nat{i < fwd_array_size}) : Lemma
      (ensures
        (let obj = Seq.index farr i in
         obj <> 0UL /\
         U64.v obj >= U64.v mword /\
         U64.v obj % U64.v mword == 0 /\
         U64.v obj < heap_size /\
         SpecObj.is_infix obj major = false ==>
         SpecObj.is_blue obj major = false))
    = let obj = Seq.index farr i in
      if obj <> 0UL &&
         U64.v obj >= U64.v mword &&
         U64.v obj % U64.v mword = 0 &&
         U64.v obj < heap_size &&
         SpecObj.is_infix obj major = false
      then begin
        let src = U64.uint_to_t (i * 8) in
        assert (obj == fwd src);
        GC.Spec.Base.is_val_addr_spec obj;
        assert (is_val_addr obj);
        assert (fwd src <> 0UL);
        assert (is_val_addr (fwd src));
        assert (SpecObj.is_infix (fwd src) major = false);
        assert (SpecObj.is_blue ((fwd src) <: obj_addr) major = false)
      end
    in
    Classical.forall_intro aux
#pop-options

/// Derive post-promotion slot soundness from the ref-table's pre-promotion
/// soundness.  The slots point into pre-existing non-blue objects; Cheney frame
/// preserves those objects' headers, so they remain non-blue scannable objects
/// at the same field addresses in major_final.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let derive_slots_scannable_in_major
  (minor: minor_state) (major_pre: heap_state) (fp: U64.t) (roots: Seq.seq U64.t)
  (slots: Seq.seq U64.t) (n: nat)
  : Lemma (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       SpecFields.well_formed_heap major_pre /\
       AllocLemmas.fl_valid major_pre fp heap_words /\
       AllocLemmas.fl_chain_terminates major_pre fp heap_words /\
       PromoteSpec.chain_objects_blue major_pre fp /\
       minor_infix_wf minor /\
       ref_table_sound major_pre slots n))
    (ensures
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       slots_scannable_in_major prom.major_final slots n))
  =
    let prom = CheneySpec.cheney_promote minor major_pre fp roots in
    CheneySpec.cheney_promote_preserves_objects minor major_pre fp roots;
    let aux (i: nat{i < n}) : Lemma
      (ensures
        (let addr = U64.v (Seq.index slots i) in
         exists (obj: GC.Spec.Base.obj_addr) (j: nat).
           Seq.mem obj (SpecFields.objects zero_addr prom.major_final) /\
           SpecObj.is_blue obj prom.major_final = false /\
           SpecObj.is_no_scan obj prom.major_final = false /\
           j < U64.v (SpecObj.wosize_of_object obj prom.major_final) /\
           addr == U64.v obj + j * 8 /\
           U64.v obj + j * 8 + 8 <= heap_size /\
           (U64.v obj + j * 8) % 8 == 0))
    = let slot_addr = Seq.index slots i in
      let a = U64.v slot_addr in
      let obj : GC.Spec.Base.obj_addr = IndDesc.indefinite_description_ghost
        GC.Spec.Base.obj_addr
        (fun obj -> exists (j: nat).
          Seq.mem obj (SpecFields.objects zero_addr major_pre) /\
          SpecObj.is_blue obj major_pre = false /\
          SpecObj.is_no_scan obj major_pre = false /\
          j < U64.v (SpecObj.wosize_of_object obj major_pre) /\
          a == U64.v obj + j * 8) in
      let j : nat = IndDesc.indefinite_description_ghost nat
        (fun j ->
          Seq.mem obj (SpecFields.objects zero_addr major_pre) /\
          SpecObj.is_blue obj major_pre = false /\
          SpecObj.is_no_scan obj major_pre = false /\
          j < U64.v (SpecObj.wosize_of_object obj major_pre) /\
          a == U64.v obj + j * 8) in
      assert (Seq.mem obj (SpecFields.objects zero_addr major_pre));
      assert (SpecObj.is_blue obj major_pre = false);
      assert (SpecObj.is_no_scan obj major_pre = false);
      assert (j < U64.v (SpecObj.wosize_of_object obj major_pre));
      assert (a == U64.v obj + j * 8);
      assert (Seq.mem obj (SpecFields.objects zero_addr prom.major_final));
      CheneyPres.cheney_promote_frame_old_header minor major_pre fp roots obj;
      assert (GC.Spec.Heap.read_word prom.major_final (GC.Spec.Heap.hd_address obj)
           == GC.Spec.Heap.read_word major_pre (GC.Spec.Heap.hd_address obj));
      SpecObj.color_of_header_eq obj prom.major_final major_pre;
      assert (SpecObj.is_blue obj prom.major_final = false);
      SpecObj.tag_of_object_spec obj prom.major_final;
      SpecObj.tag_of_object_spec obj major_pre;
      SpecObj.is_no_scan_spec obj prom.major_final;
      SpecObj.is_no_scan_spec obj major_pre;
      assert (SpecObj.is_no_scan obj prom.major_final = false);
      SpecObj.wosize_of_object_spec obj prom.major_final;
      SpecObj.wosize_of_object_spec obj major_pre;
      assert (SpecObj.wosize_of_object obj prom.major_final ==
              SpecObj.wosize_of_object obj major_pre);
      assert (j < U64.v (SpecObj.wosize_of_object obj prom.major_final));
      wfh_implies_part1 major_pre;
      SpecFields.wfh_part1_obj_bound major_pre obj;
      assert (U64.v obj + U64.v (SpecObj.wosize_of_object obj major_pre) * 8 <= heap_size);
      assert (U64.v obj + j * 8 + 8 <= heap_size);
      ML.lemma_mod_plus (U64.v obj) j 8;
      assert ((U64.v obj + j * 8) % 8 == 0)
    in
    Classical.forall_intro aux
#pop-options

/// Derivation: frame + ref_table_complete + ref_table_sound + represents_fwd
/// implies fwd_ptrs_classified.
///
/// Every forwarded minor pointer field in major_final is either:
///   - In a pre-existing non-blue object body → frame shows same value as major_pre
///     → ref_table_complete covers it (second disjunct)
///   - In a promoted object body → the promoted object is in farr (first disjunct)
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
/// Case A helper: obj was pre-existing non-blue in major_pre
private let derive_fwd_case_a
  (minor: minor_state) (major_pre: heap_state) (fp: U64.t) (roots: Seq.seq U64.t)
  (farr: Seq.seq U64.t) (slots: Seq.seq U64.t) (n: nat)
  (obj: GC.Spec.Base.obj_addr) (j: nat)
  : Lemma (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       let major_final = prom.major_final in
       let fwd = prom.fwd_map in
       Seq.length farr == fwd_array_size /\
       represents_fwd farr fwd /\
       SpecFields.well_formed_heap major_pre /\
       AllocLemmas.fl_valid major_pre fp heap_words /\
       AllocLemmas.fl_chain_terminates major_pre fp heap_words /\
       PromoteSpec.chain_objects_blue major_pre fp /\
       minor_infix_wf minor /\
       n <= Seq.length slots /\
       ref_table_complete major_pre fwd slots n /\
       // obj is pre-existing non-blue
       Seq.mem obj (SpecFields.objects zero_addr major_pre) /\
       SpecObj.is_blue obj major_pre = false /\
       // Field preconditions (from the universal)
       Seq.mem obj (SpecFields.objects zero_addr major_final) /\
       SpecObj.is_blue obj major_final = false /\
        SpecObj.is_no_scan obj major_final = false /\
        j < U64.v (SpecObj.wosize_of_object obj major_final) /\
        U64.v obj + j * 8 + 8 <= heap_size /\
        (U64.v obj + j * 8) % 8 == 0 /\
        (let a = U64.v obj + j * 8 in
         let field_val = to_minor_offset
          (GC.Spec.Heap.read_word major_final (U64.uint_to_t a)) in
        PromoteSpec.is_minor_pointer field_val /\ fwd field_val <> 0UL)))
    (ensures
      (exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj) \/
      (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == U64.v obj + j * 8))
  = let prom = CheneySpec.cheney_promote minor major_pre fp roots in
    let major_final = prom.major_final in
    let fwd = prom.fwd_map in
    let a = U64.v obj + j * 8 in
    ML.lemma_mod_plus (U64.v obj) j 8;
    // Frame: header is preserved
    CheneyPres.cheney_promote_frame_old_header minor major_pre fp roots obj;
    let hdr_eq : squash (GC.Spec.Heap.read_word major_final (GC.Spec.Heap.hd_address obj)
                      == GC.Spec.Heap.read_word major_pre (GC.Spec.Heap.hd_address obj)) = () in
    // Derive wosize equality
    SpecObj.wosize_of_object_spec obj major_final;
    SpecObj.wosize_of_object_spec obj major_pre;
    assert (SpecObj.wosize_of_object obj major_final == SpecObj.wosize_of_object obj major_pre);
    // Derive is_no_scan equality (same tag from same header)
    SpecObj.is_no_scan_spec obj major_final;
    SpecObj.is_no_scan_spec obj major_pre;
    SpecObj.tag_of_object_spec obj major_final;
    SpecObj.tag_of_object_spec obj major_pre;
    assert (SpecObj.is_no_scan obj major_pre = false);
    // Frame: field value preserved
    CheneyPres.cheney_promote_frame_old_fields minor major_pre fp roots obj j;
    assert (GC.Spec.Heap.read_word major_final (U64.uint_to_t a)
         == GC.Spec.Heap.read_word major_pre (U64.uint_to_t a));
    // ref_table_complete at (obj, j): all preconditions hold for major_pre
    assert (j < U64.v (SpecObj.wosize_of_object obj major_pre));
    let field_val = to_minor_offset (GC.Spec.Heap.read_word major_pre (U64.uint_to_t a)) in
    assert (PromoteSpec.is_minor_pointer field_val /\ fwd field_val <> 0UL);
    // ref_table_complete gives us the slot witness
    assert (exists (i: nat). i < n /\ U64.v (Seq.index slots i) == U64.v obj + j * 8)

/// Case B helper: obj is a newly promoted object (not pre-existing non-blue)
private let derive_fwd_case_b
  (minor: minor_state) (major_pre: heap_state) (fp: U64.t) (roots: Seq.seq U64.t)
  (farr: Seq.seq U64.t) (slots: Seq.seq U64.t) (n: nat)
  (obj: GC.Spec.Base.obj_addr) (j: nat)
  : Lemma (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       let major_final = prom.major_final in
       let fwd = prom.fwd_map in
       Seq.length farr == fwd_array_size /\
       represents_fwd farr fwd /\
       SpecFields.well_formed_heap major_pre /\
       SpecFields.well_formed_heap_part1 major_final /\
       AllocLemmas.fl_valid major_pre fp heap_words /\
       AllocLemmas.fl_chain_terminates major_pre fp heap_words /\
       PromoteSpec.chain_objects_blue major_pre fp /\
       minor_infix_wf minor /\
       minor_wf minor /\
       n <= Seq.length slots /\
       // NOT pre-existing non-blue
       ~(Seq.mem obj (SpecFields.objects zero_addr major_pre) /\
         SpecObj.is_blue obj major_pre = false) /\
       // obj is non-blue in major_final
       Seq.mem obj (SpecFields.objects zero_addr major_final) /\
       SpecObj.is_blue obj major_final = false))
    (ensures
      (exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj) \/
      (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == U64.v obj + j * 8))
  = let prom = CheneySpec.cheney_promote minor major_pre fp roots in
    let fwd = prom.fwd_map in
    // nonblue_origin: obj is a forwarding target
    CheneyPres.cheney_promote_nonblue_origin minor major_pre fp roots obj;
    // Get witness: exists x. fwd x == obj /\ is_minor_pointer x
    let x : U64.t = IndDesc.indefinite_description_ghost U64.t
      (fun x -> fwd x == obj /\ PromoteSpec.is_minor_pointer x) in
    assert (fwd x == obj /\ PromoteSpec.is_minor_pointer x);
    // is_minor_pointer x means: U64.v x >= 8 /\ U64.v x < minor_heap_size /\ U64.v x % 8 == 0
    assert (U64.v x % 8 == 0);
    assert (U64.v x >= 8);
    assert (U64.v x < minor_heap_size);
    // pi = U64.v x / 8
    let pi = U64.v x / 8 in
    assert (pi >= 1);
    // x < minor_heap_size and x % 8 == 0 implies x <= minor_heap_size - 8
    // hence x/8 <= (minor_heap_size - 8)/8 = minor_heap_size/8 - 1 < fwd_array_size
    FStar.Math.Lemmas.lemma_div_le (U64.v x) (minor_heap_size - 8) 8;
    assert (pi <= (minor_heap_size - 8) / 8);
    assert (pi < fwd_array_size);
    // From x % 8 == 0: pi * 8 == U64.v x
    FStar.Math.Lemmas.lemma_div_exact (U64.v x) 8;
    assert (pi * 8 == U64.v x);
    assert (U64.uint_to_t (pi * 8) == x);
    // From represents_fwd: farr[pi] == fwd(uint_to_t(pi * 8)) == fwd x == obj
    assert (Seq.index farr pi == fwd x);
    assert (Seq.index farr pi == obj)

/// Point-wise helper: combines case A and B with the mod_plus arithmetic
private let derive_fwd_ptrs_classified_pointwise
  (minor: minor_state) (major_pre: heap_state) (fp: U64.t) (roots: Seq.seq U64.t)
  (farr: Seq.seq U64.t) (slots: Seq.seq U64.t) (n: nat)
  (obj: GC.Spec.Base.obj_addr) (j: nat)
  : Lemma (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       let major_final = prom.major_final in
       let fwd = prom.fwd_map in
       Seq.length farr == fwd_array_size /\
       represents_fwd farr fwd /\
       SpecFields.well_formed_heap major_pre /\
       SpecFields.well_formed_heap_part1 major_final /\
       AllocLemmas.fl_valid major_pre fp heap_words /\
       AllocLemmas.fl_chain_terminates major_pre fp heap_words /\
       PromoteSpec.chain_objects_blue major_pre fp /\
       minor_infix_wf minor /\
       minor_wf minor /\
       n <= Seq.length slots /\
       ref_table_complete major_pre fwd slots n /\
       ref_table_sound major_pre slots n /\
       Seq.mem obj (SpecFields.objects zero_addr major_final) /\
       SpecObj.is_blue obj major_final = false /\
        SpecObj.is_no_scan obj major_final = false /\
        j < U64.v (SpecObj.wosize_of_object obj major_final) /\
        U64.v obj + j * 8 + 8 <= heap_size /\
        (U64.v obj + j * 8) % 8 == 0 /\
        (let a = U64.v obj + j * 8 in
         let field_val = to_minor_offset
          (GC.Spec.Heap.read_word major_final (U64.uint_to_t a)) in
        PromoteSpec.is_minor_pointer field_val /\ fwd field_val <> 0UL)))
    (ensures
      (exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj) \/
      (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == U64.v obj + j * 8))
  = ML.lemma_mod_plus (U64.v obj) j 8;
    if IndDesc.strong_excluded_middle
      (Seq.mem obj (SpecFields.objects zero_addr major_pre) /\
       SpecObj.is_blue obj major_pre = false)
    then
      derive_fwd_case_a minor major_pre fp roots farr slots n obj j
    else
      derive_fwd_case_b minor major_pre fp roots farr slots n obj j
#pop-options

#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let derive_fwd_ptrs_classified
  (minor: minor_state) (major_pre: heap_state) (fp: U64.t) (roots: Seq.seq U64.t)
  (farr: Seq.seq U64.t) (slots: Seq.seq U64.t) (n: nat)
  : Lemma (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       Seq.length farr == fwd_array_size /\
       represents_fwd farr prom.fwd_map /\
       SpecFields.well_formed_heap major_pre /\
       SpecFields.well_formed_heap_part1 prom.major_final /\
       AllocLemmas.fl_valid major_pre fp heap_words /\
       AllocLemmas.fl_chain_terminates major_pre fp heap_words /\
       PromoteSpec.chain_objects_blue major_pre fp /\
       minor_infix_wf minor /\
       minor_wf minor /\
       n <= Seq.length slots /\
       ref_table_complete major_pre prom.fwd_map slots n /\
       ref_table_sound major_pre slots n))
    (ensures (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
              fwd_ptrs_classified prom.major_final prom.fwd_map farr slots n))
  = let aux (obj: GC.Spec.Base.obj_addr) (j: nat) : Lemma
      (ensures
        (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
         let major_final = prom.major_final in
         let fwd = prom.fwd_map in
         Seq.mem obj (SpecFields.objects zero_addr major_final) /\
         SpecObj.is_blue obj major_final = false /\
         SpecObj.is_no_scan obj major_final = false /\
         j < U64.v (SpecObj.wosize_of_object obj major_final) /\
         U64.v obj + j * 8 + 8 <= heap_size /\
         (U64.v obj + j * 8) % 8 == 0 /\
         (let field_val = to_minor_offset
           (GC.Spec.Heap.read_word major_final (U64.uint_to_t (U64.v obj + j * 8))) in
          PromoteSpec.is_minor_pointer field_val /\ fwd field_val <> 0UL) ==>
         ((exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj) \/
          (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == U64.v obj + j * 8))))
    = let prom = CheneySpec.cheney_promote minor major_pre fp roots in
      let major_final = prom.major_final in
      let fwd = prom.fwd_map in
      if Seq.mem obj (SpecFields.objects zero_addr major_final) &&
         SpecObj.is_blue obj major_final = false &&
         SpecObj.is_no_scan obj major_final = false &&
         j < U64.v (SpecObj.wosize_of_object obj major_final) &&
         U64.v obj + j * 8 + 8 <= heap_size &&
         (U64.v obj + j * 8) % 8 = 0
      then begin
        let a = U64.v obj + j * 8 in
        ML.lemma_mod_plus (U64.v obj) j 8;
        assert (a < heap_size);
        assert (a % 8 == 0);
        let field_val = to_minor_offset (GC.Spec.Heap.read_word major_final (U64.uint_to_t a)) in
        if PromoteSpec.is_minor_pointer field_val && fwd field_val <> 0UL then
          derive_fwd_ptrs_classified_pointwise minor major_pre fp roots farr slots n obj j
      end
    in
    Classical.forall_intro_2 aux
#pop-options

/// Bridge lemma: conditional two-pass ↔ full-update equivalence.
/// Derives promoted_entries_valid_from, promoted_entries_disjoint, and
/// fwd_ptrs_classified internally from Cheney BFS properties.
let two_pass_implies_full_update
  (minor: minor_state) (major_pre: heap_state) (fp: U64.t) (roots: Seq.seq U64.t)
  (farr: Seq.seq U64.t) (slots: Seq.seq U64.t) (n: nat)
  : Lemma
    (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       Seq.length farr == fwd_array_size /\
       represents_fwd farr prom.fwd_map /\
       CheneyPres.fwd_valid_or_infix prom.fwd_map prom.major_final /\
       CheneyPres.fwd_normal_injective prom.fwd_map prom.major_final /\
       CheneySpec.fwd_bounded prom.fwd_map /\
       SpecFields.well_formed_heap_part4 prom.major_final /\
       valid_slot_addrs slots n /\
       slots_pairwise_distinct slots n /\
       ref_table_sound major_pre slots n /\
       ref_table_complete major_pre prom.fwd_map slots n /\
       fwd_targets_stable prom.fwd_map /\
       SpecFields.well_formed_heap_part1 prom.major_final /\
       PromoteSpec.heap_objects_dense prom.major_final /\
       Seq.length (SpecFields.objects zero_addr prom.major_final) > 0 /\
       SpecFields.well_formed_heap major_pre /\
       minor_infix_wf minor /\
       minor_wf minor /\
       PromoteSpec.chain_objects_blue major_pre fp /\
       AllocLemmas.fl_valid major_pre fp TwoPass.heap_fuel /\
       AllocLemmas.fl_chain_terminates major_pre fp TwoPass.heap_fuel))
    (ensures
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       rewrite_slots_iter
         (update_promoted_iter prom.major_final farr prom.fwd_map 0)
         prom.fwd_map slots n 0
       == (CheneySpec.cheney_collect_spec minor major_pre fp roots).mc_major))
  = let prom = CheneySpec.cheney_promote minor major_pre fp roots in
    derive_promoted_entries_valid_from prom.major_final farr prom.fwd_map;
    derive_promoted_entries_disjoint prom.major_final farr prom.fwd_map;
    CheneyPres.cheney_promote_fwd_targets_not_blue minor major_pre fp roots;
    derive_promoted_entries_not_blue prom.major_final farr prom.fwd_map;
    derive_slots_scannable_in_major minor major_pre fp roots slots n;
    derive_fwd_ptrs_classified minor major_pre fp roots farr slots n;
    TwoPass.promoted_plus_slots_eq_full_update minor major_pre fp roots farr slots n;
    cheney_collect_spec_unfold minor major_pre fp roots

#push-options "--z3rlimit 10 --fuel 0 --ifuel 1"
let minor_collect_full_isomorphism_post
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: Seq.seq U64.t) (n: nat) (ok: bool)
  (post_major: heap) (post_roots: Seq.seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      ref_table_covers_minor_ptrs major slots n /\
      post_major == (CheneySpec.cheney_collect_spec minor major fp roots).mc_major /\
      post_roots == PromoteSpec.rewrite_roots roots
        (CheneySpec.cheney_promote minor major fp roots).fwd_map /\
      MinorFwd.remembered_targets_in_roots major roots slots n /\
      MinorFwd.roots_valid_for_minor_collection minor major roots /\
      (ok ==> CheneyBFS.cheney_no_oom minor major fp roots))
    (ensures
      (ok ==>
       MinorFwd.normal_result_reachable_subgraph_isomorphism_prop
         minor major fp roots post_major post_roots /\
       MinorFwd.normal_result_non_pointer_fields_preserved_prop
         minor major fp roots post_major))
  =
    if ok
    then begin
      MCFH.roots_valid_for_minor_collection_nonblue minor major roots;
      MCFH.major_field_zero_covered_from_slots minor major roots slots n;
      GenInv.collection_heap_shape_elim minor major fp;
      GenInv.major_heap_shape_elim major fp;
      RBridge.minor_no_pointer_to_blue_from_collection_shape minor major fp;
      assert (CheneyBFS.cheney_no_oom minor major fp roots);
      MinorFwd.normal_post_reachable_subgraph_isomorphism
        minor major fp roots slots n;
      MinorFwd.normal_post_reachable_subgraph_isomorphism_to_result
        minor major fp roots post_major post_roots;
      MinorFwd.normal_post_non_pointer_fields_preserved
        minor major fp roots slots n;
      MinorFwd.normal_post_non_pointer_fields_preserved_to_result
        minor major fp roots post_major
    end
#pop-options

/// ---------------------------------------------------------------------------
/// minor_collect_full: includes ref_table rewriting for full correctness
/// ---------------------------------------------------------------------------

/// Compose all phases into a single verified call that achieves full
/// cheney_collect_spec correctness.  Takes a ref_table (slots array) that
/// covers all major-heap fields holding minor pointers (not belonging to
/// promoted objects — those are handled by update_promoted_objects).
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
fn minor_collect_full (gh: gen_heap_t)
                      (roots: array U64.t) (nroots: SZ.t)
                      (fwd_arr: array U64.t)
                      (queue: larray U64.t Cheney.queue_size)
                      (slots: array U64.t) (nslots: SZ.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
            pure (GenInv.collection_heap_shape
                    ({ data = 'd; bump = 'b } <: minor_state) 's 'fp /\
                  SZ.v nroots == Seq.length 'rs /\
                  Seq.length 'farr == fwd_array_size /\
                  (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
                  ref_table_sound 's 'sl (SZ.v nslots) /\
                  ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
                  slots_pairwise_distinct 'sl (SZ.v nslots) /\
                  MinorFwd.remembered_targets_in_roots 's 'rs 'sl (SZ.v nslots) /\
                  MinorFwd.roots_valid_for_minor_collection
                    ({ data = 'd; bump = 'b } <: minor_state) 's 'rs)
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2.
    is_gen_heap gh d2 b2 s2 fp2 **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let prom = CheneySpec.cheney_promote minor_st 's 'fp 'rs in
      // Heap is the two-pass result (update promoted + rewrite slots)
      s2 == rewrite_slots_iter
              (update_promoted_iter prom.major_final farr2 prom.fwd_map 0)
              prom.fwd_map 'sl (SZ.v nslots) 0 /\
      // Free pointer from promotion phase
      fp2 == prom.fp_final /\
      // Roots rewritten via forwarding map
      rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\
      // Minor heap fully reset
      U64.v b2 == 0 /\
      // Forwarding array represents the spec-level forwarding map
      represents_fwd farr2 prom.fwd_map /\
      // Forwarding entries are valid
      valid_fwd_entries farr2 /\
      Seq.length farr2 == fwd_array_size /\
      // Well-formedness preserved through promotion
      SpecFields.well_formed_heap_part1 prom.major_final /\
      // Strong correctness: the result equals cheney_collect_spec.mc_major.
      s2 == (CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs).mc_major /\
      GenInv.collection_heap_shape ({ data = d2; bump = b2 } <: minor_state) s2 fp2 /\
      (not ok ==> CheneyBFS.cheney_oom minor_st 's 'fp 'rs) /\
      (ok ==>
       CheneyBFS.cheney_no_oom minor_st 's 'fp 'rs /\
       MinorFwd.normal_result_reachable_subgraph_isomorphism_prop
         minor_st 's 'fp 'rs s2 rs2 /\
        MinorFwd.normal_result_non_pointer_fields_preserved_prop
         minor_st 's 'fp 'rs s2))
{
  unfold is_gen_heap;
  MCFH.major_field_zero_covered_from_slots
    ({data = 'd; bump = 'b} <: minor_state) 's 'rs 'sl (SZ.v nslots);
  GenInv.collection_heap_shape_elim ({data = 'd; bump = 'b} <: minor_state) 's 'fp;
  GenInv.major_heap_shape_elim 's 'fp;
  GenInv.minor_heap_shape_elim ({data = 'd; bump = 'b} <: minor_state);

  // Phase 1: Cheney BFS promotion (forward roots + scan)
  let ok = cheney_promote_phase gh.minor gh.major gh.fp_ref fwd_arr queue roots nroots;

  // Extract ghost state from promote phase
  with ms_post. assert (is_heap gh.major ms_post);
  with farr_post. assert (pts_to fwd_arr farr_post);
  with fp_post. assert (R.pts_to gh.fp_ref fp_post);

  // Phase 2: Update promoted objects' fields only (efficient path)
  CheneySpec.cheney_promote_fwd_bounded
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  fwd_bounded_implies_valid_fwd_entries farr_post
    (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map;

  update_promoted_objects gh.major fwd_arr
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // After update: ms_updated == update_promoted_iter ms_post farr_post prom_fwd 0
  with ms_updated. assert (is_heap gh.major ms_updated);
  with farr_post2. assert (pts_to fwd_arr farr_post2);

  // Phase 2b: Rewrite ref_table slots for full correctness
  ref_table_sound_implies_valid_slot_addrs 's 'sl (SZ.v nslots);
  rewrite_heap_slots gh.major fwd_arr slots nslots
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // After slot rewrite: heap is the two-pass result
  with ms_final. assert (is_heap gh.major ms_final);

  // Phase 3: Rewrite roots using ghost-tracked forwarding map
  with farr_post3. assert (pts_to fwd_arr farr_post3);
  rewrite_roots_impl roots fwd_arr nroots
    #(hide (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  // Phase 4: Reset minor heap
  minor_heap_reset gh.minor;

  // Prove the full-update equivalence for the strong spec. The slot table is
  // pairwise distinct by precondition; all other conditions are derived here.
  CheneySpec.cheney_promote_fwd_above_zero_addr
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  derive_fwd_targets_stable
    (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map;
  ref_table_covers_minor_ptrs_implies_complete
    's
    (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map
    'sl
    (SZ.v nslots);
  CheneySpec.cheney_promote_preserves_wfh_part4
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  CheneyPres.cheney_promote_fwd_valid_or_infix
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  CheneyPres.cheney_promote_fwd_normal_injective
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  CheneySpec.cheney_promote_fwd_bounded
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  CheneySpec.cheney_promote_preserves_dense
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  Classical.move_requires
    (two_pass_implies_full_update
       ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs farr_post3 'sl)
    (SZ.v nslots);
  CheneyPres.cheney_collect_preserves_collection_heap_shape
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  minor_collect_full_isomorphism_post
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'sl (SZ.v nslots) ok
    ms_final
    (PromoteSpec.rewrite_roots 'rs
      (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map);

  fold (is_gen_heap gh _ 0UL _ _);
  ok
}
#pop-options

/// ---------------------------------------------------------------------------
/// Full generational GC (minor collection + major collection)
/// ---------------------------------------------------------------------------

/// gen_gc composes the verified full minor collection with mark-and-sweep.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
fn gen_gc (gh: gen_heap_t)
           (roots: array U64.t) (nroots: SZ.t)
           (fwd_arr: array U64.t)
           (queue: larray U64.t Cheney.queue_size)
           (slots: array U64.t) (nslots: SZ.t)
           (st: gray_stack)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to slots 'sl **
           is_gray_stack st 'st **
             pure (
               let minor_st : minor_state = { data = 'd; bump = 'b } in
               GenInv.collection_heap_shape minor_st 's 'fp /\
               gen_gc_stack_budget 'rs 'st (stack_capacity st) /\
               SZ.v nroots == Seq.length 'rs /\
               Seq.length 'farr == fwd_array_size /\
               (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
               ref_table_sound 's 'sl (SZ.v nslots) /\
               ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
               slots_pairwise_distinct 'sl (SZ.v nslots) /\
               MinorFwd.remembered_targets_in_roots 's 'rs 'sl (SZ.v nslots) /\
               MinorFwd.roots_valid_for_minor_collection
                 ({ data = 'd; bump = 'b } <: minor_state) 's 'rs)
  returns res: (U64.t & bool)
  ensures exists* d2 b2 s2 rs2 farr2 qv2 st2.
    is_gen_heap gh d2 b2 s2 (fst res) **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to slots 'sl **
    is_gray_stack st st2 **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let result = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
      let ok = snd res in
      // Failure is reported only for a concrete out-of-memory event: an object
      // the major free list had no room for, at a point of this collection.
      (not ok ==> CheneyBFS.cheney_oom minor_st 's 'fp 'rs) /\
      gen_gc_roots_post minor_st 's 'fp 'rs rs2 ok 'st (stack_capacity st) /\
      gen_gc_heap_shape_post d2 b2 s2 /\
      gen_gc_reachable_subgraph_isomorphism_post
        minor_st 's 'fp 'rs ok s2 rs2 'st (stack_capacity st) /\
      gen_gc_unreachable_final_blue_post
        minor_st 's 'fp 'rs ok s2 'st (stack_capacity st))
{
  GenInv.collection_heap_shape_elim ({data = 'd; bump = 'b} <: minor_state) 's 'fp;
  GenInv.major_heap_shape_elim 's 'fp;
  GenInv.minor_heap_shape_elim ({data = 'd; bump = 'b} <: minor_state);

  // Phase 1: Full minor collection, including remembered-set slot rewriting.
  let ok = minor_collect_full gh roots nroots fwd_arr queue slots nslots;

  with d_mid b_mid ms_updated fp_mid. assert (is_gen_heap gh d_mid b_mid ms_updated fp_mid);
  with rs_mid. assert (pts_to roots rs_mid);
  with farr_mid. assert (pts_to fwd_arr farr_mid);
  with qv_mid. assert (pts_to queue qv_mid);
  assert (pts_to slots 'sl);

  unfold is_gen_heap;
  let fp_val = R.op_Bang gh.fp_ref;
  assert (pure (fp_val == fp_mid));

  assert (pure (ms_updated ==
    (CheneySpec.cheney_collect_spec ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).mc_major));
  assert (pure (fp_val ==
    (CheneySpec.cheney_collect_spec ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).mc_fp));
  cheney_collect_spec_unfold ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  CheneyCorr.cheney_collect_preserves_objects
    ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs;
  assert (pure (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr 's) ==>
    Seq.mem x (SpecFields.objects zero_addr ms_updated)));
  assert (pure (GenInv.collection_heap_shape
    ({ data = d_mid; bump = b_mid } <: minor_state) ms_updated fp_val));
  assert (pure (GenInv.collection_heap_shape
    ({ data = d_mid; bump = b_mid } <: minor_state) ms_updated fp_mid));
  assert (pure (rs_mid ==
    (CheneySpec.cheney_collect_spec ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).mc_roots));
  assert (pure (rs_mid ==
    PromoteSpec.rewrite_roots 'rs
      (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map));
  PromoteSpec.rewrite_roots_length 'rs
    (CheneySpec.cheney_promote ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).fwd_map;
  assert (pure (SZ.v nroots == Seq.length rs_mid));
  assert (pure (U64.v b_mid == 0));
  GenInv.collection_heap_shape_elim ({ data = d_mid; bump = b_mid } <: minor_state)
    ms_updated fp_val;
  assert (pure (GenInv.major_heap_shape ms_updated fp_val));
  GenInv.major_heap_shape_elim ms_updated fp_val;
  assert (pure (SpecFields.well_formed_heap ms_updated));
  wfh_implies_part1 ms_updated;
  assert (pure (SpecFields.well_formed_heap_part1 ms_updated));
  assert (pure (SpecFields.well_formed_heap_part1
    (CheneySpec.cheney_collect_spec ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs).mc_major));
  // Phase 2: Major collection, but only if the minor collection succeeded.
  //
  // On the out-of-memory path some live nursery objects were never promoted, so
  // the rewritten root set still contains nursery addresses and there is nothing
  // sensible for mark-and-sweep to do with it.  `minor_collect_full` reports
  // that through `ok`, which also witnesses `cheney_no_oom` -- the fact the
  // major phase's entry condition is derived from.  This is why `gen_gc`'s
  // caller does not have to establish `cheney_no_oom` itself.
  if ok {
    MarkBoundedImpl.darken_roots_bounded gh.major st roots nroots (stack_capacity st);
    with prepared_major prepared_st roots_after. assert (
      is_heap gh.major prepared_major **
      is_gray_stack st prepared_st **
      pts_to roots roots_after);
    assert (pure (roots_after == rs_mid));
    assert (pure ((prepared_major, prepared_st) ==
      gen_gc_prepared_state
        ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'st (stack_capacity st)));
    gen_gc_major_precondition_elim
      ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'st (stack_capacity st);
    assert (pure (MajorGC.gc_precondition_with_roots
      prepared_major prepared_st prepared_st fp_val (stack_capacity st)));
    assert (pure (roots_match_stack rs_mid prepared_st));
    // Phase 2: Major collection (mark + sweep + coalesce)
    let final_fp = MajorGC.collect_with_roots gh.major st prepared_st fp_val;

    with s_final st_final. assert (
      is_heap gh.major s_final **
      is_gray_stack st st_final);
    assert (pure (SpecGCPost.gc_postcondition s_final));
    assert (pure (SpecGCPost.full_gc_correctness prepared_major s_final prepared_st));
    assert (pure (SpecGCPost.major_gc_live_subgraph_isomorphism
      prepared_major s_final prepared_st));
    assert (pure (SpecGCPost.major_gc_unreachable_final_blue
      prepared_major s_final prepared_st));
    assert (pure (SpecGCPost.major_gc_live_subgraph_isomorphism
      (fst (gen_gc_prepared_state
        ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'st (stack_capacity st)))
      s_final
      (snd (gen_gc_prepared_state
        ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'st (stack_capacity st)))));
    assert (pure (SpecGCPost.major_gc_unreachable_final_blue
      (fst (gen_gc_prepared_state
        ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'st (stack_capacity st)))
      s_final
      (snd (gen_gc_prepared_state
        ({data = 'd; bump = 'b} <: minor_state) 's 'fp 'rs 'st (stack_capacity st)))));

    // Phase 6: Update free-list pointer and re-fold gen heap
    R.op_Colon_Equals gh.fp_ref final_fp;

    fold (is_gen_heap gh d_mid b_mid s_final final_fp);    (final_fp, ok)
  } else {
    // Nothing ran after the minor collection, so the heap we hand back is the
    // post-minor one.  It is already white/blue everywhere -- `major_heap_shape`
    // records both `no_black_objects` and `no_gray_objects` -- so it satisfies
    // the major-GC postcondition on its own, and every `ok`-guarded conjunct is
    // vacuous.
    GMP.major_heap_shape_gc_postcondition ms_updated fp_val;
    fold (is_gen_heap gh d_mid b_mid ms_updated fp_val);
    (fp_val, ok)
  }
}
#pop-options
