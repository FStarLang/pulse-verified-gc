/// ---------------------------------------------------------------------------
/// GC.Gen.TwoPassEquiv.Collect -- Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.TwoPassEquiv.Collect

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Impl.UpdatePtrs

module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneySpec = GC.Gen.Cheney
module CheneyPres = GC.Gen.CheneyPreservation
module TwoPass = GC.Gen.TwoPassEquiv
module SpecFields = GC.Spec.Fields
module SpecObj = GC.Spec.Object
module ML = FStar.Math.Lemmas
module IndDesc = FStar.IndefiniteDescription
module Classical = FStar.Classical
module Aux = GC.Gen.PromoteUpdate.Aux
module Inj = GC.Gen.CheneyPreservation.Injectivity
module CE = GC.Gen.CheneyExcept
module PromoteSpec = GC.Gen.Promote

let ref_table_covers_except_implies_complete major_pre pf fwd slots n = ()

let ref_table_covers_except_no_pending major_pre slots n = ()

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let ref_table_sound_except_implies_fwd major_pre pf fwd slots n =
  let aux (i: nat) : Lemma
    (i < n ==>
      (let addr = U64.v (Seq.index slots i) in
       addr < heap_size /\ addr % 8 == 0 /\
       (exists (obj: obj_addr) (j: nat).
         Seq.mem obj (objects zero_addr major_pre) /\
         is_blue obj major_pre = false /\
         is_no_scan obj major_pre = false /\
         j < U64.v (wosize_of_object obj major_pre) /\
         addr == U64.v obj + j * 8 /\
         (~(pf obj) \/
          ~(TwoPass.holds_forwarded major_pre fwd (U64.uint_to_t addr))))))
    = ()
  in
  Classical.forall_intro aux

let ref_table_sound_except_no_pending major_pre slots n =
  let aux (i: nat) : Lemma
    (i < n ==>
      (let addr = U64.v (Seq.index slots i) in
       addr < heap_size /\ addr % 8 == 0 /\
       (exists (obj: obj_addr) (j: nat).
         Seq.mem obj (objects zero_addr major_pre) /\
         is_blue obj major_pre = false /\
         is_no_scan obj major_pre = false /\
         j < U64.v (wosize_of_object obj major_pre) /\
         addr == U64.v obj + j * 8 /\
         (~(no_pending obj) \/
          ~(is_minor_pointer (to_minor_offset (read_word major_pre (U64.uint_to_t addr))))))))
    = ()
  in
  Classical.forall_intro aux
#pop-options

/// Derivation: fwd_valid_or_infix + wfh_part1 + fwd_bounded + represents_fwd
/// implies promoted_entries_valid_from.
/// Each non-zero farr entry fwd(i*8) has valid bounds (from fwd_bounded),
/// and is either in objects (with wosize bounds from wfh_part1) or is_infix.
#push-options "--z3rlimit 15 --fuel 0 --ifuel 0"
let derive_promoted_entries_valid_from
  (major: heap) (farr: Seq.seq U64.t) (fwd: PromoteSpec.forwarding_map)
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
  (major: heap) (farr: Seq.seq U64.t) (fwd: PromoteSpec.forwarding_map)
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


/// ---------------------------------------------------------------------------
/// The hypotheses of the two passes, at the Cheney result
/// ---------------------------------------------------------------------------
///
/// The walk of `cheney_collect_spec_except` rewrites the not-freed objects of
/// the promoted heap: `upd = not_freed prom.major_final pf`.

/// A non-infix entry of the forwarding array is the image of a nursery object,
/// so it is not freed after promotion.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let derive_promoted_entries_walked
  (minor: minor_state) (major_pre: heap) (fp: U64.t) (roots: seq U64.t)
  (pf: obj_addr -> prop) (farr: seq U64.t)
  : Lemma
    (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       CE.promote_pre minor major_pre fp /\
       pending_ok major_pre pf /\
       Seq.length farr == fwd_array_size /\
       represents_fwd farr prom.fwd_map))
    (ensures
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       TwoPass.promoted_entries_walked prom.major_final
         (not_freed prom.major_final pf) farr))
  = let prom = CheneySpec.cheney_promote minor major_pre fp roots in
    let fwd = prom.fwd_map in
    Inj.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major_pre fp roots;
    let aux (i: nat) : Lemma
      (i < fwd_array_size ==>
        (let obj = Seq.index farr i in
         obj <> 0UL /\
         U64.v obj >= U64.v mword /\
         U64.v obj % U64.v mword == 0 /\
         U64.v obj < heap_size /\
         is_infix obj prom.major_final = false ==>
         not_freed prom.major_final pf (obj <: obj_addr)))
    = if i < fwd_array_size then begin
        let obj = Seq.index farr i in
        if obj <> 0UL && U64.v obj >= U64.v mword && U64.v obj % U64.v mword = 0 &&
           U64.v obj < heap_size && is_infix obj prom.major_final = false
        then begin
          let x = U64.uint_to_t (i * 8) in
          assert (fwd x == obj);
          is_val_addr_spec obj;
          assert (Seq.mem x (minor_objects minor));
          CE.cheney_promote_image_not_freed minor major_pre fp roots pf x obj
        end
      end
    in
    Classical.forall_intro aux
#pop-options

/// A slot is a field of an old non-free object: a field of a not-freed one is
/// a field of a not-freed object after promotion, and one in a pending object
/// still holds no forwarded pointer, since promotion does not write old objects.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let derive_slot_rewrite_walked
  (minor: minor_state) (major_pre: heap) (fp: U64.t) (roots: seq U64.t)
  (pf: obj_addr -> prop) (a: nat) (obj: obj_addr) (j: nat)
  : Lemma
    (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       CE.promote_pre minor major_pre fp /\
       a < heap_size /\ a % 8 == 0 /\
       Seq.mem obj (objects zero_addr major_pre) /\
       is_blue obj major_pre = false /\
       is_no_scan obj major_pre = false /\
       j < U64.v (wosize_of_object obj major_pre) /\
       a == U64.v obj + j * 8 /\
       (~(pf obj) \/ ~(TwoPass.holds_forwarded major_pre prom.fwd_map (U64.uint_to_t a)))))
    (ensures
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       TwoPass.walked_field_addr prom.major_final (not_freed prom.major_final pf) a \/
       ~(TwoPass.holds_forwarded prom.major_final prom.fwd_map (U64.uint_to_t a))))
  = let prom = CheneySpec.cheney_promote minor major_pre fp roots in
    SpecFields.wfh_part1_obj_bound major_pre obj;
    ML.lemma_mod_plus (U64.v obj) j 8;
    assert (U64.v obj + j * 8 + 8 <= heap_size);
    CheneySpec.cheney_promote_preserves_objects minor major_pre fp roots;
    CheneyPres.cheney_promote_frame_old_header minor major_pre fp roots obj;
    Aux.header_eq_object_facts prom.major_final major_pre obj;
    if IndDesc.strong_excluded_middle (pf obj) then begin
      CheneyPres.cheney_promote_frame_old_fields minor major_pre fp roots obj j;
      assert (U64.uint_to_t a == U64.uint_to_t (U64.v obj + j * 8))
    end else
      assert (TwoPass.walked_field_addr prom.major_final (not_freed prom.major_final pf) a)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let derive_slots_rewrite_walked
  (minor: minor_state) (major_pre: heap) (fp: U64.t) (roots: seq U64.t)
  (pf: obj_addr -> prop) (slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       CE.promote_pre minor major_pre fp /\
       ref_table_sound_fwd_except major_pre pf prom.fwd_map slots n))
    (ensures
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       TwoPass.slots_rewrite_walked prom.major_final
         (not_freed prom.major_final pf) prom.fwd_map slots n))
  = let prom = CheneySpec.cheney_promote minor major_pre fp roots in
    let aux (i: nat) : Lemma
      (i < n ==>
        (let a = U64.v (Seq.index slots i) in
         a < heap_size /\ a % 8 == 0 /\
         (TwoPass.walked_field_addr prom.major_final (not_freed prom.major_final pf) a \/
          ~(TwoPass.holds_forwarded prom.major_final prom.fwd_map (U64.uint_to_t a)))))
    = if i < n then begin
        let a = U64.v (Seq.index slots i) in
        let obj : obj_addr = IndDesc.indefinite_description_ghost obj_addr (fun obj ->
          exists (j: nat).
            Seq.mem obj (objects zero_addr major_pre) /\
            is_blue obj major_pre = false /\
            is_no_scan obj major_pre = false /\
            j < U64.v (wosize_of_object obj major_pre) /\
            a == U64.v obj + j * 8 /\
            (~(pf obj) \/ ~(TwoPass.holds_forwarded major_pre prom.fwd_map (U64.uint_to_t a)))) in
        let j : nat = IndDesc.indefinite_description_ghost nat (fun j ->
            Seq.mem obj (objects zero_addr major_pre) /\
            is_blue obj major_pre = false /\
            is_no_scan obj major_pre = false /\
            j < U64.v (wosize_of_object obj major_pre) /\
            a == U64.v obj + j * 8 /\
            (~(pf obj) \/ ~(TwoPass.holds_forwarded major_pre prom.fwd_map (U64.uint_to_t a)))) in
        derive_slot_rewrite_walked minor major_pre fp roots pf a obj j
      end
    in
    Classical.forall_intro aux
#pop-options

/// A forwarded field of a not-freed object after promotion is in a promoted
/// object (the object is the image of a nursery object) or at a slot (the
/// object is old and not freed, its field is unchanged, and the write barrier
/// recorded it).
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let derive_fwd_classified_pointwise
  (minor: minor_state) (major_pre: heap) (fp: U64.t) (roots: seq U64.t)
  (pf: obj_addr -> prop) (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  (obj: obj_addr) (j: nat)
  : Lemma
    (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       let major_final = prom.major_final in
       let fwd = prom.fwd_map in
       CE.promote_pre minor major_pre fp /\
       Seq.length farr == fwd_array_size /\
       represents_fwd farr fwd /\
       n <= Seq.length slots /\
       ref_table_complete_except major_pre pf fwd slots n /\
       not_freed major_final pf obj /\
       is_no_scan obj major_final = false /\
       j < U64.v (wosize_of_object obj major_final) /\
       U64.v obj + j * 8 + 8 <= heap_size /\
       (U64.v obj + j * 8) % 8 == 0 /\
       (let field_val = to_minor_offset
          (read_word major_final (U64.uint_to_t (U64.v obj + j * 8))) in
        is_minor_pointer field_val /\ fwd field_val <> 0UL)))
    (ensures
      (exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj) \/
      (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == U64.v obj + j * 8))
  = let prom = CheneySpec.cheney_promote minor major_pre fp roots in
    let fwd = prom.fwd_map in
    CE.cheney_promote_not_freed_origin minor major_pre fp roots pf obj;
    if IndDesc.strong_excluded_middle (not_freed major_pre pf obj) then begin
      // An old not-freed object: its header and field are those of major_pre.
      CheneyPres.cheney_promote_frame_old_header minor major_pre fp roots obj;
      Aux.header_eq_object_facts prom.major_final major_pre obj;
      CheneyPres.cheney_promote_frame_old_fields minor major_pre fp roots obj j
    end else begin
      // The image of a nursery object: it is in the forwarding array.
      let v = IndDesc.indefinite_description_ghost U64.t
        (fun v -> Seq.mem v (minor_objects minor) /\ fwd v == obj) in
      minor_objects_valid minor v;
      let pi = U64.v v / 8 in
      ML.lemma_div_le (U64.v v) (minor_heap_size - 8) 8;
      ML.lemma_div_exact (U64.v v) 8;
      assert (pi < fwd_array_size);
      assert (U64.uint_to_t (pi * 8) == v);
      assert (Seq.index farr pi == obj)
    end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let derive_fwd_ptrs_classified_walked
  (minor: minor_state) (major_pre: heap) (fp: U64.t) (roots: seq U64.t)
  (pf: obj_addr -> prop) (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       CE.promote_pre minor major_pre fp /\
       Seq.length farr == fwd_array_size /\
       represents_fwd farr prom.fwd_map /\
       n <= Seq.length slots /\
       ref_table_complete_except major_pre pf prom.fwd_map slots n))
    (ensures
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       TwoPass.fwd_ptrs_classified_walked prom.major_final
         (not_freed prom.major_final pf) prom.fwd_map farr slots n))
  = let prom = CheneySpec.cheney_promote minor major_pre fp roots in
    let major_final = prom.major_final in
    let fwd = prom.fwd_map in
    let aux (obj: obj_addr) (j: nat) : Lemma
      (Seq.mem obj (objects zero_addr major_final) /\
       not_freed major_final pf obj /\
       is_no_scan obj major_final = false /\
       j < U64.v (wosize_of_object obj major_final) /\
       U64.v obj + j * 8 + 8 <= heap_size /\
       (U64.v obj + j * 8) % 8 == 0 /\
       (let field_val = to_minor_offset (read_word major_final (U64.uint_to_t (U64.v obj + j * 8))) in
        is_minor_pointer field_val /\ fwd field_val <> 0UL) ==>
       ((exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj) \/
        (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == U64.v obj + j * 8)))
    = Classical.move_requires
        (derive_fwd_classified_pointwise minor major_pre fp roots pf farr slots n obj) j
    in
    Classical.forall_intro_2 aux
#pop-options

/// ---------------------------------------------------------------------------
/// The theorems
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let two_pass_implies_collect_except minor major_pre fp roots pf farr slots n =
  let prom = CheneySpec.cheney_promote minor major_pre fp roots in
  derive_promoted_entries_valid_from prom.major_final farr prom.fwd_map;
  derive_promoted_entries_disjoint prom.major_final farr prom.fwd_map;
  derive_promoted_entries_walked minor major_pre fp roots pf farr;
  derive_slots_rewrite_walked minor major_pre fp roots pf slots n;
  derive_fwd_ptrs_classified_walked minor major_pre fp roots pf farr slots n;
  TwoPass.promoted_plus_slots_eq_walk prom.major_final (not_freed prom.major_final pf)
    prom.fwd_map farr slots n
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let two_pass_implies_full_update minor major_pre fp roots farr slots n =
  let prom = CheneySpec.cheney_promote minor major_pre fp roots in
  ref_table_sound_except_no_pending major_pre slots n;
  ref_table_sound_except_implies_fwd major_pre no_pending prom.fwd_map slots n;
  assert (ref_table_complete_except major_pre no_pending prom.fwd_map slots n);
  no_pending_ok major_pre;
  two_pass_implies_collect_except minor major_pre fp roots no_pending farr slots n;
  CE.cheney_collect_spec_except_no_pending minor major_pre fp roots
#pop-options
