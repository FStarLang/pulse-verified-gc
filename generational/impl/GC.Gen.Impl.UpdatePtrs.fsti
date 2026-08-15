/// ---------------------------------------------------------------------------
/// GC.Gen.Impl.UpdatePtrs — Pulse implementation of pointer rewriting
/// ---------------------------------------------------------------------------
///
/// After promoting minor objects to the major heap, rewrites all
/// minor-heap pointers in major-heap fields to their new major-heap addresses.

module GC.Gen.Impl.UpdatePtrs

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Impl.Heap
module PromoteSpec = GC.Gen.Promote
module SpecObj = GC.Spec.Object
module SpecHeap = GC.Spec.Heap
module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// Forwarding array representation
/// ---------------------------------------------------------------------------

/// Number of entries in the forwarding array = minor_heap_size / 8
/// Spec-only: used in ghost assertions for array lengths. Not extracted.
noextract
let fwd_array_size : n:pos{n == minor_heap_size / 8} = minor_heap_size / 8

/// Connects a concrete array to the abstract forwarding_map
let represents_fwd (farr: Seq.seq U64.t) (fwd: PromoteSpec.forwarding_map) : prop =
  Seq.length farr == fwd_array_size /\
  (forall (i: nat). i < fwd_array_size ==>
    Seq.index farr i == fwd (U64.uint_to_t (i * 8)))

/// Construct a ghost forwarding map from a concrete array
let ghost_fwd_of (farr: Seq.seq U64.t{Seq.length farr == fwd_array_size})
  : PromoteSpec.forwarding_map =
  fun (a: U64.t) ->
    if U64.v a % 8 = 0 && U64.v a / 8 < fwd_array_size
    then Seq.index farr (U64.v a / 8)
    else 0UL

/// ghost_fwd_of establishes represents_fwd
val ghost_fwd_of_represents (farr: Seq.seq U64.t{Seq.length farr == fwd_array_size})
  : Lemma (represents_fwd farr (ghost_fwd_of farr))

/// ---------------------------------------------------------------------------
/// Rewrite roots
/// ---------------------------------------------------------------------------

/// Rewrite program roots: replace minor pointers with their forwarded addresses.
fn rewrite_roots_impl
  (roots: array U64.t)
  (fwd_arr: array U64.t)
  (n: SZ.t)
  (#fwd: erased PromoteSpec.forwarding_map)
  requires pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (SZ.v n == Seq.length 'rs /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd)
  ensures exists* rs2.
    pts_to roots rs2 **
    pts_to fwd_arr 'farr **
    pure (Seq.length rs2 == Seq.length 'rs /\
          rs2 == PromoteSpec.rewrite_roots 'rs fwd)

/// ---------------------------------------------------------------------------
/// Update pointers in one object's fields
/// ---------------------------------------------------------------------------

/// Update all pointer fields in a single major-heap object.
/// For each field [0, wosize), reads the value, checks if it's a minor-heap
/// pointer with a forwarding entry, and rewrites it if so.
fn update_one_object (major: heap_t) (fwd_arr: array U64.t)
                     (obj: U64.t) (wosize: U64.t)
                     (#fwd: erased PromoteSpec.forwarding_map)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pure (U64.v obj >= 8 /\ U64.v obj % 8 == 0 /\
                 U64.v obj + U64.v wosize * 8 <= heap_size /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pure (ms2 == PromoteSpec.update_object_pointers 'ms obj (U64.v wosize) fwd 0)

/// ---------------------------------------------------------------------------
/// Update ALL major-heap objects' pointer fields
/// ---------------------------------------------------------------------------

/// Walk the major heap linearly and for each object call update_one_object.
/// Result equals PromoteSpec.update_major_pointers applied to the initial heap.
fn update_all_objects (major: heap_t) (fwd_arr: array U64.t)
                      (#fwd: erased PromoteSpec.forwarding_map)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pure (GC.Spec.Fields.well_formed_heap_part1 'ms /\
                 PromoteSpec.heap_objects_dense 'ms /\
                 heap_size > 8 /\
                 Seq.length (GC.Spec.Fields.objects zero_addr 'ms) > 0 /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pure (GC.Spec.Fields.well_formed_heap_part1 ms2 /\
          PromoteSpec.heap_objects_dense ms2 /\
          Seq.length (GC.Spec.Fields.objects zero_addr ms2) > 0 /\
          ms2 == PromoteSpec.update_major_pointers 'ms fwd)

/// ---------------------------------------------------------------------------
/// Rewrite heap slots (ref_table entries)
/// ---------------------------------------------------------------------------

/// Predicate: all slot addresses are valid heap field addresses
let valid_slot_addrs (slots: Seq.seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (i: nat). i < n ==>
    (let addr = U64.v (Seq.index slots i) in
     addr < heap_size /\ addr % 8 == 0))

/// Slots are pairwise distinct (no duplicates in the ref_table).
/// Required so that rewrite_slots_iter_slot_effect can identify
/// which slot write is final at a given address.
let slots_pairwise_distinct (slots: Seq.seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (i j: nat). i < n /\ j < n /\ i <> j ==>
    U64.v (Seq.index slots i) <> U64.v (Seq.index slots j))

/// Spec: iterate slots[idx..n), rewriting each slot's value via the forwarding map.
/// Models what rewrite_heap_slots computes.
let rec rewrite_slots_iter (major: heap) (fwd: PromoteSpec.forwarding_map)
                           (slots: Seq.seq U64.t) (n: nat) (idx: nat)
  : GTot heap (decreases (n - idx)) =
  if idx >= n then major
  else if idx >= Seq.length slots then major
  else
    let slot_addr = Seq.index slots idx in
    if U64.v slot_addr >= heap_size || U64.v slot_addr % 8 <> 0 then
      rewrite_slots_iter major fwd slots n (idx + 1)
    else
      let field_val = GC.Gen.Base.to_minor_offset (SpecHeap.read_word major slot_addr) in
      if PromoteSpec.is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then
          let major' = SpecHeap.write_word major slot_addr new_val in
          rewrite_slots_iter major' fwd slots n (idx + 1)
        else
          rewrite_slots_iter major fwd slots n (idx + 1)
      else
        rewrite_slots_iter major fwd slots n (idx + 1)

/// Rewrite specific heap slots: for each slot[i], read the value from the
/// major heap, and if it's a forwarded minor pointer, replace it.
/// Used to apply forwarding to ref_table entries without scanning the
/// entire major heap.
fn rewrite_heap_slots
  (major: heap_t)
  (fwd_arr: array U64.t)
  (slots: array U64.t)
  (n: SZ.t)
  (#fwd: erased PromoteSpec.forwarding_map)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pts_to slots 'sl **
           pure (SZ.v n <= Seq.length 'sl /\
                 Seq.length 'farr == fwd_array_size /\
                 valid_slot_addrs 'sl (SZ.v n) /\
                 represents_fwd 'farr fwd)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pts_to slots 'sl **
    pure (ms2 == rewrite_slots_iter 'ms fwd 'sl (SZ.v n) 0)

/// ---------------------------------------------------------------------------
/// Update promoted objects (fwd_arr iteration)
/// ---------------------------------------------------------------------------

/// Spec: iterate fwd_arr[idx..fwd_array_size) and for each non-zero entry,
/// if the promoted object has wosize > 0 and tag < no_scan_tag, apply
/// update_object_pointers.
let rec update_promoted_iter (major: heap) (farr: Seq.seq U64.t)
                             (fwd: PromoteSpec.forwarding_map) (idx: nat)
  : GTot heap (decreases (fwd_array_size - idx)) =
  if idx >= fwd_array_size then major
  else if Seq.length farr <> fwd_array_size then major
  else
    let major_addr = Seq.index farr idx in
    if major_addr = 0UL then
      update_promoted_iter major farr fwd (idx + 1)
    else
      let hdr_addr = U64.v major_addr - 8 in
      if hdr_addr + 8 > heap_size || hdr_addr % 8 <> 0 then
        update_promoted_iter major farr fwd (idx + 1)
      else
        let hdr = SpecHeap.read_word major (U64.uint_to_t hdr_addr) in
        let wosize = U64.v (SpecObj.getWosize hdr) in
        let tag = SpecObj.getTag hdr in
        if wosize > 0 && U64.lt tag SpecObj.no_scan_tag && not (tag = SpecObj.infix_tag) then
          if U64.v major_addr + wosize * 8 <= heap_size then
            let major' = PromoteSpec.update_object_pointers major major_addr wosize fwd 0 in
            update_promoted_iter major' farr fwd (idx + 1)
          else
            update_promoted_iter major farr fwd (idx + 1)
        else
          update_promoted_iter major farr fwd (idx + 1)

/// Unfold lemma for update_promoted_iter at a zero entry
val update_promoted_iter_zero (major: heap) (farr: Seq.seq U64.t)
                              (fwd: PromoteSpec.forwarding_map) (idx: nat)
  : Lemma (requires idx < fwd_array_size /\
                    Seq.length farr == fwd_array_size /\
                    Seq.index farr idx == 0UL)
          (ensures update_promoted_iter major farr fwd idx ==
                   update_promoted_iter major farr fwd (idx + 1))

/// Unfold lemma for update_promoted_iter at a non-zero scannable entry
val update_promoted_iter_scan (major: heap) (farr: Seq.seq U64.t)
                              (fwd: PromoteSpec.forwarding_map) (idx: nat)
  : Lemma (requires idx < fwd_array_size /\
                    Seq.length farr == fwd_array_size /\
                    (let major_addr = Seq.index farr idx in
                     major_addr <> 0UL /\
                     U64.v major_addr >= 8 /\ U64.v major_addr % 8 == 0 /\
                     (let hdr_addr = U64.v major_addr - 8 in
                      hdr_addr + 8 <= heap_size /\ hdr_addr % 8 == 0 /\
                      (let hdr = SpecHeap.read_word major (U64.uint_to_t hdr_addr) in
                       let wosize = U64.v (SpecObj.getWosize hdr) in
                       let tag = SpecObj.getTag hdr in
                       wosize > 0 /\ U64.lt tag SpecObj.no_scan_tag /\
                       tag <> SpecObj.infix_tag /\
                       U64.v major_addr + wosize * 8 <= heap_size))))
          (ensures (let major_addr = Seq.index farr idx in
                    let hdr_addr = U64.v major_addr - 8 in
                    let hdr = SpecHeap.read_word major (U64.uint_to_t hdr_addr) in
                    let wosize = U64.v (SpecObj.getWosize hdr) in
                    let major' = PromoteSpec.update_object_pointers major major_addr wosize fwd 0 in
                    update_promoted_iter major farr fwd idx ==
                    update_promoted_iter major' farr fwd (idx + 1)))

/// Unfold lemma for update_promoted_iter at a non-scannable entry
/// (no-scan, infix, wosize=0, or out-of-bounds)
val update_promoted_iter_skip (major: heap) (farr: Seq.seq U64.t)
                              (fwd: PromoteSpec.forwarding_map) (idx: nat)
  : Lemma (requires idx < fwd_array_size /\
                    Seq.length farr == fwd_array_size /\
                    (let major_addr = Seq.index farr idx in
                     major_addr <> 0UL /\
                     (let hdr_addr = U64.v major_addr - 8 in
                      hdr_addr + 8 > heap_size \/ hdr_addr % 8 <> 0 \/
                      (hdr_addr + 8 <= heap_size /\ hdr_addr % 8 == 0 /\
                       (let hdr = SpecHeap.read_word major (U64.uint_to_t hdr_addr) in
                        let wosize = U64.v (SpecObj.getWosize hdr) in
                        let tag = SpecObj.getTag hdr in
                        ~(wosize > 0 /\ U64.lt tag SpecObj.no_scan_tag /\ tag <> SpecObj.infix_tag) \/
                        U64.v major_addr + wosize * 8 > heap_size)))))
          (ensures update_promoted_iter major farr fwd idx ==
                   update_promoted_iter major farr fwd (idx + 1))

/// Base case: update_promoted_iter at idx >= fwd_array_size is identity
val update_promoted_iter_done (major: heap) (farr: Seq.seq U64.t)
                              (fwd: PromoteSpec.forwarding_map) (idx: nat)
  : Lemma (requires idx >= fwd_array_size)
          (ensures update_promoted_iter major farr fwd idx == major)

/// Precondition for valid fwd_arr entries: every non-zero entry points to
/// a valid major-heap object (address >= 8, aligned, header accessible,
/// body fits in heap).
let valid_fwd_entries (farr: Seq.seq U64.t) : prop =
  Seq.length farr == fwd_array_size /\
  (forall (i: nat). i < fwd_array_size ==>
    (let addr = Seq.index farr i in
     addr == 0UL \/
     (U64.v addr >= 8 /\ U64.v addr % 8 == 0 /\
      U64.v addr <= heap_size)))

/// Strong validity: farr entries from idx onward are valid objects in major.
/// Needed for the two-pass equivalence proof (preservation at non-fwd addresses).
let promoted_entries_valid_from (major: heap) (farr: Seq.seq U64.t) (idx: nat) : prop =
  Seq.length farr == fwd_array_size /\
  GC.Spec.Fields.well_formed_heap_part1 major /\
  (forall (i: nat). i >= idx /\ i < fwd_array_size ==>
    (let obj = Seq.index farr i in
     obj = 0UL \/
     (U64.v obj >= U64.v mword /\ U64.v obj % 8 == 0 /\ U64.v obj < heap_size /\
      SpecObj.is_infix obj major) \/
     (U64.v obj >= U64.v mword /\ U64.v obj % 8 == 0 /\ U64.v obj < heap_size /\
      Seq.mem obj (GC.Spec.Fields.objects zero_addr major) /\
      (let wz = U64.v (SpecObj.wosize_of_object obj major) in
       U64.v obj + wz * 8 <= heap_size /\
       (forall (k:nat). k < wz ==>
         (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0))))))

/// Promoted body disjointness: non-zero, non-infix entries in farr have
/// non-overlapping bodies. Infix entries are exempt (they are interior
/// pointers with fake wosize and are skipped by update_promoted_iter).
let promoted_entries_disjoint (major: heap) (farr: Seq.seq U64.t) : prop =
  Seq.length farr == fwd_array_size /\
  (forall (i1 i2: nat). i1 < fwd_array_size /\ i2 < fwd_array_size /\ i1 <> i2 ==>
    (let o1 = Seq.index farr i1 in
     let o2 = Seq.index farr i2 in
     o1 <> 0UL /\ o2 <> 0UL /\
     U64.v o1 >= 8 /\ U64.v o2 >= 8 /\
     U64.v o1 % 8 == 0 /\ U64.v o2 % 8 == 0 /\
     U64.v o1 < heap_size /\ U64.v o2 < heap_size /\
     SpecObj.is_infix o1 major = false /\
      SpecObj.is_infix o2 major = false ==>
      (U64.v o1 + U64.v (SpecObj.wosize_of_object o1 major) * 8 <= U64.v o2 \/
       U64.v o2 + U64.v (SpecObj.wosize_of_object o2 major) * 8 <= U64.v o1)))

/// Non-zero non-infix forwarding-array entries point to non-blue objects.
/// This is needed because update_promoted_iter scans farr entries by tag,
/// while update_major_pointers skips blue objects.  For farr values produced by
/// Cheney promotion, this follows from fwd_targets_not_blue.
let promoted_entries_not_blue (major: heap) (farr: Seq.seq U64.t) : prop =
  Seq.length farr == fwd_array_size /\
  (forall (i: nat). i < fwd_array_size ==>
    (let obj = Seq.index farr i in
     obj <> 0UL /\
     U64.v obj >= U64.v mword /\
     U64.v obj % U64.v mword == 0 /\
     U64.v obj < heap_size /\
     SpecObj.is_infix obj major = false ==>
     SpecObj.is_blue obj major = false))

/// Update only the promoted objects' fields by iterating fwd_arr.
/// For each non-zero fwd_arr[i], reads the header at (fwd_arr[i] - 8),
/// and if wosize > 0 and tag < no_scan_tag, rewrites pointer fields.
fn update_promoted_objects (major: heap_t) (fwd_arr: array U64.t)
                           (#fwd: erased PromoteSpec.forwarding_map)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pure (Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd /\
                 valid_fwd_entries 'farr)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pure (ms2 == update_promoted_iter 'ms 'farr fwd 0)

/// ---------------------------------------------------------------------------
/// Ref-table completeness: sufficient condition for full correctness
/// ---------------------------------------------------------------------------

/// Client-facing remembered-set completeness.  Every scannable non-blue field
/// in the ORIGINAL major heap that currently contains a minor pointer has its
/// address listed in slots[0..n).
///
/// This is intentionally independent of the forwarding map produced by Cheney
/// promotion: the write barrier records old-major fields when they are assigned
/// young pointers, without knowing which young objects will be live later.
let ref_table_covers_minor_ptrs (major_pre: heap)
                               (slots: Seq.seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (obj: GC.Spec.Base.obj_addr) (j: nat).
    Seq.mem obj (GC.Spec.Fields.objects zero_addr major_pre) /\
    GC.Spec.Object.is_blue obj major_pre = false /\
    GC.Spec.Object.is_no_scan obj major_pre = false /\
    j < U64.v (SpecObj.wosize_of_object obj major_pre) /\
    U64.v obj + j * 8 + 8 <= heap_size /\
    (let field_val = GC.Gen.Base.to_minor_offset
       (SpecHeap.read_word major_pre (U64.uint_to_t (U64.v obj + j * 8))) in
     PromoteSpec.is_minor_pointer field_val) ==>
    (exists (i: nat). i < n /\ U64.v (Seq.index slots i) == U64.v obj + j * 8))

/// Internal proof-facing completeness. The ref_table is "complete" w.r.t. the
/// pre-promotion major heap and a particular forwarding map: every
/// field (of a scannable, non-blue object) in the ORIGINAL major heap that
/// holds a forwarded minor pointer has its address listed in slots[0..n).
///
/// This is derived inside the implementation from ref_table_covers_minor_ptrs.
/// After promotion, these same fields still hold minor pointers (promotion adds
/// new objects but doesn't modify pre-existing object bodies). Combined with
/// update_promoted_iter (which handles newly-promoted objects' fields), this
/// ensures ALL forwarded minor pointers in the post-promotion heap get rewritten.
///
/// Quantifies over field positions (obj, j) rather than all aligned addresses,
/// because header words can accidentally look like forwarded minor pointers
/// (e.g., makeHeader 1 White 0 = 1024, which passes is_minor_pointer).
let ref_table_complete (major_pre: heap) (fwd: PromoteSpec.forwarding_map)
                       (slots: Seq.seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (obj: GC.Spec.Base.obj_addr) (j: nat).
    Seq.mem obj (GC.Spec.Fields.objects zero_addr major_pre) /\
    GC.Spec.Object.is_blue obj major_pre = false /\
    GC.Spec.Object.is_no_scan obj major_pre = false /\
    j < U64.v (SpecObj.wosize_of_object obj major_pre) /\
    U64.v obj + j * 8 + 8 <= heap_size /\
    (let field_val = GC.Gen.Base.to_minor_offset
       (SpecHeap.read_word major_pre (U64.uint_to_t (U64.v obj + j * 8))) in
     PromoteSpec.is_minor_pointer field_val /\ fwd field_val <> 0UL) ==>
    (exists (i: nat). i < n /\ U64.v (Seq.index slots i) == U64.v obj + j * 8))

val ref_table_covers_minor_ptrs_implies_complete
  (major_pre: heap) (fwd: PromoteSpec.forwarding_map)
  (slots: Seq.seq U64.t) (n: nat)
  : Lemma (requires ref_table_covers_minor_ptrs major_pre slots n)
          (ensures ref_table_complete major_pre fwd slots n)

/// Slot soundness: every slot address is a field of a scannable non-blue object
/// in the original heap. This ensures rewrite_slots_iter only touches addresses
/// that update_major_pointers would also touch.
///
/// The write barrier only records addresses of pointer fields in non-blue,
/// non-no_scan objects, so this is a natural caller obligation.
let ref_table_sound (major_pre: heap) (slots: Seq.seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (i: nat). i < n ==>
    (let addr = U64.v (Seq.index slots i) in
     addr < heap_size /\ addr % 8 == 0 /\
     (exists (obj: GC.Spec.Base.obj_addr) (j: nat).
       Seq.mem obj (GC.Spec.Fields.objects zero_addr major_pre) /\
       GC.Spec.Object.is_blue obj major_pre = false /\
       GC.Spec.Object.is_no_scan obj major_pre = false /\
       j < U64.v (SpecObj.wosize_of_object obj major_pre) /\
       addr == U64.v obj + j * 8)))

val ref_table_sound_implies_valid_slot_addrs
  (major_pre: heap) (slots: Seq.seq U64.t) (n: nat)
  : Lemma (requires ref_table_sound major_pre slots n)
          (ensures valid_slot_addrs slots n)

/// Slot soundness in the post-promotion heap used by the two-pass equivalence
/// proof.  The implementation derives this from ref_table_sound on major_pre
/// plus Cheney frame/header preservation for pre-existing non-blue objects.
let slots_scannable_in_major (major: heap) (slots: Seq.seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (i: nat). i < n ==>
    (let addr = U64.v (Seq.index slots i) in
     exists (obj: GC.Spec.Base.obj_addr) (j: nat).
       Seq.mem obj (GC.Spec.Fields.objects zero_addr major) /\
       GC.Spec.Object.is_blue obj major = false /\
       GC.Spec.Object.is_no_scan obj major = false /\
       j < U64.v (SpecObj.wosize_of_object obj major) /\
       addr == U64.v obj + j * 8 /\
       U64.v obj + j * 8 + 8 <= heap_size /\
       (U64.v obj + j * 8) % 8 == 0))

/// Forwarding targets don't trigger the minor-pointer condition.
/// After pass 1 rewrites a field to fwd(offset), the resulting value
/// should NOT cause pass 2 to rewrite it again (no double-application).
///
/// Holds when major/minor address spaces are well-separated: forwarding
/// targets are major addresses that don't convert to valid minor offsets.
[@@"opaque_to_smt"]
let fwd_targets_stable (fwd: PromoteSpec.forwarding_map) : prop =
  forall (x: U64.t). fwd x <> 0UL ==>
    (let target = fwd x in
     let target_as_minor = GC.Gen.Base.to_minor_offset target in
     ~(PromoteSpec.is_minor_pointer target_as_minor /\ fwd target_as_minor <> 0UL))

/// Classification of forwarded minor pointers at scannable object fields.
/// For every field of a scannable (non-blue, non-no_scan) object in major_final
/// that contains a forwarded minor pointer, the object is either:
///   (1) a promoted object (recorded in farr), OR
///   (2) at a ref_table slot address.
///
/// Quantifies over field positions (obj, j) rather than all aligned addresses.
/// This avoids the unprovable header-collision case where object headers
/// (e.g., makeHeader 1 White 0 = 1024) accidentally satisfy is_minor_pointer.
///
/// Provable from: well_formed_heap + promotion frame + nonblue_origin +
/// ref_table_complete. Derived in GC.Gen.Impl.derive_fwd_ptrs_classified.
let fwd_ptrs_classified (major: heap) (fwd: PromoteSpec.forwarding_map)
                        (farr: Seq.seq U64.t) (slots: Seq.seq U64.t) (n: nat) : prop =
  Seq.length farr == fwd_array_size /\
  n <= Seq.length slots /\
  (forall (obj: GC.Spec.Base.obj_addr) (j: nat).
    {:pattern (GC.Gen.Base.to_minor_offset
      (SpecHeap.read_word major (U64.uint_to_t (U64.v obj + j * 8))))}
    Seq.mem obj (GC.Spec.Fields.objects zero_addr major) /\
    GC.Spec.Object.is_blue obj major = false /\
    GC.Spec.Object.is_no_scan obj major = false /\
    j < U64.v (SpecObj.wosize_of_object obj major) /\
    U64.v obj + j * 8 + 8 <= heap_size /\
    (U64.v obj + j * 8) % 8 == 0 /\
    (let field_val = GC.Gen.Base.to_minor_offset
       (SpecHeap.read_word major (U64.uint_to_t (U64.v obj + j * 8))) in
     PromoteSpec.is_minor_pointer field_val /\ fwd field_val <> 0UL) ==>
    ((exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj) \/
     (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == U64.v obj + j * 8)))

/// The key equivalence theorem (promoted + slots = full update) is proved in
/// GC.Gen.TwoPassEquiv.promoted_plus_slots_eq_full_update.
/// Import GC.Gen.TwoPassEquiv to use it.
