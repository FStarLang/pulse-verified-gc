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
        if wosize > 0 && U64.lt tag SpecObj.no_scan_tag then
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
                       U64.v major_addr + wosize * 8 <= heap_size))))
          (ensures (let major_addr = Seq.index farr idx in
                    let hdr_addr = U64.v major_addr - 8 in
                    let hdr = SpecHeap.read_word major (U64.uint_to_t hdr_addr) in
                    let wosize = U64.v (SpecObj.getWosize hdr) in
                    let major' = PromoteSpec.update_object_pointers major major_addr wosize fwd 0 in
                    update_promoted_iter major farr fwd idx ==
                    update_promoted_iter major' farr fwd (idx + 1)))

/// Unfold lemma for update_promoted_iter at a non-scannable entry
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
                        ~(wosize > 0 /\ U64.lt tag SpecObj.no_scan_tag) \/
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

/// The ref_table is "complete" w.r.t. the pre-promotion major heap: every
/// field (of a scannable, non-blue object) in the ORIGINAL major heap that
/// holds a forwarded minor pointer has its address listed in slots[0..n).
///
/// This matches what the write barrier records: addresses of existing major-heap
/// fields that were assigned minor pointers. After promotion, these same fields
/// still hold minor pointers (promotion adds new objects but doesn't modify
/// pre-existing object bodies). Combined with update_promoted_iter (which
/// handles newly-promoted objects' fields), this ensures ALL minor pointers
/// in the post-promotion heap get rewritten.
let ref_table_complete (major_pre: heap) (fwd: PromoteSpec.forwarding_map)
                       (slots: Seq.seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (addr: nat).
    addr < heap_size /\ addr % 8 == 0 /\
    (let field_val = GC.Gen.Base.to_minor_offset (SpecHeap.read_word major_pre (U64.uint_to_t addr)) in
     PromoteSpec.is_minor_pointer field_val /\ fwd field_val <> 0UL) ==>
    (exists (i: nat). i < n /\ U64.v (Seq.index slots i) == addr))

/// Slot soundness: every slot address is a field of a scannable non-blue object
/// in the original heap. This ensures rewrite_slots_iter only touches addresses
/// that update_major_pointers would also touch.
let ref_table_sound (major_pre: heap) (slots: Seq.seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (i: nat). i < n ==>
    (let addr = U64.v (Seq.index slots i) in
     addr < heap_size /\ addr % 8 == 0))

/// Key equivalence: update_promoted_iter + rewrite_slots_iter = update_major_pointers,
/// under the ref_table_complete condition and suitable structural invariants.
///
/// This connects the efficient two-pass approach (promoted objects via fwd_arr +
/// ref_table slots) to the full-correctness spec (walk all objects).
///
/// Takes the full promotion parameters so the proof can internally derive
/// preservation of pre-existing fields via promote_all_read_other.
///
/// Proof sketch:
/// 1. Promoted objects' fields are at addresses written by update_promoted_iter.
///    After Pass 1, those fields no longer hold minor pointers (they hold fwd targets).
/// 2. Pre-existing fields with minor pointers are in the ref_table (by completeness).
///    After Pass 1, their values are unchanged (Pass 1 only touches promoted fields).
///    Pass 2 rewrites them correctly.
/// 3. Both passes write the same values as update_major_pointers would (fwd(minor_offset)).
/// 4. Writes at distinct addresses commute, so iteration order doesn't matter.
val promoted_plus_slots_eq_full_update
  (minor: GC.Gen.MinorHeap.minor_state) (major_pre: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (farr: Seq.seq U64.t) (slots: Seq.seq U64.t) (n: nat)
  : Lemma
    (requires
      (let prom = GC.Gen.Cheney.cheney_promote minor major_pre fp roots in
       Seq.length farr == fwd_array_size /\
       valid_fwd_entries farr /\
       represents_fwd farr prom.fwd_map /\
       valid_slot_addrs slots n /\
       ref_table_sound major_pre slots n /\
       ref_table_complete major_pre prom.fwd_map slots n /\
       GC.Spec.Fields.well_formed_heap_part1 prom.major_final /\
       PromoteSpec.heap_objects_dense prom.major_final /\
       Seq.length (GC.Spec.Fields.objects zero_addr prom.major_final) > 0 /\
       GC.Spec.Fields.well_formed_heap major_pre /\
       GC.Spec.Allocator.Lemmas.fl_valid major_pre fp (heap_size / U64.v mword) /\
       GC.Spec.Allocator.Lemmas.fl_chain_terminates major_pre fp (heap_size / U64.v mword)))
    (ensures
      (let prom = GC.Gen.Cheney.cheney_promote minor major_pre fp roots in
       rewrite_slots_iter (update_promoted_iter prom.major_final farr prom.fwd_map 0)
                          prom.fwd_map slots n 0
         == PromoteSpec.update_major_pointers prom.major_final prom.fwd_map))
