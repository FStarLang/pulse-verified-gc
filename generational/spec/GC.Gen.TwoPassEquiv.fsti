/// ---------------------------------------------------------------------------
/// GC.Gen.TwoPassEquiv — Equivalence of two-pass pointer rewriting and full update
/// ---------------------------------------------------------------------------
///
/// Proves: update_promoted_iter + rewrite_slots_iter == update_major_pointers
/// under ref_table_complete and standard well-formedness conditions.

module GC.Gen.TwoPassEquiv

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

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

let heap_fuel : nat = heap_size / U64.v mword

/// ---------------------------------------------------------------------------
/// Heap extensionality: word-level agreement implies byte-level equality
/// ---------------------------------------------------------------------------

val heap_read_word_extensional (h1 h2: heap)
  : Lemma
    (requires (forall (a: nat).
       a < heap_size /\ a % 8 == 0 ==>
       read_word h1 (U64.uint_to_t a) == read_word h2 (U64.uint_to_t a)))
    (ensures h1 == h2)

/// ---------------------------------------------------------------------------
/// update_promoted_iter frame: addresses outside promoted objects are unchanged
/// ---------------------------------------------------------------------------

/// Frame precondition: addr is outside all promoted object bodies from idx onward
let promoted_iter_frame_pre (major: heap) (farr: seq U64.t) (idx: nat) (addr: hp_addr) : prop =
  Seq.length farr == fwd_array_size /\
  well_formed_heap_part1 major /\
  (forall (i: nat). i >= idx /\ i < fwd_array_size ==>
    (let obj = Seq.index farr i in
     obj = 0UL \/
     (U64.v obj >= U64.v mword /\ U64.v obj % 8 == 0 /\ U64.v obj < heap_size /\
      is_infix obj major) \/
     (U64.v obj >= U64.v mword /\ U64.v obj % 8 == 0 /\ U64.v obj < heap_size /\
      Seq.mem obj (objects zero_addr major) /\
      (let wz = U64.v (wosize_of_object obj major) in
       U64.v obj + wz * 8 <= heap_size /\
       (forall (k:nat). k < wz ==>
         (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)) /\
       (U64.v addr < U64.v obj \/ U64.v addr >= U64.v obj + wz * 8)))))

val update_promoted_iter_frame
  (major: heap) (farr: seq U64.t) (fwd: forwarding_map) (idx: nat)
  (addr: hp_addr)
  : Lemma
    (requires promoted_iter_frame_pre major farr idx addr)
    (ensures
      read_word (update_promoted_iter major farr fwd idx) addr ==
      read_word major addr)
    (decreases (fwd_array_size - idx))

/// ---------------------------------------------------------------------------
/// update_promoted_iter effect on promoted fields
/// ---------------------------------------------------------------------------

/// For a field inside a promoted object, update_promoted_iter applies
/// the same transformation as update_object_pointers.
val update_promoted_iter_promoted_field
  (major: heap) (farr: seq U64.t) (fwd: forwarding_map)
  (pi: nat) (j: nat)
  : Lemma
    (requires
      Seq.length farr == fwd_array_size /\
      well_formed_heap_part1 major /\
      pi < fwd_array_size /\
      (let obj = Seq.index farr pi in
       obj <> 0UL /\
       U64.v obj >= U64.v mword /\ U64.v obj % 8 == 0 /\ U64.v obj < heap_size /\
       Seq.mem obj (objects zero_addr major) /\
       (let wz = U64.v (wosize_of_object obj major) in
        let tag = getTag (read_word major (hd_address obj)) in
        wz > 0 /\ U64.lt tag no_scan_tag /\ tag <> infix_tag /\
        U64.v obj + wz * 8 <= heap_size /\
        j < wz /\
        (forall (k:nat). k < wz ==>
          (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))) /\
      // All promoted objects are valid (or infix) with disjoint bodies
      (forall (i: nat). i < fwd_array_size ==>
        (let o = Seq.index farr i in
         o = 0UL \/
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          is_infix o major) \/
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          Seq.mem o (objects zero_addr major) /\
          U64.v o + U64.v (wosize_of_object o major) * 8 <= heap_size))) /\
      (forall (i1 i2: nat). i1 < fwd_array_size /\ i2 < fwd_array_size /\ i1 <> i2 ==>
        (let o1 = Seq.index farr i1 in
         let o2 = Seq.index farr i2 in
         o1 <> 0UL /\ o2 <> 0UL /\
         is_infix o1 major = false /\ is_infix o2 major = false ==>
         (U64.v o1 + U64.v (wosize_of_object o1 major) * 8 <= U64.v o2 \/
          U64.v o2 + U64.v (wosize_of_object o2 major) * 8 <= U64.v o1))))
    (ensures
      (let obj = Seq.index farr pi in
       let wz = U64.v (wosize_of_object obj major) in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_raw = read_word major field_addr in
       let old_val = to_minor_offset old_raw in
       let result = read_word (update_promoted_iter major farr fwd 0) field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> result == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> result == old_raw)))

/// ---------------------------------------------------------------------------
/// rewrite_slots_iter frame: addresses not in slots are unchanged
/// ---------------------------------------------------------------------------

val rewrite_slots_iter_frame
  (major: heap) (fwd: forwarding_map) (slots: seq U64.t) (n: nat) (idx: nat)
  (addr: hp_addr)
  : Lemma
    (requires
      idx <= n /\ n <= Seq.length slots /\
      (forall (i: nat). i >= idx /\ i < n ==>
        (let sa = U64.v (Seq.index slots i) in
         sa < heap_size /\ sa % 8 == 0 /\
         (U64.v addr + 8 <= sa \/ sa + 8 <= U64.v addr))))
    (ensures
      read_word (rewrite_slots_iter major fwd slots n idx) addr ==
      read_word major addr)
    (decreases (n - idx))

/// ---------------------------------------------------------------------------
/// rewrite_slots_iter effect on a slot address
/// ---------------------------------------------------------------------------

val rewrite_slots_iter_slot_effect
  (major: heap) (fwd: forwarding_map) (slots: seq U64.t) (n: nat) (si: nat)
  : Lemma
    (requires
      si < n /\ n <= Seq.length slots /\
      (forall (i: nat). i < n ==>
        (let sa = U64.v (Seq.index slots i) in
         sa < heap_size /\ sa % 8 == 0)) /\
      (forall (i: nat). i < n /\ i <> si ==>
        U64.v (Seq.index slots i) <> U64.v (Seq.index slots si)))
    (ensures
      (let slot_addr = Seq.index slots si in
       let old_raw = read_word major slot_addr in
       let old_val = to_minor_offset old_raw in
       let result = read_word (rewrite_slots_iter major fwd slots n 0) slot_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> result == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> result == old_raw)))

/// ---------------------------------------------------------------------------
/// Main equivalence theorem
/// ---------------------------------------------------------------------------

val promoted_plus_slots_eq_full_update
  (minor: minor_state) (major_pre: heap) (fp: U64.t) (roots: seq U64.t)
  (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       Seq.length farr == fwd_array_size /\
       promoted_entries_valid_from prom.major_final farr 0 /\
       promoted_entries_disjoint prom.major_final farr /\
       promoted_entries_not_blue prom.major_final farr /\
       well_formed_heap_part4 prom.major_final /\
       valid_slot_addrs slots n /\
       slots_pairwise_distinct slots n /\
       ref_table_sound major_pre slots n /\
       slots_scannable_in_major prom.major_final slots n /\
       ref_table_complete major_pre prom.fwd_map slots n /\
       fwd_targets_stable prom.fwd_map /\
       fwd_ptrs_classified prom.major_final prom.fwd_map farr slots n /\
       well_formed_heap_part1 prom.major_final /\
       heap_objects_dense prom.major_final /\
       Seq.length (objects zero_addr prom.major_final) > 0 /\
       well_formed_heap major_pre /\
       AllocLemmas.fl_valid major_pre fp heap_fuel /\
       AllocLemmas.fl_chain_terminates major_pre fp heap_fuel))
    (ensures
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       rewrite_slots_iter
         (update_promoted_iter prom.major_final farr prom.fwd_map 0)
         prom.fwd_map slots n 0
         == update_major_pointers prom.major_final prom.fwd_map))
