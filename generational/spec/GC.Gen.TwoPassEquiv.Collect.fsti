/// ---------------------------------------------------------------------------
/// GC.Gen.TwoPassEquiv.Collect -- the two passes at a Cheney result
/// ---------------------------------------------------------------------------
///
/// The implementation rewrites the promoted objects' fields
/// (`update_promoted_iter`) and then the remembered slots
/// (`rewrite_slots_iter`).  This module proves that this is the pointer update
/// of `cheney_collect_spec_except` for a set `pf` of objects pending free in
/// the pre-collection heap, given the write barrier's guarantees stated over
/// the not-freed objects (`two_pass_implies_collect_except`).
/// `two_pass_implies_full_update` is the instance `pf = no_pending`.

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

/// ---------------------------------------------------------------------------
/// The write barrier's guarantees, except the objects pending free
/// ---------------------------------------------------------------------------

/// `ref_table_covers_minor_ptrs` except the pending objects: every nursery
/// pointer held by a field of a not-freed scannable object is at a recorded
/// slot.  At `no_pending` it is `ref_table_covers_minor_ptrs`.
let ref_table_covers_except (major_pre: heap) (pf: obj_addr -> prop)
                            (slots: seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (obj: obj_addr) (j: nat).
    not_freed major_pre pf obj /\
    is_no_scan obj major_pre = false /\
    j < U64.v (wosize_of_object obj major_pre) /\
    U64.v obj + j * 8 + 8 <= heap_size /\
    is_minor_pointer (to_minor_offset (read_word major_pre (U64.uint_to_t (U64.v obj + j * 8)))) ==>
    (exists (i: nat). i < n /\ U64.v (Seq.index slots i) == U64.v obj + j * 8))

/// The forwarding-map form used by the proof (`ref_table_complete` except the
/// pending objects).
let ref_table_complete_except (major_pre: heap) (pf: obj_addr -> prop)
                              (fwd: forwarding_map) (slots: seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (obj: obj_addr) (j: nat).
    not_freed major_pre pf obj /\
    is_no_scan obj major_pre = false /\
    j < U64.v (wosize_of_object obj major_pre) /\
    U64.v obj + j * 8 + 8 <= heap_size /\
    (let field_val = to_minor_offset (read_word major_pre (U64.uint_to_t (U64.v obj + j * 8))) in
     is_minor_pointer field_val /\ fwd field_val <> 0UL) ==>
    (exists (i: nat). i < n /\ U64.v (Seq.index slots i) == U64.v obj + j * 8))

val ref_table_covers_except_implies_complete
  (major_pre: heap) (pf: obj_addr -> prop) (fwd: forwarding_map) (slots: seq U64.t) (n: nat)
  : Lemma (requires ref_table_covers_except major_pre pf slots n)
          (ensures ref_table_complete_except major_pre pf fwd slots n)

val ref_table_covers_except_no_pending (major_pre: heap) (slots: seq U64.t) (n: nat)
  : Lemma (requires ref_table_covers_minor_ptrs major_pre slots n)
          (ensures ref_table_covers_except major_pre no_pending slots n)

/// `ref_table_sound` except the pending objects, with a forwarding map: every
/// slot is a field of a non-free scannable object, and a slot in a pending
/// object holds no forwarded nursery pointer, so rewriting it is a no-op.
let ref_table_sound_fwd_except (major_pre: heap) (pf: obj_addr -> prop)
                               (fwd: forwarding_map) (slots: seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (i: nat). i < n ==>
    (let addr = U64.v (Seq.index slots i) in
     addr < heap_size /\ addr % 8 == 0 /\
     (exists (obj: obj_addr) (j: nat).
       Seq.mem obj (objects zero_addr major_pre) /\
       is_blue obj major_pre = false /\
       is_no_scan obj major_pre = false /\
       j < U64.v (wosize_of_object obj major_pre) /\
       addr == U64.v obj + j * 8 /\
       (~(pf obj) \/ ~(TwoPass.holds_forwarded major_pre fwd (U64.uint_to_t addr))))))

/// The caller's form of `ref_table_sound_fwd_except`, before any forwarding map
/// exists: every slot is a field of a non-free scannable object, and a slot in
/// a pending object holds no nursery pointer at all (a pending object is not
/// written after it became garbage, and the nursery was empty then).  At
/// `no_pending` it is `ref_table_sound`.
let ref_table_sound_except (major_pre: heap) (pf: obj_addr -> prop)
                           (slots: seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (i: nat). i < n ==>
    (let addr = U64.v (Seq.index slots i) in
     addr < heap_size /\ addr % 8 == 0 /\
     (exists (obj: obj_addr) (j: nat).
       Seq.mem obj (objects zero_addr major_pre) /\
       is_blue obj major_pre = false /\
       is_no_scan obj major_pre = false /\
       j < U64.v (wosize_of_object obj major_pre) /\
       addr == U64.v obj + j * 8 /\
       (~(pf obj) \/
        ~(is_minor_pointer (to_minor_offset (read_word major_pre (U64.uint_to_t addr))))))))

val ref_table_sound_except_implies_fwd
  (major_pre: heap) (pf: obj_addr -> prop) (fwd: forwarding_map) (slots: seq U64.t) (n: nat)
  : Lemma (requires ref_table_sound_except major_pre pf slots n)
          (ensures ref_table_sound_fwd_except major_pre pf fwd slots n /\
                   valid_slot_addrs slots n)

val ref_table_sound_except_no_pending (major_pre: heap) (slots: seq U64.t) (n: nat)
  : Lemma (requires ref_table_sound major_pre slots n)
          (ensures ref_table_sound_except major_pre no_pending slots n)

/// ---------------------------------------------------------------------------
/// The two passes are the collection's pointer update
/// ---------------------------------------------------------------------------

val two_pass_implies_collect_except
  (minor: minor_state) (major_pre: heap) (fp: U64.t) (roots: seq U64.t)
  (pf: obj_addr -> prop)
  (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       Seq.length farr == fwd_array_size /\
       represents_fwd farr prom.fwd_map /\
       CheneyPres.fwd_valid_or_infix prom.fwd_map prom.major_final /\
       CheneyPres.fwd_normal_injective prom.fwd_map prom.major_final /\
       CheneySpec.fwd_bounded prom.fwd_map /\
       well_formed_heap_part4 prom.major_final /\
       valid_slot_addrs slots n /\
       slots_pairwise_distinct slots n /\
       pending_ok major_pre pf /\
       ref_table_sound_fwd_except major_pre pf prom.fwd_map slots n /\
       ref_table_complete_except major_pre pf prom.fwd_map slots n /\
       fwd_targets_stable prom.fwd_map /\
       well_formed_heap_part1 prom.major_final /\
       well_formed_heap_part1 major_pre /\ well_formed_heap_part4 major_pre /\
       minor_infix_wf minor /\
       minor_wf minor /\
       chain_objects_blue major_pre fp /\
       AllocLemmas.fl_valid major_pre fp TwoPass.heap_fuel /\
       AllocLemmas.fl_chain_terminates major_pre fp TwoPass.heap_fuel))
    (ensures
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       rewrite_slots_iter
         (update_promoted_iter prom.major_final farr prom.fwd_map 0)
         prom.fwd_map slots n 0
       == (CheneySpec.cheney_collect_spec_except minor major_pre fp roots pf).mc_major))

/// The stop-the-world instance.
val two_pass_implies_full_update
  (minor: minor_state) (major_pre: heap) (fp: U64.t) (roots: seq U64.t)
  (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       Seq.length farr == fwd_array_size /\
       represents_fwd farr prom.fwd_map /\
       CheneyPres.fwd_valid_or_infix prom.fwd_map prom.major_final /\
       CheneyPres.fwd_normal_injective prom.fwd_map prom.major_final /\
       CheneySpec.fwd_bounded prom.fwd_map /\
       well_formed_heap_part4 prom.major_final /\
       valid_slot_addrs slots n /\
       slots_pairwise_distinct slots n /\
       ref_table_sound major_pre slots n /\
       ref_table_complete major_pre prom.fwd_map slots n /\
       fwd_targets_stable prom.fwd_map /\
       well_formed_heap_part1 prom.major_final /\
       heap_objects_dense prom.major_final /\
       Seq.length (objects zero_addr prom.major_final) > 0 /\
       well_formed_heap_part1 major_pre /\ well_formed_heap_part4 major_pre /\
       minor_infix_wf minor /\
       minor_wf minor /\
       chain_objects_blue major_pre fp /\
       AllocLemmas.fl_valid major_pre fp TwoPass.heap_fuel /\
       AllocLemmas.fl_chain_terminates major_pre fp TwoPass.heap_fuel))
    (ensures
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       rewrite_slots_iter
         (update_promoted_iter prom.major_final farr prom.fwd_map 0)
         prom.fwd_map slots n 0
       == (CheneySpec.cheney_collect_spec minor major_pre fp roots).mc_major))
