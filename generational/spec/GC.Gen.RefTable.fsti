/// ---------------------------------------------------------------------------
/// GC.Gen.RefTable -- what the minor collection assumes of the remembered set
/// ---------------------------------------------------------------------------
///
/// The remembered set ("ref table") is the array `slots[0..n)` of major-heap
/// field addresses recorded by the write barrier.  The minor collection
/// rewrites those fields after promoting the nursery.  Its preconditions on
/// the table are stated for a definition `free` of what counts as free in the major heap
/// (`GC.Spec.Fields.free_def`); the stop-the-world forms are the instances at
/// `free_stw`.

module GC.Gen.RefTable

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.Promote

/// Every slot address is an aligned heap address.
let valid_slot_addrs (slots: seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (i: nat). i < n ==>
    (let addr = U64.v (Seq.index slots i) in
     addr < heap_size /\ addr % 8 == 0))

/// No slot is recorded twice, so the last write at an address is identified
/// by a single slot (`GC.Gen.TwoPassEquiv`).
let slots_pairwise_distinct (slots: seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (i j: nat). i < n /\ j < n /\ i <> j ==>
    U64.v (Seq.index slots i) <> U64.v (Seq.index slots j))

/// Coverage: every nursery pointer held by a field of a non-free, scannable
/// block is at a recorded slot.  The write barrier records old-major fields
/// when they are assigned nursery pointers, without knowing which nursery
/// objects will be live, so this does not mention a forwarding map.
let ref_table_covers_with (free: free_def) (major_pre: heap)
                          (slots: seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (obj: obj_addr) (j: nat).
    is_block major_pre obj /\ not (free major_pre obj) /\ scannable major_pre obj /\
    j < U64.v (wosize_of_object obj major_pre) /\
    U64.v obj + j * 8 + 8 <= heap_size /\
    is_minor_pointer (to_minor_offset (read_word major_pre (U64.uint_to_t (U64.v obj + j * 8)))) ==>
    (exists (i: nat). i < n /\ U64.v (Seq.index slots i) == U64.v obj + j * 8))

/// The forwarding-map form used by the proof: every field of a scannable
/// non-free block holding a *forwarded* nursery pointer is at a slot.
/// Quantifies over field positions (obj, j) rather than all aligned
/// addresses, because header words can look like forwarded nursery pointers.
let ref_table_complete_with (free: free_def) (major_pre: heap)
                            (fwd: forwarding_map) (slots: seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (obj: obj_addr) (j: nat).
    is_block major_pre obj /\ not (free major_pre obj) /\ scannable major_pre obj /\
    j < U64.v (wosize_of_object obj major_pre) /\
    U64.v obj + j * 8 + 8 <= heap_size /\
    (let field_val = to_minor_offset (read_word major_pre (U64.uint_to_t (U64.v obj + j * 8))) in
     is_minor_pointer field_val /\ fwd field_val <> 0UL) ==>
    (exists (i: nat). i < n /\ U64.v (Seq.index slots i) == U64.v obj + j * 8))

val ref_table_covers_with_implies_complete
  (free: free_def) (major_pre: heap) (fwd: forwarding_map) (slots: seq U64.t) (n: nat)
  : Lemma (requires ref_table_covers_with free major_pre slots n)
          (ensures ref_table_complete_with free major_pre fwd slots n)

/// Soundness: every slot is a field of a scannable non-free block, so
/// rewriting the slots touches only fields the pointer update also rewrites.
///
/// It holds because the table is emptied at every minor collection and an
/// entry is recorded only when the program writes a field, so the object was
/// reachable after the last minor collection.  Such an object is never about
/// to be freed: marking starts right after a minor collection, and under
/// a deletion barrier anything written during marking ends black.
let ref_table_sound_with (free: free_def) (major_pre: heap)
                         (slots: seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (i: nat). i < n ==>
    (let addr = U64.v (Seq.index slots i) in
     addr < heap_size /\ addr % 8 == 0 /\
     (exists (obj: obj_addr) (j: nat).
       is_block major_pre obj /\ not (free major_pre obj) /\ scannable major_pre obj /\
       j < U64.v (wosize_of_object obj major_pre) /\
       addr == U64.v obj + j * 8)))

val ref_table_sound_with_implies_valid_slot_addrs
  (free: free_def) (major_pre: heap) (slots: seq U64.t) (n: nat)
  : Lemma (requires ref_table_sound_with free major_pre slots n)
          (ensures valid_slot_addrs slots n)

/// The stop-the-world forms: the `free_stw` instances.
let ref_table_covers_minor_ptrs (major_pre: heap) (slots: seq U64.t) (n: nat) : prop =
  ref_table_covers_with free_stw major_pre slots n

let ref_table_sound (major_pre: heap) (slots: seq U64.t) (n: nat) : prop =
  ref_table_sound_with free_stw major_pre slots n
