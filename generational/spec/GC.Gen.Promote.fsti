/// ---------------------------------------------------------------------------
/// GC.Gen.Promote — Specification of minor→major object promotion (copying)
/// ---------------------------------------------------------------------------
///
/// When the minor heap is full, all live minor-heap objects are promoted
/// (copied) to the major heap. This module defines:
///
/// 1. promote_object: copy a single minor object to the major heap
/// 2. promote_all: promote all reachable objects from a set of roots
/// 3. update_pointers: rewrite minor-heap pointers to their new major addresses
///
/// After promotion, the minor heap is reset (bump pointer → 0).
///
/// Key correctness property: every object reachable from roots in the
/// pre-promotion state is present in the post-promotion major heap with
/// identical field data (modulo pointer updates).

module GC.Gen.Promote

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap

/// ---------------------------------------------------------------------------
/// Forwarding Map
/// ---------------------------------------------------------------------------

/// A forwarding map records where each minor object was placed in the major heap.
/// It maps minor_obj_addr → major_obj_addr (or 0 if not promoted).
let forwarding_map = U64.t -> GTot U64.t

/// Empty forwarding: nothing promoted yet
let empty_forwarding : forwarding_map = fun _ -> 0UL

/// Extend forwarding with a new mapping
let extend_forwarding (fwd: forwarding_map) (minor_addr: U64.t) (major_addr: U64.t) : forwarding_map =
  fun a -> if a = minor_addr then major_addr else fwd a

/// ---------------------------------------------------------------------------
/// Promote a Single Object
/// ---------------------------------------------------------------------------

/// Copy `n` fields (words) from minor heap at `src_obj + (i+1)*8` to major heap at `dst + (i+1)*8`
val copy_fields (minor: minor_state) (major: heap) 
                (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : GTot heap

/// Result of promoting one object
noeq
type promote_one_result = {
  major_out : heap;         // updated major heap
  fp_out    : U64.t;        // updated major free-list pointer
  new_addr  : U64.t;        // address of object in major heap (0 if failed)
}

/// Promote a single object from minor heap to major heap.
///
/// 1. Read wosize and tag from minor object header
/// 2. Allocate in major heap via the major allocator
/// 3. Copy field data from minor to major
///
/// If major allocation fails (OOM), returns new_addr = 0.
val promote_object (minor: minor_state) (major: heap) (obj: U64.t)
                   (fp: U64.t) (wosize: nat{wosize > 0})
  : GTot promote_one_result

/// ---------------------------------------------------------------------------
/// Promote All Live Objects
/// ---------------------------------------------------------------------------

/// The set of roots for minor collection includes:
/// - Program stack roots (mutator roots pointing into minor heap)
/// - Remembered set (major-heap objects pointing into minor heap)
///
/// "Live" minor objects = objects reachable from these roots via
/// pointer fields within the minor heap.

/// Result of promoting all live objects
noeq
type promote_all_result = {
  major_final : heap;            // final major heap state
  fp_final    : U64.t;           // final free-list pointer
  fwd_map     : forwarding_map;  // maps old minor addrs to new major addrs
}

/// Promote all objects listed in `live_set` (in order).
/// Each promotion allocates in the major heap and records the forwarding.
val promote_all_spec (minor: minor_state) (major: heap)
                     (fp: U64.t) (live_set: seq U64.t)
  : GTot promote_all_result

/// ---------------------------------------------------------------------------
/// Pointer Update
/// ---------------------------------------------------------------------------

/// After all objects are promoted, update pointers:
/// - In the major heap: any field that pointed to a minor address
///   gets rewritten to the forwarded major address.
/// - In the roots: update root pointers similarly.
///
/// This ensures no dangling references to the (about to be reset) minor heap.

/// Update all pointers in the major heap that refer to minor addresses
val update_major_pointers (major: heap) (fwd: forwarding_map)
  : GTot heap

/// update_major_pointers is currently identity (placeholder)
val update_major_pointers_id (major: heap) (fwd: forwarding_map)
  : Lemma (update_major_pointers major fwd == major)

/// ---------------------------------------------------------------------------
/// Minor Collection (Full Spec)
/// ---------------------------------------------------------------------------

/// Result of a complete minor collection
noeq
type minor_collect_result = {
  mc_major  : heap;          // post-collection major heap
  mc_fp     : U64.t;         // post-collection free-list pointer
  mc_minor  : minor_state;   // reset minor heap (bump = 0)
}

/// Full minor collection specification:
/// 1. Determine live set (reachable from roots)
/// 2. Promote all live objects to major heap
/// 3. Update pointers in major heap
/// 4. Reset minor heap
///
/// Parameters:
///   minor: current minor heap state
///   major: current major heap state
///   fp: current major-heap free-list pointer
///   roots: addresses of root pointers (in stack + remembered set)
val minor_collect_spec (minor: minor_state) (major: heap)
                       (fp: U64.t) (roots: seq U64.t)
  : GTot minor_collect_result

/// Unfold lemma: mc_major is update_major_pointers applied to promote_all result
val minor_collect_spec_unfold (minor: minor_state) (major: heap)
                              (fp: U64.t) (roots: seq U64.t)
  : Lemma (let live_set = minor_objects minor in
           let prom_res = promote_all_spec minor major fp live_set in
           (minor_collect_spec minor major fp roots).mc_major ==
             update_major_pointers prom_res.major_final prom_res.fwd_map)

/// ---------------------------------------------------------------------------
/// Correctness Properties
/// ---------------------------------------------------------------------------

/// Helper: all destination addresses in copy_fields are valid hp_addr
let dst_fields_valid (dst_obj: U64.t) (n: nat) : prop =
  (forall (j:nat). j < n ==>
    (U64.v dst_obj + j * 8 + 8 <= heap_size /\
     (U64.v dst_obj + j * 8) % 8 == 0))

/// copy_fields doesn't modify addresses outside the dst region
val copy_fields_frame
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  (addr: hp_addr)
  : Lemma
    (requires
      dst_fields_valid dst_obj n /\
      U64.v dst_obj % 8 == 0 /\
      (U64.v addr + 8 <= U64.v dst_obj \/
       U64.v addr >= U64.v dst_obj + n * 8))
    (ensures
      read_word (copy_fields minor major src_obj dst_obj i n) addr ==
      read_word major addr)

/// Key lemma: copy_fields correctly copies all fields
val copy_fields_all_correct
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (n: nat)
  : Lemma
    (requires
      dst_fields_valid dst_obj n /\
      U64.v dst_obj % 8 == 0)
    (ensures
      (let result = copy_fields minor major src_obj dst_obj 0 n in
       (forall (j:nat). j < n ==>
         read_word result (U64.uint_to_t (U64.v dst_obj + j * 8)) ==
         minor_read_field minor src_obj j)))

/// After promotion, field data is preserved: every field of the promoted
/// object in the major heap equals the corresponding minor-heap field.
val promote_preserves_fields
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             U64.v obj >= 8 /\ U64.v obj < minor_heap_size)
          (ensures
             (let res = promote_object minor major obj fp wosize in
              res.new_addr <> 0UL ==>
              dst_fields_valid res.new_addr wosize ==>
              U64.v res.new_addr % 8 == 0 ==>
              (forall (j:nat). j < wosize ==>
                read_word res.major_out (U64.uint_to_t (U64.v res.new_addr + j * 8)) ==
                minor_read_field minor obj j)))

/// copy_fields preserves the objects walk (writes only within object bodies, never headers)
val copy_fields_preserves_objects
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (n: nat)
  : Lemma (requires
             well_formed_heap major /\
             Seq.mem dst_obj (objects 0UL major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n)
          (ensures
             objects 0UL (copy_fields minor major src_obj dst_obj 0 n) == objects 0UL major)

/// promote_object preserves existing object membership
val promote_object_preserves_objects
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap major /\
             GC.Spec.Allocator.Lemmas.fl_valid major fp (heap_size / U64.v mword))
          (ensures
             (let res = promote_object minor major obj fp wosize in
              (forall (x: obj_addr). Seq.mem x (objects 0UL major) ==>
                Seq.mem x (objects 0UL res.major_out))))

/// promote_all_spec preserves existing object membership
val promote_all_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires
             well_formed_heap major /\
             GC.Spec.Allocator.Lemmas.fl_valid major fp (heap_size / U64.v mword))
          (ensures
             (let res = promote_all_spec minor major fp live_set in
              (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                Seq.mem x (objects zero_addr res.major_final))))

/// After minor collection, every object that was reachable from roots
/// in (minor + major) is present in the post-collection major heap.
val minor_collect_preserves_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: U64.t)
  : Lemma (requires
             minor_wf minor /\
             Seq.mem obj (minor_objects minor))
          (ensures
             (let res = minor_collect_spec minor major fp roots in
              True))  // TODO: strengthen when reachability is defined
