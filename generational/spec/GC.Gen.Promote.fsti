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

/// ---------------------------------------------------------------------------
/// Correctness Properties
/// ---------------------------------------------------------------------------

/// After minor collection, every object that was reachable from roots
/// in (minor ∪ major) is present in the post-collection major heap.
val minor_collect_preserves_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: U64.t)
  : Lemma (requires
             minor_wf minor /\
             Seq.mem obj (minor_objects minor))  // obj is in minor heap
          (ensures
             (let res = minor_collect_spec minor major fp roots in
              // If obj was live, it's now in the major heap at fwd_map(obj)
              True))  // Placeholder — refined when we define reachability

/// After promotion, field data is preserved
val promote_preserves_fields
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             U64.v obj >= 8 /\ U64.v obj < minor_heap_size)
          (ensures
             (let res = promote_object minor major obj fp wosize in
              res.new_addr <> 0UL ==>
              (forall (i:nat). i >= 1 /\ i <= wosize ==>
                // Field data matches (modulo pointer forwarding)
                True)))  // Placeholder — refined with forwarding map
