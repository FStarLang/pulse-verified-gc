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
open GC.Gen.Reachability
open GC.Gen.Remembered

module AllocLemmas = GC.Spec.Allocator.Lemmas

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

/// Base case: copy_fields with i >= n is identity
val copy_fields_base (minor: minor_state) (major: heap) 
                     (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : Lemma (requires i >= n)
          (ensures copy_fields minor major src_obj dst_obj i n == major)
          [SMTPat (copy_fields minor major src_obj dst_obj i n)]

/// Step lemma: one recursive unfolding of copy_fields
val copy_fields_step (minor: minor_state) (major: heap) 
                     (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : Lemma (requires i < n /\
                     U64.v dst_obj + i * 8 + 8 <= heap_size /\
                     (U64.v dst_obj + i * 8) % 8 == 0)
           (ensures copy_fields minor major src_obj dst_obj i n ==
                    copy_fields minor
                      (write_word major (U64.uint_to_t (U64.v dst_obj + i * 8))
                                       (minor_read_field minor src_obj i))
                      src_obj dst_obj (i + 1) n)
           [SMTPat (copy_fields minor major src_obj dst_obj i n)]

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

/// Unfold: when alloc fails (OOM), promote_object returns original heap/fp unchanged.
val promote_object_oom (minor: minor_state) (major: heap) (obj: U64.t)
                       (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out == 0UL)
          (ensures (let res = promote_object minor major obj fp wosize in
                    res.major_out == major /\ res.fp_out == fp /\ res.new_addr == 0UL))

/// Unfold: when alloc succeeds, promote_object = alloc + copy_fields.
val promote_object_success (minor: minor_state) (major: heap) (obj: U64.t)
                           (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out <> 0UL)
          (ensures (let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
                    let res = promote_object minor major obj fp wosize in
                    res.major_out == copy_fields minor alloc_res.heap_out obj alloc_res.obj_out 0 wosize /\
                    res.fp_out == alloc_res.fp_out /\
                    res.new_addr == alloc_res.obj_out))

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

/// Check if a value looks like a minor-heap pointer
let is_minor_pointer (v: U64.t) : bool =
  U64.v v >= 8 && U64.v v < minor_heap_size && U64.v v % 8 = 0

/// Update pointers in one object's fields: iterate fields [i, wosize) and rewrite
/// minor-heap pointers via the forwarding map.
val update_object_pointers (major: heap) (obj: U64.t) (wosize: nat)
                           (fwd: forwarding_map) (i: nat)
  : GTot heap

/// Unfold lemma: one step of update_object_pointers when i < wosize
val update_object_pointers_step (major: heap) (obj: U64.t) (wosize: nat)
                                (fwd: forwarding_map) (i: nat)
  : Lemma (requires i < wosize /\
                    U64.v obj + i * 8 + 8 <= heap_size /\
                    (U64.v obj + i * 8) % 8 = 0)
          (ensures (let field_offset = U64.v obj + i * 8 in
                    let field_val = read_word major (U64.uint_to_t field_offset) in
                    update_object_pointers major obj wosize fwd i ==
                    (if is_minor_pointer field_val then
                       let new_val = fwd field_val in
                       if new_val <> 0UL then
                         update_object_pointers (write_word major (U64.uint_to_t field_offset) new_val) obj wosize fwd (i + 1)
                       else
                         update_object_pointers major obj wosize fwd (i + 1)
                     else
                       update_object_pointers major obj wosize fwd (i + 1))))

/// Base case: update_object_pointers at i >= wosize is identity
val update_object_pointers_done (major: heap) (obj: U64.t) (wosize: nat)
                                (fwd: forwarding_map) (i: nat)
  : Lemma (requires i >= wosize)
          (ensures update_object_pointers major obj wosize fwd i == major)

/// Update all pointers in the major heap that refer to minor addresses
val update_major_pointers (major: heap) (fwd: forwarding_map)
  : GTot heap

/// ---------------------------------------------------------------------------
/// Live Set and Root Rewriting
/// ---------------------------------------------------------------------------

/// Compute the live set: minor objects reachable from program roots combined
/// with the remembered set (major-heap objects pointing into the minor heap).
let live_set_of (minor: minor_state) (major: heap) (roots: seq U64.t) : GTot (seq U64.t) =
  let remembered = minor_roots_from_major major in
  minor_reachable minor (Seq.append roots remembered)

/// Rewrite a single root: if it's a minor pointer that was forwarded, use the new address
let rewrite_root (r: U64.t) (fwd: forwarding_map) : GTot U64.t =
  if is_minor_pointer r && fwd r <> 0UL then fwd r else r

/// Rewrite all roots using the forwarding map
val rewrite_roots (roots: seq U64.t) (fwd: forwarding_map) : GTot (seq U64.t)

/// rewrite_roots has the same length as roots
val rewrite_roots_length (roots: seq U64.t) (fwd: forwarding_map)
  : Lemma (ensures Seq.length (rewrite_roots roots fwd) == Seq.length roots)
    [SMTPat (rewrite_roots roots fwd)]

/// rewrite_roots applies rewrite_root pointwise
val rewrite_roots_index (roots: seq U64.t) (fwd: forwarding_map) (i: nat)
  : Lemma (requires i < Seq.length roots)
          (ensures Seq.index (rewrite_roots roots fwd) i == rewrite_root (Seq.index roots i) fwd)

/// If a sequence has rewrite_root applied pointwise, it equals rewrite_roots
val rewrite_roots_pointwise (roots: seq U64.t) (fwd: forwarding_map) (rs2: seq U64.t)
  : Lemma (requires Seq.length rs2 == Seq.length roots /\
                    (forall (j: nat). j < Seq.length roots ==>
                      Seq.index rs2 j == rewrite_root (Seq.index roots j) fwd))
          (ensures rs2 == rewrite_roots roots fwd)

/// ---------------------------------------------------------------------------
/// Minor Collection (Full Spec)
/// ---------------------------------------------------------------------------

/// Result of a complete minor collection
noeq
type minor_collect_result = {
  mc_major  : heap;            // post-collection major heap
  mc_fp     : U64.t;           // post-collection free-list pointer
  mc_minor  : minor_state;     // reset minor heap (bump = 0)
  mc_roots  : seq U64.t;       // rewritten roots (minor pointers → major addresses)
  mc_fwd    : forwarding_map;  // forwarding map (for spec-level reasoning)
}

/// Full minor collection specification:
/// 1. Determine live set (reachable from roots + remembered set)
/// 2. Promote all live objects to major heap
/// 3. Update pointers in major heap
/// 4. Rewrite roots to point to new major addresses
/// 5. Reset minor heap
///
/// Parameters:
///   minor: current minor heap state
///   major: current major heap state
///   fp: current major-heap free-list pointer
///   roots: addresses of root pointers (program stack)
val minor_collect_spec (minor: minor_state) (major: heap)
                       (fp: U64.t) (roots: seq U64.t)
  : GTot minor_collect_result

/// Unfold lemma: mc_major is update_major_pointers applied to promote_all result
val minor_collect_spec_unfold (minor: minor_state) (major: heap)
                              (fp: U64.t) (roots: seq U64.t)
  : Lemma (let live_set = live_set_of minor major roots in
           let prom_res = promote_all_spec minor major fp live_set in
           (minor_collect_spec minor major fp roots).mc_major ==
             update_major_pointers prom_res.major_final prom_res.fwd_map /\
           (minor_collect_spec minor major fp roots).mc_fwd == prom_res.fwd_map /\
           (minor_collect_spec minor major fp roots).mc_fp == prom_res.fp_final)

/// Unfold lemma: mc_minor is minor_reset minor (well-formed, bump = 0)
val minor_collect_resets_minor (minor: minor_state) (major: heap)
                               (fp: U64.t) (roots: seq U64.t)
  : Lemma (let res = minor_collect_spec minor major fp roots in
           minor_wf res.mc_minor /\ U64.v res.mc_minor.bump == 0)

/// Unfold lemma: mc_roots is rewrite_roots applied to roots
val minor_collect_rewrites_roots (minor: minor_state) (major: heap)
                                  (fp: U64.t) (roots: seq U64.t)
  : Lemma (let res = minor_collect_spec minor major fp roots in
           res.mc_roots == rewrite_roots roots res.mc_fwd)

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

/// copy_fields preserves the allocator invariants (wfh_part1, fl_valid, fl_chain_terminates)
/// when dst_obj is not in the free-list chain.
/// This is the key lemma enabling Pulse promote_one to maintain loop invariants.
val copy_fields_preserves_alloc_invariants
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (n: nat{n > 0})
  (fp: U64.t)
  : Lemma (requires
             well_formed_heap_part1 major /\
             Seq.mem dst_obj (objects 0UL major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
             AllocLemmas.chain_avoids major fp dst_obj (heap_size / U64.v mword) = true)
           (ensures (let g' = copy_fields minor major src_obj dst_obj 0 n in
                     well_formed_heap_part1 g' /\
                     AllocLemmas.fl_valid g' fp (heap_size / U64.v mword) /\
                     AllocLemmas.fl_chain_terminates g' fp (heap_size / U64.v mword)))

/// promote_all_spec preserves existing object membership
val promote_all_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires
             well_formed_heap major /\
             GC.Spec.Allocator.Lemmas.fl_valid major fp (heap_size / U64.v mword) /\
             GC.Spec.Allocator.Lemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures
             (let res = promote_all_spec minor major fp live_set in
              (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                Seq.mem x (objects zero_addr res.major_final))))

/// promote_all_spec preserves well_formed_heap_part1
val promote_all_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures well_formed_heap_part1 (promote_all_spec minor major fp live_set).major_final)

/// promote_all_spec preserves well_formed_heap_part4 (no infix objects)
val promote_all_preserves_wfh_part4
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures well_formed_heap_part4 (promote_all_spec minor major fp live_set).major_final)

/// update_major_pointers preserves the objects walk
val update_major_pointers_preserves_objects (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures objects zero_addr (update_major_pointers major fwd) == objects zero_addr major)

/// update_major_pointers preserves well_formed_heap_part1
val update_major_pointers_preserves_wfh_part1 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures well_formed_heap_part1 (update_major_pointers major fwd))

/// update_major_pointers preserves well_formed_heap_part4 (no infix objects)
val update_major_pointers_preserves_wfh_part4 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ well_formed_heap_part4 major)
    (ensures well_formed_heap_part4 (update_major_pointers major fwd))

/// update_major_pointers preserves well_formed_heap_part3 (infix well-formedness)
val update_major_pointers_preserves_wfh_part3 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ well_formed_heap_part4 major)
    (ensures well_formed_heap_part3 (update_major_pointers major fwd))

/// Predicate: every forwarded object's address is in the objects of heap g
let fwd_targets_in_objects (fwd: forwarding_map) (live_set: seq U64.t) (idx: nat) (g: heap) : prop =
  forall (k:nat). k < idx /\ k < Seq.length live_set ==>
    (let obj = Seq.index live_set k in
     fwd obj <> 0UL ==>
     (U64.v (fwd obj) >= U64.v mword /\
      U64.v (fwd obj) < heap_size /\
      U64.v (fwd obj) % U64.v mword == 0 /\
      Seq.mem ((fwd obj) <: obj_addr) (objects zero_addr g)))

/// Stronger invariant: for ANY address x, if fwd(x) ≠ 0, then fwd(x) is valid object in g.
let fwd_all_targets_valid (fwd: forwarding_map) (g: heap) : prop =
  forall (x: U64.t). fwd x <> 0UL ==>
    (U64.v (fwd x) >= U64.v mword /\
     U64.v (fwd x) < heap_size /\
     U64.v (fwd x) % U64.v mword == 0 /\
     Seq.mem ((fwd x) <: obj_addr) (objects zero_addr g))

/// promote_all_spec produces fwd_all_targets_valid for its final heap.
val promote_all_fwd_all_targets_valid
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fwd_all_targets_valid res.fwd_map res.major_final))

/// After promote_all_spec, every forwarded object's address is in objects of the final heap.
val promote_all_adds_promoted
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fwd_targets_in_objects res.fwd_map live_set (Seq.length live_set) res.major_final))

/// After minor collection, every promoted object's forwarded address
/// is in the post-collection major heap's objects list.
val minor_collect_preserves_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: U64.t)
  : Lemma (requires
             minor_wf minor /\
             well_formed_heap major /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
             Seq.mem obj (live_set_of minor major roots))
          (ensures
             (let res = minor_collect_spec minor major fp roots in
              let live_set = live_set_of minor major roots in
              let prom_res = promote_all_spec minor major fp live_set in
              fwd_targets_in_objects prom_res.fwd_map live_set (Seq.length live_set) res.mc_major))

/// ---------------------------------------------------------------------------
/// Field effect of update_major_pointers
/// ---------------------------------------------------------------------------

/// Specifies the effect of update_major_pointers on a single field:
/// After the update, field j of object obj is either:
///   - fwd(old_value) if the old value was a minor pointer with valid forwarding
///   - the old value otherwise
val update_major_pointers_field_effect
  (major: heap) (fwd: forwarding_map) (obj: obj_addr) (j: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.mem obj (objects zero_addr major) /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v obj + j * 8 + 8 <= heap_size /\
      (U64.v obj + j * 8) % 8 == 0)
    (ensures
      (let updated = update_major_pointers major fwd in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_val = read_word major field_addr in
       let new_val = read_word updated field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> new_val == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> new_val == old_val)))

/// Pointer closure modulo forwarding: every pointer field value v that is NOT
/// a rewritable minor pointer (i.e., ~(is_minor_pointer v /\ fwd v <> 0)) is in objects.
/// This is weaker than well_formed_heap_part2 because fields that will be rewritten
/// by update_major_pointers don't need to be valid yet.
let pointer_closure_modulo_fwd (major: heap) (fwd: forwarding_map) : prop =
  forall (src: obj_addr) (j: nat).
    Seq.mem src (objects 0UL major) /\
    j < U64.v (wosize_of_object src major) /\
    U64.v src + j * 8 + 8 <= heap_size ==>
    (let v = read_word major (U64.uint_to_t (U64.v src + j * 8)) in
     is_pointer v /\ ~(is_minor_pointer v /\ fwd v <> 0UL) ==>
     Seq.mem (v <: obj_addr) (objects 0UL major))

/// update_major_pointers establishes well_formed_heap_part2 (pointer closure):
/// If the intermediate heap has pointer_closure_modulo_fwd and fwd targets are valid,
/// then after update the result satisfies part2.
val update_major_pointers_preserves_wfh_part2 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\
                    pointer_closure_modulo_fwd major fwd /\
                    fwd_all_targets_valid fwd major)
    (ensures well_formed_heap_part2 (update_major_pointers major fwd))

/// ---------------------------------------------------------------------------
/// Field correspondence: promote_all_spec preserves all promoted fields
/// ---------------------------------------------------------------------------

/// Predicate: all promoted objects in the major heap have field data matching
/// the original minor-heap values (pre-pointer-update).
let fields_match_minor (minor: minor_state) (major: heap) (fwd: forwarding_map)
                       (live_set: seq U64.t) (idx: nat) : prop =
  forall (k:nat). k < idx /\ k < Seq.length live_set ==>
    (let obj = Seq.index live_set k in
     let wz = minor_wosize minor obj in
     fwd obj <> 0UL /\ wz > 0 ==>
     (let new_addr = fwd obj in
      dst_fields_valid new_addr wz /\
      U64.v new_addr % 8 == 0 ==>
      (forall (j:nat). j < wz ==>
        read_word major (U64.uint_to_t (U64.v new_addr + j * 8)) ==
        minor_read_field minor obj j)))

/// After promote_all_spec, all promoted objects' fields match the minor heap values.
/// This is the pre-pointer-update field correspondence.
val promote_all_preserves_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fields_match_minor minor res.major_final res.fwd_map
                                       live_set (Seq.length live_set)))

/// ---------------------------------------------------------------------------
/// Frame lemma: promote_all_spec preserves reads in non-promoted object bodies
/// ---------------------------------------------------------------------------

/// For objects in the original major heap that avoid the free chain, their body
/// contents are unchanged through the entire promote_all_spec operation.
/// This is critical for proving well_formed_heap_part2 after promotion:
/// non-promoted objects' pointer fields still target valid objects.
val promote_all_read_other
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  (other: obj_addr) (addr: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Seq.mem other (objects 0UL major) /\
                    AllocLemmas.chain_avoids major fp other (heap_size / U64.v mword) = true /\
                    U64.v addr >= U64.v other /\
                    U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other major) * 8)
          (ensures (let res = promote_all_spec minor major fp live_set in
                    read_word res.major_final addr == read_word major addr))

/// ---------------------------------------------------------------------------
/// All-Objects Minor Collection (matches linear-walk implementation)
/// ---------------------------------------------------------------------------

/// Minor collection that promotes ALL minor objects (not just reachable ones).
/// This matches the implementation's linear walk from 0 to bump.
/// Sound overapproximation: live_set_of ⊆ minor_objects, so all live objects
/// are promoted. Extra promotions don't break any invariant.
let minor_collect_all_spec (minor: minor_state) (major: heap)
                            (fp: U64.t) (roots: seq U64.t)
  : GTot minor_collect_result =
  let all_objs = minor_objects minor in
  let prom_res = promote_all_spec minor major fp all_objs in
  let updated = update_major_pointers prom_res.major_final prom_res.fwd_map in
  { mc_major = updated;
    mc_fp    = prom_res.fp_final;
    mc_minor = minor_reset minor;
    mc_roots = rewrite_roots roots prom_res.fwd_map;
    mc_fwd   = prom_res.fwd_map }

/// Unfold: mc_major of all-objects collection
val minor_collect_all_spec_unfold (minor: minor_state) (major: heap)
                                   (fp: U64.t) (roots: seq U64.t)
  : Lemma (let all_objs = minor_objects minor in
           let prom_res = promote_all_spec minor major fp all_objs in
           (minor_collect_all_spec minor major fp roots).mc_major ==
             update_major_pointers prom_res.major_final prom_res.fwd_map /\
           (minor_collect_all_spec minor major fp roots).mc_fwd == prom_res.fwd_map /\
           (minor_collect_all_spec minor major fp roots).mc_fp == prom_res.fp_final)
