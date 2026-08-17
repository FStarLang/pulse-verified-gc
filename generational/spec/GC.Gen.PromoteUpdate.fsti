/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate — Val signatures for pointer-update and promotion lemmas
/// ---------------------------------------------------------------------------
///
/// These val declarations were extracted from GC.Gen.Promote.fsti and are
/// implemented in GC.Gen.PromoteUpdate.fst.

module GC.Gen.PromoteUpdate

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
open GC.Gen.WriteBodyLemmas

module AllocLemmas = GC.Spec.Allocator.Lemmas
module FreeListShape = GC.Gen.FreeListShape

open GC.Gen.Promote

val update_major_pointers_preserves_objects (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures objects zero_addr (update_major_pointers major fwd) == objects zero_addr major)

/// update_major_pointers preserves well_formed_heap_part1
val update_major_pointers_preserves_wfh_part1 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures well_formed_heap_part1 (update_major_pointers major fwd))

/// Step lemma: unfold one iteration of update_all_objects_aux (non-blue, non-no-scan case)
val update_all_objects_aux_step (major: heap) (objs: seq obj_addr)
                                (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx < Seq.length objs /\ well_formed_heap_part1 major /\
                    objs == objects zero_addr major /\
                    is_blue (Seq.index objs idx) major = false /\
                    is_no_scan (Seq.index objs idx) major = false)
          (ensures (let obj = Seq.index objs idx in
                    let wz = U64.v (wosize_of_object obj major) in
                    update_all_objects_aux major objs fwd idx ==
                    update_all_objects_aux (update_object_pointers major obj wz fwd 0) objs fwd (idx + 1)))

/// Blue skip step: when the object at idx is blue, skip without modifying heap
val update_all_objects_aux_skip_blue (major: heap) (objs: seq obj_addr)
                                     (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx < Seq.length objs /\
                    is_blue (Seq.index objs idx) major)
          (ensures update_all_objects_aux major objs fwd idx ==
                   update_all_objects_aux major objs fwd (idx + 1))

/// No-scan skip step: when the object at idx is no-scan, skip without modifying heap
val update_all_objects_aux_skip_no_scan (major: heap) (objs: seq obj_addr)
                                        (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx < Seq.length objs /\
                    is_blue (Seq.index objs idx) major = false /\
                    is_no_scan (Seq.index objs idx) major)
          (ensures update_all_objects_aux major objs fwd idx ==
                   update_all_objects_aux major objs fwd (idx + 1))

/// Done lemma: identity when idx >= Seq.length objs
val update_all_objects_aux_done (major: heap) (objs: seq obj_addr)
                                (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx >= Seq.length objs)
          (ensures update_all_objects_aux major objs fwd idx == major)

/// Connection: update_major_pointers unfolds to update_all_objects_aux at index 0
val update_major_pointers_unfold (major: heap) (fwd: forwarding_map)
  : Lemma (update_major_pointers major fwd ==
           update_all_objects_aux major (objects zero_addr major) fwd 0)

/// Master positional step lemma for the Pulse loop.
val update_all_objects_positional_step
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major = false /\
                    is_no_scan (f_address pos) major = false)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let major' = update_object_pointers major obj wz fwd 0 in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\ next_nat < pow2 64 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    well_formed_heap_part1 major' /\
                    heap_objects_dense major' /\
                    objects zero_addr major' == objects zero_addr major /\
                    // Spec equality: when next is still within heap bounds
                    (next_nat < heap_size ==>
                      update_all_objects_aux major' (objects (U64.uint_to_t next_nat) major') fwd 0 ==
                        update_all_objects_aux major (objects pos major) fwd 0) /\
                    // Terminal: when next reaches/exceeds heap_size
                    (next_nat >= heap_size ==>
                      major' == update_all_objects_aux major (objects pos major) fwd 0) /\
                    // Density: next position is valid (when not done)
                    (next_nat + 8 < heap_size ==>
                      Seq.mem (f_address (U64.uint_to_t next_nat)) (objects zero_addr major') /\
                      Seq.length (objects (U64.uint_to_t next_nat) major') > 0)))

/// Blue positional step: when the object is blue, skip without modification
val update_all_objects_positional_step_blue
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\ next_nat < pow2 64 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    // Spec: skipping blue advances to the next object with same heap
                    (next_nat < heap_size ==>
                      update_all_objects_aux major (objects (U64.uint_to_t next_nat) major) fwd 0 ==
                        update_all_objects_aux major (objects pos major) fwd 0) /\
                    // Terminal: when next reaches heap_size, result is just major
                    (next_nat >= heap_size ==>
                      major == update_all_objects_aux major (objects pos major) fwd 0) /\
                    // Density: next position is valid
                    (next_nat + 8 < heap_size ==>
                      Seq.mem (f_address (U64.uint_to_t next_nat)) (objects zero_addr major) /\
                      Seq.length (objects (U64.uint_to_t next_nat) major) > 0)))

/// No-scan positional step: when the object has tag >= no_scan_tag, skip it
val update_all_objects_positional_step_no_scan
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major = false /\
                    is_no_scan (f_address pos) major)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\ next_nat < pow2 64 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    (next_nat < heap_size ==>
                      update_all_objects_aux major (objects (U64.uint_to_t next_nat) major) fwd 0 ==
                        update_all_objects_aux major (objects pos major) fwd 0) /\
                    (next_nat >= heap_size ==>
                      major == update_all_objects_aux major (objects pos major) fwd 0) /\
                    (next_nat + 8 < heap_size ==>
                      Seq.mem (f_address (U64.uint_to_t next_nat)) (objects zero_addr major) /\
                      Seq.length (objects (U64.uint_to_t next_nat) major) > 0)))

/// Terminal step: when next_pos >= heap_size, processing gives the final result.
val update_all_objects_terminal_step
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major = false /\
                    is_no_scan (f_address pos) major = false)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    (next_nat + 8 >= heap_size ==>
                      (let major' = update_object_pointers major obj wz fwd 0 in
                       major' == update_all_objects_aux major (objects pos major) fwd 0))))

/// The first object in objects zero_addr is at position 0 (when heap_size > 8)
val objects_initial_membership (g: heap)
  : Lemma (requires heap_size > 8 /\ well_formed_heap_part1 g /\
                    Seq.length (objects zero_addr g) > 0)
          (ensures Seq.mem (f_address zero_addr) (objects zero_addr g))

/// update_major_pointers preserves object headers
val update_major_pointers_preserves_header (major: heap) (fwd: forwarding_map) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 major /\ Seq.mem h (objects zero_addr major))
    (ensures read_word (update_major_pointers major fwd) (hd_address h) ==
             read_word major (hd_address h))

/// update_major_pointers preserves all fields of blue objects
val update_major_pointers_preserves_blue_field
  (major: heap) (fwd: forwarding_map) (h: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    Seq.mem h (objects zero_addr major) /\
                    is_blue h major /\
                    j < U64.v (wosize_of_object h major) /\
                    U64.v h + j * 8 + 8 <= heap_size /\
                    (U64.v h + j * 8) % 8 == 0)
    (ensures (let field_addr = U64.uint_to_t (U64.v h + j * 8) in
              read_word (update_major_pointers major fwd) field_addr ==
              read_word major field_addr))

/// update_major_pointers preserves all fields of no-scan objects
val update_major_pointers_preserves_no_scan_field
  (major: heap) (fwd: forwarding_map) (h: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    Seq.mem h (objects zero_addr major) /\
                    is_no_scan h major /\
                    ~(is_blue h major) /\
                    j < U64.v (wosize_of_object h major) /\
                    U64.v h + j * 8 + 8 <= heap_size /\
                    (U64.v h + j * 8) % 8 == 0)
    (ensures (let field_addr = U64.uint_to_t (U64.v h + j * 8) in
              read_word (update_major_pointers major fwd) field_addr ==
              read_word major field_addr))

/// update_major_pointers preserves well_formed_heap_part4 (no infix objects)
val update_major_pointers_preserves_wfh_part4 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ well_formed_heap_part4 major)
    (ensures well_formed_heap_part4 (update_major_pointers major fwd))

/// update_major_pointers preserves well_formed_heap_part3 (infix well-formedness)
val update_major_pointers_preserves_wfh_part3 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ well_formed_heap_part4 major)
    (ensures well_formed_heap_part3 (update_major_pointers major fwd))

/// promote_all_spec produces fwd_all_targets_valid for its final heap.
val promote_all_fwd_all_targets_valid
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words)
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fwd_all_targets_valid res.fwd_map res.major_final))

/// After promote_all_spec, every forwarded object's address is in objects of the final heap.
val promote_all_adds_promoted
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words)
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
             AllocLemmas.fl_valid major fp heap_words /\
             AllocLemmas.fl_chain_terminates major fp heap_words /\
             Seq.mem obj (live_set_of minor major roots))
          (ensures
             (let res = minor_collect_spec minor major fp roots in
              let live_set = live_set_of minor major roots in
              let prom_res = promote_all_spec minor major fp live_set in
              fwd_targets_in_objects prom_res.fwd_map live_set (Seq.length live_set) res.mc_major))

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
      (U64.v obj + j * 8) % 8 == 0 /\
      is_blue obj major = false /\
      is_no_scan obj major = false)
    (ensures
      (let updated = update_major_pointers major fwd in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_raw = read_word major field_addr in
       let old_val = to_minor_offset old_raw in
       let new_val = read_word updated field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> new_val == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> new_val == old_raw)))

/// update_major_pointers establishes well_formed_heap_part2 (pointer closure):
/// If the intermediate heap has pointer_closure_modulo_fwd and fwd targets are valid,
/// and blue objects' pointer fields target valid objects (blue_fields_closed),
/// and no-scan objects' fields don't look like pointers (no_scan_invariant),
/// then after update the result satisfies part2.
val update_major_pointers_preserves_wfh_part2 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\
                    pointer_closure_modulo_fwd major fwd /\
                    fwd_all_targets_valid fwd major /\
                    blue_fields_closed major /\
                    no_scan_invariant major)
    (ensures well_formed_heap_part2 (update_major_pointers major fwd))

/// Distinctness: no two positions in live_set share the same address.
let distinct_live_set (live_set: seq U64.t) : prop =
  forall (i j: nat). i < Seq.length live_set /\ j < Seq.length live_set /\ i <> j ==>
    Seq.index live_set i <> Seq.index live_set j

/// After promote_all_spec, all promoted objects' fields match the minor heap values.
/// This is the pre-pointer-update field correspondence.
val promote_all_preserves_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    distinct_live_set live_set)
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fields_match_minor minor res.major_final res.fwd_map
                                       live_set (Seq.length live_set)))

/// For objects in the original major heap that avoid the free chain, their body
/// contents are unchanged through the entire promote_all_spec operation.
/// This is critical for proving well_formed_heap_part2 after promotion:
/// non-promoted objects' pointer fields still target valid objects.
val promote_all_read_other
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  (other: obj_addr) (addr: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    Seq.mem other (objects zero_addr major) /\
                    AllocLemmas.chain_avoids major fp other heap_words = true /\
                    U64.v addr >= U64.v other /\
                    U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other major) * 8)
          (ensures (let res = promote_all_spec minor major fp live_set in
                    read_word res.major_final addr == read_word major addr))

/// promote_object preserves chain_objects_blue
val promote_object_preserves_chain_objects_blue
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      chain_objects_blue major fp /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      chain_objects_blue (promote_object minor major obj fp wosize).major_out
                         (promote_object minor major obj fp wosize).fp_out)

val promote_object_preserves_free_list_shape
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      FreeListShape.fp_pointer_or_zero fp /\
      FreeListShape.blue_link_fields_valid major /\
      chain_objects_blue major fp /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      FreeListShape.fp_pointer_or_zero
        (promote_object minor major obj fp wosize).fp_out /\
      FreeListShape.blue_link_fields_valid
        (promote_object minor major obj fp wosize).major_out)

/// After promote_all_spec, blue objects' pointer fields still target valid objects.
/// Requires chain_objects_blue: the free chain only contains blue objects.
/// This is needed because allocation modifies the predecessor's field 0 (chain link)
/// and the new value (remainder or next_fp) must target a valid object.
/// Since chain nodes are blue, bfc(major) ensures their fields target objects.
val promote_all_preserves_blue_fields_closed
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp)
          (ensures blue_fields_closed (promote_all_spec minor major fp live_set).major_final)

/// Unfold: mc_major of all-objects collection
val minor_collect_all_spec_unfold (minor: minor_state) (major: heap)
                                   (fp: U64.t) (roots: seq U64.t)
  : Lemma (let all_objs = minor_objects minor in
           let prom_res = promote_all_spec minor major fp all_objs in
           (minor_collect_all_spec minor major fp roots).mc_major ==
             update_major_pointers prom_res.major_final prom_res.fwd_map /\
           (minor_collect_all_spec minor major fp roots).mc_fwd == prom_res.fwd_map /\
           (minor_collect_all_spec minor major fp roots).mc_fp == prom_res.fp_final)
