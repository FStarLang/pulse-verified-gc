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
open GC.Gen.WriteBodyLemmas

module AllocLemmas = GC.Spec.Allocator.Lemmas
module FreeListShape = GC.Gen.FreeListShape

open GC.Gen.Promote

/// ---------------------------------------------------------------------------
/// The pointer update over a fixed set of objects (`update_walk`)
/// ---------------------------------------------------------------------------
///
/// The walk rewrites the fields of the scannable objects in its set `upd` and
/// nothing else.  Each `update_major_pointers_*` lemma below is the instance
/// at `not_freed major no_pending` (`update_major_pointers` is defined so),
/// with `is_blue x` read as "`x` is not rewritten".

val update_walk_preserves_objects
  (major: heap) (upd: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures objects zero_addr (update_walk major upd fwd) == objects zero_addr major)

val update_walk_preserves_wfh_part1
  (major: heap) (upd: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures well_formed_heap_part1 (update_walk major upd fwd))

val update_walk_ext
  (major: heap) (upd1 upd2: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      (upd1 x <==> upd2 x))
    (ensures update_walk major upd1 fwd == update_walk major upd2 fwd)

val update_walk_preserves_header
  (major: heap) (upd: obj_addr -> prop) (fwd: forwarding_map) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 major /\ Seq.mem h (objects zero_addr major))
    (ensures read_word (update_walk major upd fwd) (hd_address h) ==
             read_word major (hd_address h))

val update_walk_preserves_skipped_field
  (major: heap) (upd: obj_addr -> prop) (fwd: forwarding_map) (h: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    Seq.mem h (objects zero_addr major) /\
                    (~(upd h) \/ is_no_scan h major) /\
                    j < U64.v (wosize_of_object h major) /\
                    U64.v h + j * 8 + 8 <= heap_size /\
                    (U64.v h + j * 8) % 8 == 0)
    (ensures (let field_addr = U64.uint_to_t (U64.v h + j * 8) in
              read_word (update_walk major upd fwd) field_addr ==
              read_word major field_addr))

val update_walk_preserves_wfh_part4
  (major: heap) (upd: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ well_formed_heap_part4 major)
    (ensures well_formed_heap_part4 (update_walk major upd fwd))

val update_walk_field_effect
  (major: heap) (upd: obj_addr -> prop) (fwd: forwarding_map) (obj: obj_addr) (j: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.mem obj (objects zero_addr major) /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v obj + j * 8 + 8 <= heap_size /\
      (U64.v obj + j * 8) % 8 == 0 /\
      upd obj /\
      is_no_scan obj major = false)
    (ensures
      (let updated = update_walk major upd fwd in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_raw = read_word major field_addr in
       let old_val = to_minor_offset old_raw in
       let new_val = read_word updated field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> new_val == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> new_val == old_raw)))

/// ---------------------------------------------------------------------------
/// The idle walk (`update_major_pointers`)
/// ---------------------------------------------------------------------------

val update_major_pointers_preserves_objects (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures objects zero_addr (update_major_pointers major fwd) == objects zero_addr major)

/// update_major_pointers preserves well_formed_heap_part1
val update_major_pointers_preserves_wfh_part1 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures well_formed_heap_part1 (update_major_pointers major fwd))
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
