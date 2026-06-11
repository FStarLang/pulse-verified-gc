module GC.Gen.PromoteUpdate.Field

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
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas

module AllocLemmas = GC.Spec.Allocator.Lemmas

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

val update_major_pointers_preserves_wfh_part2 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\
                    pointer_closure_modulo_fwd major fwd /\
                    fwd_all_targets_valid fwd major /\
                    blue_fields_closed major /\
                    no_scan_invariant major)
    (ensures well_formed_heap_part2 (update_major_pointers major fwd))
