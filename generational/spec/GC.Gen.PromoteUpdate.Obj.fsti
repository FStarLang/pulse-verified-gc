/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.Obj — Per-object pointer-update preservation lemmas
/// ---------------------------------------------------------------------------

module GC.Gen.PromoteUpdate.Obj

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
module WriteBody = GC.Gen.WriteBodyLemmas

val update_object_pointers_preserves_objects
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures objects zero_addr (update_object_pointers major obj wosize fwd i) == objects zero_addr major)

val update_object_pointers_preserves_other_header
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  (other: obj_addr)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      Seq.mem other (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      other <> obj /\
      U64.v other > U64.v obj /\
      wosize == U64.v (wosize_of_object obj major) /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures
      read_word (update_object_pointers major obj wosize fwd i) (hd_address other) ==
      read_word major (hd_address other))

val update_object_pointers_preserves_self_header
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures
      read_word (update_object_pointers major obj wosize fwd i) (hd_address obj) ==
      read_word major (hd_address obj))

val update_object_pointers_preserves_addr_below
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  (addr: hp_addr)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      U64.v addr < U64.v obj /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures
      read_word (update_object_pointers major obj wosize fwd i) addr ==
      read_word major addr)

val update_object_pointers_preserves_addr_above
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  (addr: hp_addr)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      U64.v addr >= U64.v obj + wosize * 8 /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures
      read_word (update_object_pointers major obj wosize fwd i) addr ==
      read_word major addr)

val update_object_pointers_field_self
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat) (j: nat)
  : Lemma
    (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      j < wosize /\
      i <= j /\
      (forall (k:nat). k < wosize ==>
        (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))
    (ensures
      (let updated = update_object_pointers major obj wosize fwd i in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_val = read_word major field_addr in
       let new_val = read_word updated field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> new_val == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> new_val == old_val)))

val update_obj_ptrs_preserves_earlier_field
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat) (j: nat)
  : Lemma
    (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      j < i /\ i <= wosize /\
      (forall (k:nat). k < wosize ==>
        (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))
    (ensures
      (let field_j_addr = U64.uint_to_t (U64.v obj + j * 8) in
       read_word (update_object_pointers major obj wosize fwd i) field_j_addr ==
       read_word major field_j_addr))
