/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.Aux — the pointer-update walk: objects, part 1, extensionality in the rewritten set
/// ---------------------------------------------------------------------------

module GC.Gen.PromoteUpdate.Aux

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
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas

module AllocLemmas = GC.Spec.Allocator.Lemmas
module WriteBody = GC.Gen.WriteBodyLemmas

/// Two heaps that agree on an object's header agree on everything the walk
/// reads from it.
val header_eq_object_facts (g1 g2: heap) (h: obj_addr)
  : Lemma (requires read_word g1 (hd_address h) == read_word g2 (hd_address h))
          (ensures wosize_of_object h g1 == wosize_of_object h g2 /\
                   is_no_scan h g1 == is_no_scan h g2 /\
                   is_blue h g1 == is_blue h g2 /\
                   is_infix h g1 == is_infix h g2)

/// One step of either walk rewrites only field words of `obj`: the object list,
/// part 1 and every object's header are unchanged.
val update_object_pointers_step (major: heap) (obj: obj_addr) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ Seq.mem obj (objects zero_addr major))
    (ensures (let wz = U64.v (wosize_of_object obj major) in
              let major' = update_object_pointers major obj wz fwd 0 in
              U64.v obj + wz * 8 <= heap_size /\
              (forall (k:nat). k < wz ==>
                (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)) /\
              objects zero_addr major' == objects zero_addr major /\
              well_formed_heap_part1 major' /\
              (forall (h: obj_addr). Seq.mem h (objects zero_addr major) ==>
                read_word major' (hd_address h) == read_word major (hd_address h))))

/// ---------------------------------------------------------------------------
/// The walk over a fixed set of objects
/// ---------------------------------------------------------------------------

val update_walk_preserves_objects
  (major: heap) (upd: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures objects zero_addr (update_walk major upd fwd) == objects zero_addr major)

val update_walk_preserves_wfh_part1
  (major: heap) (upd: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures well_formed_heap_part1 (update_walk major upd fwd))

/// Only the members of the rewritten set on the walk matter.
val update_walk_ext
  (major: heap) (upd1 upd2: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      (upd1 x <==> upd2 x))
    (ensures update_walk major upd1 fwd == update_walk major upd2 fwd)

/// ---------------------------------------------------------------------------
/// The stop-the-world instances
/// ---------------------------------------------------------------------------

val update_major_pointers_preserves_objects (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures objects zero_addr (update_major_pointers major fwd) == objects zero_addr major)

val update_major_pointers_preserves_wfh_part1 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures well_formed_heap_part1 (update_major_pointers major fwd))

