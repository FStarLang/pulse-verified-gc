/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.Aux — Auxiliary update_all_objects lemmas
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
/// The walk over a live set
/// ---------------------------------------------------------------------------

val update_live_pointers_preserves_objects
  (major: heap) (live: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures objects zero_addr (update_live_pointers major live fwd) == objects zero_addr major)

val update_live_pointers_preserves_wfh_part1
  (major: heap) (live: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures well_formed_heap_part1 (update_live_pointers major live fwd))

/// Only the live set's members on the walk matter.
val update_live_pointers_ext
  (major: heap) (live1 live2: obj_addr -> prop) (fwd: forwarding_map)
  : Lemma (requires forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      (live1 x <==> live2 x))
    (ensures update_live_pointers major live1 fwd == update_live_pointers major live2 fwd)

/// At the idle live set (every non-free block), the live walk is today's walk.
val update_live_pointers_idle (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures update_live_pointers major (idle_live major) fwd == update_major_pointers major fwd)

/// ---------------------------------------------------------------------------
/// The idle instances
/// ---------------------------------------------------------------------------

val update_major_pointers_preserves_objects (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures objects zero_addr (update_major_pointers major fwd) == objects zero_addr major)

val update_major_pointers_preserves_wfh_part1 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures well_formed_heap_part1 (update_major_pointers major fwd))

val update_major_pointers_unfold (major: heap) (fwd: forwarding_map)
  : Lemma (update_major_pointers major fwd ==
           update_all_objects_aux major (objects zero_addr major) fwd 0)
