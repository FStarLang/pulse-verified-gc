/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation.Fields -- promoted-field correspondence
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation.Fields

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// If Cheney forwards a normal minor object `x`, every copied body field within
/// the original minor wosize is the corresponding minor-heap field.  The lemma
/// deliberately excludes infix forwarding targets: those are interior pointers
/// into an already-promoted parent rather than standalone copied objects.
val cheney_promote_fwd_target_fields_match
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x: U64.t) (j: nat)
  : Lemma
    (requires well_formed_heap major /\
              AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
              chain_objects_blue major fp /\
              minor_wf minor /\
              minor_infix_wf minor /\
              (let prom = cheney_promote minor major fp roots in
               prom.fwd_map x <> 0UL /\
               Seq.mem x (minor_objects minor) /\
               is_val_addr (prom.fwd_map x) /\
               is_infix (prom.fwd_map x) prom.major_final = false /\
               j < minor_wosize minor x /\
               U64.v (prom.fwd_map x) + j * 8 + 8 <= heap_size /\
               (U64.v (prom.fwd_map x) + j * 8) % 8 == 0))
    (ensures
      (let prom = cheney_promote minor major fp roots in
        read_word prom.major_final
          (U64.uint_to_t (U64.v (prom.fwd_map x) + j * 8))
        == minor_read_field minor x j))

/// Allocator rounding can leave one extra body word in a promoted block.
/// That word is zeroed during promotion and remains non-pointer through the
/// rest of Cheney's BFS.
val cheney_promote_fwd_target_extra_field_not_pointer
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x: U64.t) (j: nat)
  : Lemma
    (requires well_formed_heap major /\
              AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
              chain_objects_blue major fp /\
              minor_wf minor /\
              minor_infix_wf minor /\
              (let prom = cheney_promote minor major fp roots in
               prom.fwd_map x <> 0UL /\
               Seq.mem x (minor_objects minor) /\
               is_val_addr (prom.fwd_map x) /\
               is_infix (prom.fwd_map x) prom.major_final = false /\
               j >= minor_wosize minor x /\
               j < U64.v (wosize_of_object (prom.fwd_map x <: obj_addr)
                                             prom.major_final) /\
               U64.v (prom.fwd_map x) + j * 8 + 8 <= heap_size /\
               (U64.v (prom.fwd_map x) + j * 8) % 8 == 0))
    (ensures
      (let prom = cheney_promote minor major fp roots in
       let field = read_word prom.major_final
          (U64.uint_to_t (U64.v (prom.fwd_map x) + j * 8)) in
       field == 0UL /\ ~(is_pointer_field field)))
