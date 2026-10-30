/// ---------------------------------------------------------------------------
/// GC.Gen.NoBlueUtil -- small field-level no-blue helpers
/// ---------------------------------------------------------------------------

module GC.Gen.NoBlueUtil

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module Mark = GC.Spec.Mark

/// A concrete field that points to `dst` witnesses `points_to`.
val field_pointer_points_to_nat
  (g: heap) (src dst: obj_addr) (j: nat)
  : Lemma
    (requires well_formed_heap_part1 g /\
              Seq.mem src (objects zero_addr g) /\
              j < U64.v (wosize_of_object src g) /\
              U64.v src + j * U64.v mword + U64.v mword <= heap_size /\
              (U64.v src + j * U64.v mword) % U64.v mword == 0 /\
              is_pointer_to
                (read_word g (U64.uint_to_t (U64.v src + j * U64.v mword)))
                dst)
    (ensures points_to g src dst)

/// The same, except the objects pending free: a pointer field of a not-freed
/// scannable object targets a not-freed object.
val field_pointer_target_not_freed_nat
  (g: heap) (pf: obj_addr -> prop) (src dst: obj_addr) (j: nat)
  : Lemma
    (requires well_formed_heap_except g pf /\
              not_freed g pf src /\
              fields_constrained g src /\
              j < U64.v (wosize_of_object src g) /\
              U64.v src + j * U64.v mword + U64.v mword <= heap_size /\
              (U64.v src + j * U64.v mword) % U64.v mword == 0 /\
              is_pointer_to
                (read_word g (U64.uint_to_t (U64.v src + j * U64.v mword)))
                dst)
    (ensures not_freed g pf (resolve_object dst g) /\
             infix_addr_wf g (objects zero_addr g) dst)
