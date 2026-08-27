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

/// Instantiate `Mark.no_pointer_to_blue` at a concrete field.
val field_pointer_no_blue_from_no_pointer_to_blue
  (g: heap) (src dst: obj_addr) (j: nat)
  : Lemma
    (requires well_formed_heap_part1 g /\
              Mark.no_pointer_to_blue g /\
              Seq.mem src (objects zero_addr g) /\
              ~(is_blue src g) /\
              fields_constrained g src /\
              j < U64.v (wosize_of_object src g) /\
              U64.v src + j * U64.v mword + U64.v mword <= heap_size /\
              (U64.v src + j * U64.v mword) % U64.v mword == 0 /\
              is_pointer_to
                (read_word g (U64.uint_to_t (U64.v src + j * U64.v mword)))
                dst)
    (ensures ~(is_blue (resolve_object dst g) g))

/// A concrete pointer field in a well-formed heap targets an object --- after
/// resolution, since the field may hold an interior pointer to an infix object
/// embedded in a closure.  The infix well-formedness of the raw target is
/// exposed too, so callers can reach the enclosing closure.
val field_pointer_target_in_objects_nat
  (g: heap) (src dst: obj_addr) (j: nat)
  : Lemma
    (requires well_formed_heap g /\
              Seq.mem src (objects zero_addr g) /\
              fields_constrained g src /\
              j < U64.v (wosize_of_object src g) /\
              U64.v src + j * U64.v mword + U64.v mword <= heap_size /\
              (U64.v src + j * U64.v mword) % U64.v mword == 0 /\
              is_pointer_to
                (read_word g (U64.uint_to_t (U64.v src + j * U64.v mword)))
                dst)
    (ensures Seq.mem (resolve_object dst g) (objects zero_addr g) /\
             infix_addr_wf g (objects zero_addr g) dst)

