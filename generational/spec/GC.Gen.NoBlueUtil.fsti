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
    (requires blocks_fit g /\
              Seq.mem src (objects zero_addr g) /\
              j < U64.v (wosize_of_object src g) /\
              U64.v src + j * U64.v mword + U64.v mword <= heap_size /\
              (U64.v src + j * U64.v mword) % U64.v mword == 0 /\
              is_pointer_to
                (read_word g (U64.uint_to_t (U64.v src + j * U64.v mword)))
                dst)
    (ensures points_to g src dst)

/// The pointer clauses at a field: a pointer field of a non-free, scannable
/// block targets a non-free block.
val field_pointer_target_not_free_nat
  (free: free_def) (g: heap) (src dst: obj_addr) (j: nat)
  : Lemma
    (requires well_formed_heap_with free g /\
              in_use free g src /\ Seq.mem src (objects zero_addr g) /\
              ~(is_no_scan src g) /\
              j < U64.v (wosize_of_object src g) /\
              U64.v src + j * U64.v mword + U64.v mword <= heap_size /\
              (U64.v src + j * U64.v mword) % U64.v mword == 0 /\
              is_pointer_to
                (read_word g (U64.uint_to_t (U64.v src + j * U64.v mword)))
                dst)
    (ensures in_use free g (resolve_object dst g) /\
             infix_addr_wf g (objects zero_addr g) dst)
