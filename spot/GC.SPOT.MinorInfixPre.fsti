/// ---------------------------------------------------------------------------
/// GC.SPOT.MinorInfixPre — a concrete major-to-nursery interior pointer, and
/// the proof that `gen_gc` accepts it
/// ---------------------------------------------------------------------------
///
/// The heap:
///
///   major   `c` at `zero_addr + 8`, two fields; field 1 holds `24`
///           (`GC.SPOT.ConcreteMajorInfix`), plus a blue free block
///   nursery  a `CLOSUREREC` pair --- one closure at byte 8 with an infix
///           header at byte 16 and the second entry point at byte 24
///           (`GC.SPOT.MinorInfixHeap`)
///
/// So `c`'s field 1 points at byte 24 of the nursery, which is *not* an object:
/// it is the second entry point of a mutually recursive closure group.  This is
/// the shape stock OCaml produces whenever `let rec f x = ... and g y = ...` is
/// small enough to be allocated young and one of the two closures is stored
/// into an older block.
///
/// Before Phase H this heap was rejected out of hand:
/// `GC.Gen.HeapInvariant.collection_heap_shape` carried a clause forbidding a
/// major field from holding an interior nursery pointer.  `spot_mi_was_forbidden`
/// below reproduces that clause and derives `False` from it, which is what makes
/// this SPOT non-vacuous: it is not merely *a* heap the collector accepts, it is
/// exactly a heap the collector used to reject.

module GC.SPOT.MinorInfixPre

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module MinorFwd = GC.Gen.MinorCollectForwarding
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module GenImpl = GC.Gen.Impl
module Preconditions = GC.SPOT.Preconditions
module Layout = GC.SPOT.Layout
module Major = GC.SPOT.ConcreteMajorInfix
module Nursery = GC.SPOT.MinorInfixHeap
module MinorInfix = GC.SPOT.MinorInfix

/// The nursery, re-exported under a shorter name.
let spot_mi_minor : minor_state = Nursery.spot_infix_nursery

/// Roots: the major object, and the *interior* nursery pointer.
///
/// The interior pointer has to be a root: `remembered_targets_in_roots` demands
/// that every minor value reachable through the remembered set also appear in
/// the root set, and `c`'s field 1 is exactly such a value.  So this SPOT
/// exercises interior roots as well as interior fields.
val spot_mi_roots : (r:unit{Major.spot_major_room}) ->
  Tot (s:seq U64.t{Seq.length s == 2})

val spot_mi_roots_mem : r:unit{Major.spot_major_room} ->
  Lemma (ensures Seq.mem (Major.spot_c r <: U64.t) (spot_mi_roots r) /\
                 Seq.mem (Layout.b_minor <: U64.t) (spot_mi_roots r))

/// The remembered set: one slot, the address of `c`'s field 1.
val spot_mi_slots : (r:unit{Major.spot_major_room}) ->
  Tot (s:seq U64.t{Seq.length s == 1})

val spot_mi_slots_index : r:unit{Major.spot_major_room} ->
  Lemma (ensures Seq.index (spot_mi_slots r) 0 == Major.spot_c_field1 r)

val spot_mi_fwd_array : seq U64.t

/// ---------------------------------------------------------------------------
/// It really is an interior pointer
/// ---------------------------------------------------------------------------

/// The value in `c`'s field 1, read through the collector's own accessor, is an
/// infix address of the nursery whose enclosing closure is the object at byte 8.
val spot_mi_field_is_interior : r:unit{Major.spot_major_room} ->
  Lemma (ensures (
    let target =
      MinorInfix.stored_target (Major.spot_major_heap r) (Major.spot_c r)
                               Layout.c_to_a_field_index in
    U64.v (Major.spot_c r) + Layout.c_to_a_field_index * 8 + 8 <= heap_size /\
    target == (Layout.b_minor <: U64.t) /\
    is_infix_in_minor spot_mi_minor target /\
    ~(Seq.mem target (minor_objects spot_mi_minor)) /\
    infix_parent spot_mi_minor target == (Layout.a_minor <: U64.t) /\
    resolve_minor spot_mi_minor target == (Layout.a_minor <: U64.t)))

/// ---------------------------------------------------------------------------
/// The precondition
/// ---------------------------------------------------------------------------

/// The entry invariant, on the nose: exactly the predicate `gen_gc` requires of
/// the heap it is handed.
val spot_mi_collection_heap_shape : r:unit{Major.spot_major_room} ->
  Lemma (ensures GenInv.collection_heap_shape
                   spot_mi_minor (Major.spot_major_heap r) (Major.spot_major_fp r))

/// The interior nursery pointer is a legal root.  This is the Phase H.2 clause
/// under test: `roots_valid_for_minor_collection` sends every minor root through
/// `resolve_minor`, so an interior root is admitted and names its closure.
val spot_mi_roots_valid : r:unit{Major.spot_major_room} ->
  Lemma (ensures MinorFwd.roots_valid_for_minor_collection
                   spot_mi_minor (Major.spot_major_heap r) (spot_mi_roots r))

val spot_mi_minor_collect_full_pre : r:unit{Major.spot_major_room} ->
  Lemma (ensures Preconditions.minor_collect_full_pre
                   spot_mi_minor (Major.spot_major_heap r) (Major.spot_major_fp r)
                   (spot_mi_roots r) spot_mi_fwd_array (spot_mi_slots r) 1)

/// `gen_gc`'s full precondition, for any empty mark stack with room for the
/// two roots.
val spot_mi_gen_gc_pre : r:unit{Major.spot_major_room} -> cap:nat{cap >= 2} ->
  Lemma (ensures Preconditions.gen_gc_pre
                   spot_mi_minor (Major.spot_major_heap r) (Major.spot_major_fp r)
                   (spot_mi_roots r) spot_mi_fwd_array (spot_mi_slots r) 1
                   Seq.empty cap)

/// ---------------------------------------------------------------------------
/// Non-vacuity
/// ---------------------------------------------------------------------------

/// The heap above violates the clause Phase H deleted from
/// `collection_heap_shape`.  Together with `spot_mi_collection_heap_shape` this
/// is the statement that the relaxation is real and that this SPOT witnesses it:
/// the collector's entry invariant holds of a heap the *old* invariant excluded.
val spot_mi_was_forbidden : r:unit{Major.spot_major_room} ->
  Lemma (requires MinorInfix.deleted_major_minor_fields_no_infix_targets
                    spot_mi_minor (Major.spot_major_heap r))
        (ensures False)
