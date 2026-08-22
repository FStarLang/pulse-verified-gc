/// ---------------------------------------------------------------------------
/// GC.Spec.SweepInv - Abstract Sweep Predicates
/// ---------------------------------------------------------------------------
///
/// Wraps Seq.mem and objects predicates into abstract propositions
/// for use in Pulse pure() clauses without quantifier explosion.

module GC.Spec.SweepInv

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.HeapGraph

module U64 = FStar.UInt64

/// Abstract: object address is a member of the global objects list
/// Takes U64.t (not obj_addr) because Pulse f_address returns U64.t
val obj_in_objects (obj: U64.t) (g: heap) : prop

/// Abstract: free pointer validity — if it's a pointer, it's in objects
val fp_valid (fp: U64.t) (g: heap) : prop
/// ---------------------------------------------------------------------------
/// Introduction lemmas
/// ---------------------------------------------------------------------------

val obj_in_objects_intro : (obj: obj_addr) -> (g: heap) ->
  Lemma (requires Seq.mem obj (objects zero_addr g))
        (ensures obj_in_objects obj g)

/// fp_valid holds trivially when fp is not a pointer field (e.g., 0UL)
val fp_valid_not_pointer : (fp: U64.t) -> (g: heap) ->
  Lemma (requires not (is_pointer_field fp))
        (ensures fp_valid fp g)

/// fp_valid from obj_in_objects
val fp_valid_from_obj : (fp: U64.t) -> (g: heap) ->
  Lemma (requires obj_in_objects fp g)
        (ensures fp_valid fp g)

/// ---------------------------------------------------------------------------
/// Elimination lemmas (non-quantified for Pulse use)
/// ---------------------------------------------------------------------------

val obj_in_objects_elim : (obj: U64.t) -> (g: heap) ->
  Lemma (requires obj_in_objects obj g)
        (ensures U64.v obj >= U64.v mword /\ U64.v obj < heap_size /\
                 U64.v obj % U64.v mword == 0 /\
                 Seq.mem (obj <: obj_addr) (objects zero_addr g))

val fp_valid_elim : (fp: U64.t) -> (g: heap) ->
  Lemma (requires fp_valid fp g)
        (ensures is_pointer_field fp ==>
                  (U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                   U64.v fp % U64.v mword == 0 /\
                   Seq.mem (fp <: obj_addr) (objects zero_addr g)))

/// ---------------------------------------------------------------------------
/// Sweep postcondition: introduction and elimination
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// Preservation: sweep_post transfers fp_valid across equal objects lists
/// ---------------------------------------------------------------------------

val fp_valid_transfer : (fp: U64.t) -> (g1: heap) -> (g2: heap) ->
  Lemma (requires fp_valid fp g1 /\ objects zero_addr g2 == objects zero_addr g1)
        (ensures fp_valid fp g2)

/// Initial loop invariant: when objects from zero_addr is non-empty,
/// the head object (at f_address zero_addr) is in the objects list
val obj_in_objects_head : (g: heap) ->
  Lemma (requires Seq.length (objects zero_addr g) > 0)
        (ensures obj_in_objects (f_address zero_addr) g)

/// ---------------------------------------------------------------------------
/// Heap density: walk continues at every interior position
/// ---------------------------------------------------------------------------

/// Abstract: the objects walk never stops early due to oversized wosize.
/// At every walk position where objects > 0, if the next position has room
/// for a header (next + 8 < heap_size), the walk continues there and
/// the head object is in the global objects list.
val heap_objects_dense : heap -> prop

/// Introduction lemma for heap_objects_dense: prove it from the universal property
val heap_objects_dense_intro : (g: heap) ->
  Lemma (requires (forall (start: hp_addr).
                    U64.v start + 8 < heap_size ==>
                    Seq.mem (f_address start) (objects zero_addr g) ==>
                    Seq.length (objects start g) > 0 ==>
                    (let wz = getWosize (read_word g start) in
                     let next = U64.v start + ((U64.v wz + 1) * 8) in
                     next + 8 < heap_size ==>
                     Seq.length (objects (U64.uint_to_t next) g) > 0 /\
                     Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g))))
        (ensures heap_objects_dense g)

/// Step lemma: density + object at start in global list + objects at start > 0
/// + next has room → objects at next > 0
val objects_dense_step : (start: hp_addr) -> (g: heap) ->
  Lemma (requires heap_objects_dense g /\
                  U64.v start + 8 < heap_size /\
                  Seq.mem (f_address start) (objects zero_addr g) /\
                  Seq.length (objects start g) > 0)
        (ensures (let wz = getWosize (read_word g start) in
                  let next = U64.v start + ((U64.v wz + 1) * 8) in
                  next + 8 < heap_size ==>
                  Seq.length (objects (U64.uint_to_t next) g) > 0))

/// From density + non-empty objects at next, derive obj_in_objects for the head
val objects_dense_obj_in : (start: hp_addr) -> (g: heap) ->
  Lemma (requires heap_objects_dense g /\
                  U64.v start + 8 < heap_size /\
                  Seq.mem (f_address start) (objects zero_addr g) /\
                  Seq.length (objects start g) > 0)
        (ensures (let wz = getWosize (read_word g start) in
                  let next = U64.v start + ((U64.v wz + 1) * 8) in
                  next + 8 < heap_size ==>
                  obj_in_objects (U64.uint_to_t (next + 8)) g))

/// Transfer: density transfers when objects lists and all read_word values are equal.
/// This holds when only color bits change (mark phase), since objects and getWosize
/// are determined by the same header words.
val heap_objects_dense_transfer : (g1: heap) -> (g2: heap) ->
  Lemma (requires heap_objects_dense g1 /\
                  objects zero_addr g2 == objects zero_addr g1 /\
                  (forall (p: hp_addr). getWosize (read_word g2 p) == getWosize (read_word g1 p)))
        (ensures heap_objects_dense g2)

/// Color change preserves density: set_object_color only modifies color bits,
/// leaving getWosize unchanged at every position.
val color_change_preserves_density : (obj: obj_addr) -> (g: heap) -> (c: color) ->
  Lemma (requires heap_objects_dense g)
        (ensures heap_objects_dense (set_object_color obj g c))

/// ---------------------------------------------------------------------------
/// Walk reconstruction: membership in global list implies local walk is non-empty
/// ---------------------------------------------------------------------------

/// Key bridge: if an object address is in the global walk and the heap is well-formed,
/// then the local walk from its header position is non-empty.
/// This avoids needing suffix preservation — we only need global membership.
val member_implies_objects_nonempty : (h: hp_addr{U64.v h + 8 < heap_size}) -> (g: heap) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem (f_address h) (objects zero_addr g))
        (ensures Seq.length (objects h g) > 0)

/// ---------------------------------------------------------------------------
/// Header preservation across sweep operations
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// Whiteness tracking: all objects before a position are white
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// No Gray Objects
/// ---------------------------------------------------------------------------

/// Abstract: no gray objects in the heap
val no_gray_objects : heap -> prop
/// Eliminate: extract per-object non-gray from no_gray_objects
val no_gray_elim : (obj: obj_addr) -> (g: heap) ->
  Lemma (requires no_gray_objects g /\ Seq.mem obj (objects zero_addr g))
        (ensures ~(is_gray obj g))

/// No gray from empty-stack mark_inv: all gray objects are on (empty) stack
val no_gray_intro : (g: heap) ->
  Lemma (requires forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==> ~(is_gray obj g))
        (ensures no_gray_objects g)
