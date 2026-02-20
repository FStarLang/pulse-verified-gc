/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.SweepInv - Abstract Sweep Predicates
/// ---------------------------------------------------------------------------
///
/// Wraps Seq.mem and objects predicates into abstract propositions
/// for use in Pulse pure() clauses without quantifier explosion.

module Pulse.Spec.GC.SweepInv

open FStar.Seq
open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.HeapGraph

module U64 = FStar.UInt64

/// Abstract: object address is a member of the global objects list
/// Takes U64.t (not obj_addr) because Pulse f_address returns U64.t
val obj_in_objects (obj: U64.t) (g: heap) : prop

/// Abstract: free pointer validity — if it's a pointer, it's in objects
val fp_valid (fp: U64.t) (g: heap) : prop

/// Abstract: sweep postcondition — wfh preserved, objects preserved, fp valid
val sweep_post : heap -> heap -> U64.t -> prop

/// ---------------------------------------------------------------------------
/// Introduction lemmas
/// ---------------------------------------------------------------------------

val obj_in_objects_intro : (obj: obj_addr) -> (g: heap) ->
  Lemma (requires Seq.mem obj (objects 0UL g))
        (ensures obj_in_objects obj g)

val fp_valid_intro : (fp: obj_addr) -> (g: heap) ->
  Lemma (requires Seq.mem fp (objects 0UL g))
        (ensures fp_valid fp g)

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
                 Seq.mem (obj <: obj_addr) (objects 0UL g))

val fp_valid_elim : (fp: U64.t) -> (g: heap) ->
  Lemma (requires fp_valid fp g)
        (ensures is_pointer_field fp ==>
                  (U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                   U64.v fp % U64.v mword == 0 /\
                   Seq.mem (fp <: obj_addr) (objects 0UL g)))

/// ---------------------------------------------------------------------------
/// Sweep postcondition: introduction and elimination
/// ---------------------------------------------------------------------------

val sweep_post_intro : (g_pre: heap) -> (g_post: heap) -> (new_fp: U64.t) ->
  Lemma (requires well_formed_heap g_post /\
                  objects 0UL g_post == objects 0UL g_pre /\
                  fp_valid new_fp g_post)
        (ensures sweep_post g_pre g_post new_fp)

val sweep_post_elim_wfh : (g_pre: heap) -> (g_post: heap) -> (new_fp: U64.t) ->
  Lemma (requires sweep_post g_pre g_post new_fp)
        (ensures well_formed_heap g_post)

val sweep_post_elim_objects : (g_pre: heap) -> (g_post: heap) -> (new_fp: U64.t) ->
  Lemma (requires sweep_post g_pre g_post new_fp)
        (ensures objects 0UL g_post == objects 0UL g_pre)

val sweep_post_elim_fp : (g_pre: heap) -> (g_post: heap) -> (new_fp: U64.t) ->
  Lemma (requires sweep_post g_pre g_post new_fp)
        (ensures fp_valid new_fp g_post)

/// ---------------------------------------------------------------------------
/// Preservation: sweep_post transfers fp_valid across equal objects lists
/// ---------------------------------------------------------------------------

val fp_valid_transfer : (fp: U64.t) -> (g1: heap) -> (g2: heap) ->
  Lemma (requires fp_valid fp g1 /\ objects 0UL g2 == objects 0UL g1)
        (ensures fp_valid fp g2)

val obj_in_objects_transfer : (obj: U64.t) -> (g1: heap) -> (g2: heap) ->
  Lemma (requires obj_in_objects obj g1 /\ objects 0UL g2 == objects 0UL g1)
        (ensures obj_in_objects obj g2)

/// Initial loop invariant: when objects from 0 is non-empty and 8 < heap_size,
/// the head object (at address 8) is in the objects list
val obj_in_objects_head : (g: heap) ->
  Lemma (requires Seq.length (objects 0UL g) > 0 /\ heap_size > 8)
        (ensures obj_in_objects (U64.uint_to_t 8) g)

/// ---------------------------------------------------------------------------
/// Heap density: walk continues at every interior position
/// ---------------------------------------------------------------------------

/// Abstract: the objects walk never stops early due to oversized wosize.
/// At every walk position where objects > 0, if the next position has room
/// for a header (next + 8 < heap_size), the walk continues there and
/// the head object is in the global objects list.
val heap_objects_dense : heap -> prop

/// Step lemma: density + objects at start > 0 + next has room → objects at next > 0
val objects_dense_step : (start: hp_addr) -> (g: heap) ->
  Lemma (requires heap_objects_dense g /\ Seq.length (objects start g) > 0)
        (ensures (let wz = getWosize (read_word g start) in
                  let next = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
                  next + 8 < heap_size ==>
                  Seq.length (objects (U64.uint_to_t next) g) > 0))

/// From density + non-empty objects at next, derive obj_in_objects for the head
val objects_dense_obj_in : (start: hp_addr) -> (g: heap) ->
  Lemma (requires heap_objects_dense g /\ Seq.length (objects start g) > 0)
        (ensures (let wz = getWosize (read_word g start) in
                  let next = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
                  next + 8 < heap_size ==>
                  obj_in_objects (U64.uint_to_t (next + 8)) g))

/// Transfer: density transfers when objects lists and all read_word values are equal.
/// This holds when only color bits change (mark phase), since objects and getWosize
/// are determined by the same header words.
val heap_objects_dense_transfer : (g1: heap) -> (g2: heap) ->
  Lemma (requires heap_objects_dense g1 /\
                  objects 0UL g2 == objects 0UL g1 /\
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
                  Seq.mem (obj_address h) (objects 0UL g))
        (ensures Seq.length (objects h g) > 0)

/// ---------------------------------------------------------------------------
/// Header preservation across sweep operations
/// ---------------------------------------------------------------------------

/// Abstract: all words at positions >= start are unchanged between two heaps.
/// Uses nat for start to avoid U64.uint_to_t overflow issues in Pulse postconditions.
val headers_preserved_from : nat -> heap -> heap -> prop

/// Reflexivity: same heap trivially preserves all words
val headers_preserved_from_refl : (start: nat) -> (g: heap) ->
  Lemma (ensures headers_preserved_from start g g)

/// Elimination: extract a specific read_word equality
val headers_preserved_from_elim : (start: nat) -> (pos: hp_addr) -> (g_cur: heap) -> (g_init: heap) ->
  Lemma (requires headers_preserved_from start g_cur g_init /\ U64.v pos >= start)
        (ensures read_word g_cur pos == read_word g_init pos)

/// Transitivity with weakening: chain two preservation facts
val headers_preserved_from_trans : (start1: nat) -> (start2: nat) ->
  (g1: heap) -> (g2: heap) -> (g3: heap) ->
  Lemma (requires headers_preserved_from start1 g2 g1 /\
                  headers_preserved_from start2 g3 g2 /\
                  start2 >= start1)
        (ensures headers_preserved_from start2 g3 g1)

/// After a write at addr with addr + mword <= start, all words from start onward
/// are preserved. Used to prove sweep_object preserves headers at the next position.
val headers_preserved_from_write : (start: nat) -> (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (requires U64.v addr + U64.v mword <= start)
        (ensures headers_preserved_from start (write_word g addr v) g)

/// ---------------------------------------------------------------------------
/// Whiteness tracking: all objects before a position are white
/// ---------------------------------------------------------------------------

/// Headers preserved before a limit (positions < limit unchanged from g_init)
val headers_preserved_before : nat -> heap -> heap -> prop

/// Reflexivity
val headers_preserved_before_refl : (limit: nat) -> (g: heap) ->
  Lemma (ensures headers_preserved_before limit g g)

/// Write at position >= limit preserves headers before limit
val headers_preserved_before_write : (limit: nat) -> (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (requires U64.v addr >= limit)
        (ensures headers_preserved_before limit (write_word g addr v) g)

/// Transitivity
val headers_preserved_before_trans : (limit: nat) -> (g1: heap) -> (g2: heap) -> (g3: heap) ->
  Lemma (requires headers_preserved_before limit g2 g1 /\ headers_preserved_before limit g3 g2)
        (ensures headers_preserved_before limit g3 g1)

/// All objects with header position < pos are white or blue in the given heap
val objects_white_before : nat -> heap -> prop

/// Vacuously true at the start (no objects before position 0)
val objects_white_before_zero : (g: heap) ->
  Lemma (ensures objects_white_before 0 g)

/// Step: extend swept region from h_addr to h_addr + (wz+1)*8
/// Requires:
/// - All objects before h_addr are white or blue in g_pre
/// - Objects list is preserved
/// - Heap is well-formed
/// - Current object at h_addr is white or blue in g_post
/// - Headers before h_addr are preserved from g_pre to g_post
/// - Wosize at h_addr is the same in g_post and g_pre (color-only change)
/// - obj_address h_addr is in the objects list
val objects_white_before_step : (h_addr: hp_addr) -> (g_pre: heap) -> (g_post: heap) ->
  Lemma (requires
    objects_white_before (U64.v h_addr) g_pre /\
    objects 0UL g_post == objects 0UL g_pre /\
    well_formed_heap g_post /\
    U64.v h_addr + 8 < heap_size /\
    (is_white (obj_address h_addr) g_post \/ is_blue (obj_address h_addr) g_post) /\
    headers_preserved_before (U64.v h_addr) g_post g_pre /\
    getWosize (read_word g_post h_addr) == getWosize (read_word g_pre h_addr) /\
    Seq.mem (obj_address h_addr) (objects 0UL g_post))
  (ensures objects_white_before 
    (U64.v h_addr + FStar.Mul.((U64.v (getWosize (read_word g_pre h_addr)) + 1) * 8)) g_post)

/// Final: when pos covers all of heap_size, all objects are white or blue
val objects_white_before_all : (pos: nat) -> (g: heap) ->
  Lemma (requires objects_white_before pos g /\ pos >= heap_size)
        (ensures forall (x: obj_addr). Seq.mem x (objects 0UL g) ==> (is_white x g \/ is_blue x g))

/// Exit variant: when pos + 8 >= heap_size, all objects are white or blue.
/// At loop exit we have pos + mword >= heap_size, meaning no more objects can start at pos.
/// All objects have hd_address(x) + 8 < heap_size (from hd_address_bounds), so hd_address(x) < pos.
val objects_white_before_exit : (pos: nat) -> (g: heap) ->
  Lemma (requires objects_white_before pos g /\ pos + 8 >= heap_size)
        (ensures forall (x: obj_addr). Seq.mem x (objects 0UL g) ==> (is_white x g \/ is_blue x g))

/// ---------------------------------------------------------------------------
/// No Gray Objects
/// ---------------------------------------------------------------------------

/// Abstract: no gray objects in the heap
val no_gray_objects : heap -> prop

/// Derive per-object non-gray from headers preservation + global no-gray
/// Key insight: if headers at h_addr are preserved from g_init to g_cur,
/// then the color at h_addr is the same, so no-gray transfers.
val no_gray_at_preserved : (obj: obj_addr) -> (g_init: heap) -> (g_cur: heap) ->
  Lemma (requires no_gray_objects g_init /\
                  Seq.mem obj (objects 0UL g_init) /\
                  read_word g_cur (hd_address obj) == read_word g_init (hd_address obj))
        (ensures ~(is_gray obj g_cur))

/// Eliminate: extract per-object non-gray from no_gray_objects
val no_gray_elim : (obj: obj_addr) -> (g: heap) ->
  Lemma (requires no_gray_objects g /\ Seq.mem obj (objects 0UL g))
        (ensures ~(is_gray obj g))

/// No gray from empty-stack mark_inv: all gray objects are on (empty) stack
val no_gray_intro : (g: heap) ->
  Lemma (requires forall (obj: obj_addr). Seq.mem obj (objects 0UL g) ==> ~(is_gray obj g))
        (ensures no_gray_objects g)
