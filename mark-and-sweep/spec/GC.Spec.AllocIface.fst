/// ---------------------------------------------------------------------------
/// GC.Spec.AllocIface - the allocator interface, for any allocator and any collector
/// ---------------------------------------------------------------------------
///
/// An allocator is plugged into a collector through this interface alone.
/// It does not see the collector; it sees only the collector's **phase**,
/// and, while sweeping, which memory the sweep has yet to visit:
///
///   | phase      | the collector is ...                  | new object                      |
///   |------------|---------------------------------------|---------------------------------|
///   | `Idle`     | not collecting                        | white                           |
///   | `Marking`  | marking (incrementally)               | black                           |
///   | `Sweeping` | sweeping (incrementally)              | black in unswept memory, white  |
///   |            |                                       | in swept memory                 |
///
/// This is `colour_at` (plan §20.2), main's `Phase.allocation_color` with
/// "at or above the cursor" read as "unswept": a new object is black while
/// the collector marks, so the mark keeps it; black in memory the sweep has
/// yet to visit, so the sweep keeps it; white otherwise.
///
/// An allocator is a record `allocator`: its state, its invariant per phase,
/// its allocation function per phase, and two predicates on words:
///   - `unswept`: memory the sweep has yet to visit, which decides the
///     colour;
///   - `pending`: memory the allocator must not change, the sweep's
///     remaining work.
/// Main's first fit allocates above its cursor (unswept) but never into a
/// block the sweep will free (pending), so the two differ there; for the page
/// allocator they are the same predicate.
///
/// `allocator_ok a` is what it guarantees (`alloc_post`); `phase_ok a` is
/// how its invariant moves with the collector's phase.  The page allocator
/// is one instance (`GC.Spec.Pages.Allocator.pages_allocator`).
///
/// As OCaml's `caml_alloc_shr`, an allocator writes the new object's header
/// and leaves its fields; the caller writes every field before the heap is
/// used again (`fields_written_with`).  What the caller may store depends on
/// what the collector counts as free (`free_def`): `allocator_ok_with a free`
/// takes it per phase and state, and `allocator_ok` is the stop-the-world
/// instance, where free means blue.

module GC.Spec.AllocIface

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header

module U64 = FStar.UInt64
module Seq = FStar.Seq

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Phases and the colour of a new object
/// ---------------------------------------------------------------------------

type phase =
  | Idle
  | Marking
  | Sweeping

/// The colour by the phase alone: what an allocator that uses only swept
/// memory gives, since there `colour_at` is this (the page allocator's
/// `alloc` paints with it).
let new_colour (ph: phase) : color =
  match ph with
  | Marking -> Black
  | Idle | Sweeping -> White

/// ---------------------------------------------------------------------------
/// What an allocation must do
/// ---------------------------------------------------------------------------

/// `x` is an object of `g` that is not free.
let live (g: heap) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)

/// Every object that is not free keeps its place, header and fields.
let others_unchanged (g g': heap) : prop =
  forall (x: obj_addr).
    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) ==>
    Seq.mem x (objects zero_addr g') /\
    read_word g' (hd_address x) == read_word g (hd_address x) /\
    (forall (b: hp_addr). U64.v x <= U64.v b /\ U64.v b < U64.v x + U64.v (wosize_of_object x g) * 8 ==>
       read_word g' b == read_word g b)

/// A value the caller may store in a field: not a pointer, or a pointer that
/// resolves to an object that is not free.
let field_ok (g: heap) (v: U64.t) : prop =
  is_pointer v ==>
  Seq.mem (resolve_object (v <: obj_addr) g) (objects zero_addr g) /\
  infix_addr_wf g (objects zero_addr g) (v <: obj_addr) /\
  ~(is_blue (resolve_object (v <: obj_addr) g) g)

/// The same, for any definition of free: not a pointer, or a pointer that
/// resolves to a block that is not free, through a valid interior pointer if
/// it is one.  `field_ok` is the instance at `free_stw` (`field_ok_stw`).
let field_ok_with (free: free_def) (g: heap) (v: U64.t) : prop =
  is_pointer v ==>
  in_use free g (resolve_object (v <: obj_addr) g) /\
  infix_addr_wf g (objects zero_addr g) (v <: obj_addr)

let field_ok_stw (g: heap) (v: U64.t)
  : Lemma (field_ok_with free_stw g v <==> field_ok g v)
  = ()

/// `g''` is `g'` with the fields of `x` written with values the caller may
/// store.
let fields_written (g' g'': heap) (x: obj_addr) : prop =
  (forall (a: hp_addr).
     U64.v a < U64.v x \/ U64.v a >= U64.v x + U64.v (wosize_of_object x g') * 8 ==>
     read_word g'' a == read_word g' a) /\
  (forall (a: hp_addr).
     U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g') * 8 ==>
     field_ok g'' (read_word g'' a))

/// The same, for any definition of free.
let fields_written_with (free: free_def) (g' g'': heap) (x: obj_addr) : prop =
  (forall (a: hp_addr).
     U64.v a < U64.v x \/ U64.v a >= U64.v x + U64.v (wosize_of_object x g') * 8 ==>
     read_word g'' a == read_word g' a) /\
  (forall (a: hp_addr).
     U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g') * 8 ==>
     field_ok_with free g'' (read_word g'' a))

let fields_written_stw (g' g'': heap) (x: obj_addr)
  : Lemma (fields_written_with free_stw g' g'' x <==> fields_written g' g'' x)
  = ()

/// ---------------------------------------------------------------------------
/// An allocator
/// ---------------------------------------------------------------------------

noeq type allocator = {
  (* the allocator's own state *)
  ast: Type0;
  (* what it needs of the heap and its state, and keeps, in each phase *)
  inv: phase -> heap -> ast -> prop;
  (* allocate an object of wosize `wz`; 0 when there is no room *)
  alloc: phase -> heap -> ast -> nat -> GTot (heap & ast & U64.t);
  (* memory the sweep has yet to visit: decides the new object's colour *)
  unswept: ast -> hp_addr -> prop;
  (* the words it must not touch: the sweep's remaining work *)
  pending: ast -> hp_addr -> prop;
}

/// **The colour of a new object** (plan §20.2): black while marking, and
/// while sweeping when its header lies in memory the sweep has yet to visit;
/// white otherwise.
let colour_at (a: allocator) (s: a.ast) (ph: phase) (x: obj_addr) : GTot color =
  match ph with
  | Marking -> Black
  | Sweeping ->
    if FStar.IndefiniteDescription.strong_excluded_middle (a.unswept s (hd_address x)) then Black
    else White
  | Idle -> White

/// What one allocation guarantees, when the caller may store the values
/// `field_ok_with free`.  On success the new object:
///   - is an object of the heap, of wosize `wz`, of colour `colour_at`, and
///     was not an object that is not free;
///   - leaves every other object that is not free as it was, and every
///     pending word;
///   - leaves the invariant to the caller: every heap the caller makes by
///     writing the fields satisfies it.
/// On failure nothing changes.
let alloc_post_with (free: free_def) (a: allocator) (ph: phase) (g: heap) (s: a.ast) (wz: nat)
                    (g': heap) (s': a.ast) (obj: U64.t) : prop =
  (obj == 0UL ==> g' == g /\ s' == s) /\
  (obj =!= 0UL ==>
     U64.v obj >= 8 /\ U64.v obj < heap_size /\ U64.v obj % 8 == 0 /\
     (let x : obj_addr = obj in
      Seq.mem x (objects zero_addr g') /\
      U64.v (wosize_of_object x g') == wz /\
      color_of_object x g' == colour_at a s ph x /\
      ~(live g x) /\
      (forall (g'': heap). fields_written_with free g' g'' x ==> a.inv ph g'' s')) /\
     others_unchanged g g' /\
     (forall (b: hp_addr). a.pending s b ==> read_word g' b == read_word g b))

/// The stop-the-world instance: the caller stores `field_ok` values.
let alloc_post (a: allocator) (ph: phase) (g: heap) (s: a.ast) (wz: nat)
               (g': heap) (s': a.ast) (obj: U64.t) : prop =
  alloc_post_with free_stw a ph g s wz g' s' obj

/// Every allocation, in every phase, meets `alloc_post_with`, with what the
/// collector counts as free in that phase and state.
let allocator_ok_with (a: allocator) (free: phase -> a.ast -> free_def) : prop =
  forall (ph: phase) (g: heap) (s: a.ast) (wz: nat).
    a.inv ph g s ==>
    (let (g', s', obj) = a.alloc ph g s wz in alloc_post_with (free ph s) a ph g s wz g' s' obj)

let allocator_ok (a: allocator) : prop =
  forall (ph: phase) (g: heap) (s: a.ast) (wz: nat).
    a.inv ph g s ==>
    (let (g', s', obj) = a.alloc ph g s wz in alloc_post a ph g s wz g' s' obj)

/// `allocator_ok` is `allocator_ok_with` at `free_stw` in every phase.
let allocator_ok_stw (a: allocator)
  : Lemma (allocator_ok a <==> allocator_ok_with a (fun _ _ -> free_stw))
  = ()

/// The first version's statement (stage 4 item 0): the colour from the phase
/// alone (`new_colour`), and the frame on `unswept`.  Kept to show that the
/// second version loses nothing for an allocator that never allocates into
/// unswept memory (`GC.Spec.Pages.Allocator.alloc_post_new_old`).
let alloc_post_v1 (a: allocator) (ph: phase) (g: heap) (s: a.ast) (wz: nat)
                  (g': heap) (s': a.ast) (obj: U64.t) : prop =
  (obj == 0UL ==> g' == g /\ s' == s) /\
  (obj =!= 0UL ==>
     U64.v obj >= 8 /\ U64.v obj < heap_size /\ U64.v obj % 8 == 0 /\
     (let x : obj_addr = obj in
      Seq.mem x (objects zero_addr g') /\
      U64.v (wosize_of_object x g') == wz /\
      color_of_object x g' == new_colour ph /\
      ~(live g x) /\
      (forall (g'': heap). fields_written g' g'' x ==> a.inv ph g'' s')) /\
     others_unchanged g g' /\
     (forall (b: hp_addr). a.unswept s b ==> read_word g' b == read_word g b))

/// How the invariant follows the collector:
///   - starting to mark keeps it;
///   - marking recolours objects that are not free, never to blue: that
///     keeps it.
/// The collector moves from `Marking` to `Sweeping` and from `Sweeping` to
/// `Idle` with its own sweep, so those steps are the collector's proof
/// obligations, stated with the sweep (`GC.Spec.Pages.Allocator`).
let phase_ok (a: allocator) : prop =
  (forall (g: heap) (s: a.ast). a.inv Idle g s ==> a.inv Marking g s) /\
  (forall (g: heap) (s: a.ast) (x: obj_addr) (c: color).
     a.inv Marking g s /\ live g x /\ c <> Blue ==> a.inv Marking (set_object_color x g c) s)
