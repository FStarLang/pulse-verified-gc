/// ---------------------------------------------------------------------------
/// GC.Spec.AllocIface - the allocator interface, for any allocator and any collector
/// ---------------------------------------------------------------------------
///
/// An allocator is plugged into a collector through this interface alone.
/// It does not see the collector; it sees only the collector's **phase**:
///
///   | phase      | the collector is ...                  | new object |
///   |------------|---------------------------------------|------------|
///   | `Idle`     | not collecting                        | white      |
///   | `Marking`  | marking (incrementally)               | black      |
///   | `Sweeping` | sweeping (incrementally)              | white      |
///
/// A new object is black while the collector marks, so the mark keeps it;
/// white otherwise.  While sweeping it is white because the allocator only
/// uses memory that is already swept (`unswept` below), so the sweep never
/// sees it.  This is the rule of plan §7.2, and it differs from
/// `akhil/incremental-sweep`'s `allocation_color (Sweeping c)`, which
/// allocates in front of the cursor too and makes those objects black.
///
/// An allocator is a record `allocator`: its state, its invariant per phase,
/// its allocation function per phase, and the memory it must not touch.
/// `allocator_ok a` is what it guarantees (`alloc_post`); `phase_ok a` is
/// how its invariant moves with the collector's phase.  The page allocator
/// is one instance (`GC.Spec.Pages.Allocator.pages_allocator`).
///
/// As OCaml's `caml_alloc_shr`, an allocator writes the new object's header
/// and leaves its fields; the caller writes every field before the heap is
/// used again (`fields_written`).

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

/// `g''` is `g'` with the fields of `x` written with values the caller may
/// store.
let fields_written (g' g'': heap) (x: obj_addr) : prop =
  (forall (a: hp_addr).
     U64.v a < U64.v x \/ U64.v a >= U64.v x + U64.v (wosize_of_object x g') * 8 ==>
     read_word g'' a == read_word g' a) /\
  (forall (a: hp_addr).
     U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g') * 8 ==>
     field_ok g'' (read_word g'' a))

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
  (* the words it must not touch: memory the collector has not swept yet *)
  unswept: ast -> hp_addr -> prop;
}

/// What one allocation guarantees.  On success the new object:
///   - is an object of the heap, of wosize `wz`, of the phase's colour,
///     and was not an object that is not free;
///   - leaves every other object that is not free as it was, and every
///     word of memory that is not swept;
///   - leaves the invariant to the caller: every heap the caller makes by
///     writing the fields satisfies it.
/// On failure nothing changes.
let alloc_post (a: allocator) (ph: phase) (g: heap) (s: a.ast) (wz: nat)
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

let allocator_ok (a: allocator) : prop =
  forall (ph: phase) (g: heap) (s: a.ast) (wz: nat).
    a.inv ph g s ==>
    (let (g', s', obj) = a.alloc ph g s wz in alloc_post a ph g s wz g' s' obj)

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
