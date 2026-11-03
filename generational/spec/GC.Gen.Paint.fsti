/// ---------------------------------------------------------------------------
/// GC.Gen.Paint - the colour of what a minor collection promotes, by phase
/// ---------------------------------------------------------------------------
///
/// A minor collection allocates its promoted copies through the allocator, at
/// the collector's phase (`GC.Spec.Allocator.Cursor.alloc_phase`).  The phase
/// matters to exactly two things: the colour of each new header (black in
/// front of the sweep's cursor, white behind it) and the sweep's `swept_tail`.
/// The collection's specification (`GC.Gen.Cheney`) is stated once, outside a
/// sweep, where every new object is white; this module says what the same
/// collection does at any phase:
///
///   * **the heap is the idle one, painted** (`paint_ph ph g0 g`): every block
///     of `g` that is new -- not free, and not a not-free block of the heap the
///     collection started from, `g0` -- and in front of the cursor has its
///     header blackened (`recolour`).  At `Idle` nothing is painted;
///   * **`swept_tail` is the last cell of the list at or below where it was**
///     (`phase_at ph g`): allocation only takes cells off the list (or shrinks
///     them in place), and when it takes `swept_tail`'s own cell the tail moves
///     to the cell before it on the (ascending) list.
///
/// One promotion at the phase is the idle promotion, painted
/// (`paint_promote`), so a whole run is (`GC.Gen.CheneyAt.cheney_promote_at`).
/// Painting changes colours only: walk, sizes, tags, fields, free blocks and
/// links stay, so every colour-blind fact of the idle heap holds of the painted
/// one (`recoloured` and its lemmas, `paint_major_shape`).

module GC.Gen.Paint

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Spec.SweepPhase.Intrinsic
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module SA = GC.Spec.Allocator
module AC = GC.Spec.Allocator.Cursor
module Promote = GC.Gen.Promote
module WB = GC.Gen.WriteBodyLemmas
module GenInv = GC.Gen.HeapInvariant

/// ---------------------------------------------------------------------------
/// Painting
/// ---------------------------------------------------------------------------

/// `g` keeps every block of `g0` that is not free, with its header.
let kept (g0 g: heap) : prop =
  forall (q: hp_addr). pos g0 q /\ not (blue_at g0 q) ==> pos g q /\ read_word g q == read_word g0 q

/// A block of `g` at or in front of `c` that is new against `g0`.
let new_front (c: nat) (g0 g: heap) (q: hp_addr) : GTot bool =
  U64.v q >= c && not (blue_at g q) && not (pos g0 q && not (blue_at g0 q))

/// Blacken the new blocks of `g` in front of `c`.
let paint (c: nat) (g0 g: heap) : GTot heap = recolour (new_front c g0 g) g zero_addr

/// At a phase: nothing outside a sweep, the new blocks in front of the cursor
/// during one.
let paint_ph (ph: GC.Spec.Phase.gc_phase) (g0 g: heap) : GTot heap =
  match ph with
  | GC.Spec.Phase.Idle -> g
  | GC.Spec.Phase.Sweeping st -> paint (U64.v st.cursor) g0 g

val paint_read (c: nat) (g0 g: heap) (a: hp_addr)
  : Lemma (read_word (paint c g0 g) a ==
           (if pos g a && new_front c g0 g a then black_header (read_word g a) else read_word g a))

/// Nothing is new against the heap itself.
val paint_self (c: nat) (g0: heap) : Lemma (paint c g0 g0 == g0)

/// ---------------------------------------------------------------------------
/// Recoloured heaps
/// ---------------------------------------------------------------------------

/// `g'` is `g` with some non-free headers recoloured: the same walk; at every
/// position the same size and tag, and free exactly where `g` is (a free
/// header unchanged); every other word unchanged.
let recoloured (g g': heap) : prop =
  (forall (b: nat). W.reaches g' zero_addr b == W.reaches g zero_addr b) /\
  (forall (q: hp_addr). W.reaches g zero_addr (U64.v q) ==>
     getWosize (read_word g' q) == getWosize (read_word g q) /\
     getTag (read_word g' q) == getTag (read_word g q) /\
     blue_at g' q == blue_at g q /\
     (blue_at g q ==> read_word g' q == read_word g q)) /\
  (forall (a: hp_addr). ~(W.reaches g zero_addr (U64.v a)) ==> read_word g' a == read_word g a)

val paint_recoloured (c: nat) (g0 g: heap) : Lemma (recoloured g (paint c g0 g))

val paint_ph_recoloured (ph: GC.Spec.Phase.gc_phase) (g0 g: heap) : Lemma (recoloured g (paint_ph ph g0 g))

/// What recolouring keeps: the objects, which of them are free (so the
/// allocated ones), their sizes, tags and fields, and the free-list cells and
/// links.
val recoloured_facts (g g': heap)
  : Lemma (requires recoloured g g')
          (ensures objects zero_addr g' == objects zero_addr g /\
                   (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      (is_blue x g' <==> is_blue x g) /\
                      wosize_of_object x g' == wosize_of_object x g /\
                      tag_of_object x g' == tag_of_object x g /\
                      same_block g g' (hd_address x)) /\
                   (forall (x: obj_addr). allocated g' x == allocated g x) /\
                   (forall (x: U64.t). FL.fl_cell g' x <==> FL.fl_cell g x) /\
                   (forall (x: U64.t). FL.fl_cell g x ==> FL.fl_next g' x == FL.fl_next g x) /\
                   (heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 ==>
                      heap_objects_dense g' /\ Seq.length (objects zero_addr g') > 0) /\
                   (no_infix_block g ==> no_infix_block g'))

/// Well-formedness, on a view `v'` that counts after the recolouring the
/// blocks `v` counted before; and an ascending list.
val recoloured_wf (g g': heap) (v v': view)
  : Lemma (requires recoloured g g' /\ well_formed_view v g /\ view_ok v /\ view_ok v' /\
                    (forall (x: obj_addr). v' g' x == v g x))
          (ensures well_formed_view v' g')

val recoloured_fl (g g': heap) (fp: U64.t)
  : Lemma (requires recoloured g g' /\ FLA.fl_ascending g fp)
          (ensures FLA.fl_ascending g' fp)

/// The major half of the minor collection's shape, on a view the recolouring
/// does not change.
val recoloured_major_shape (g g': heap) (fp: U64.t) (v: view)
  : Lemma (requires recoloured g g' /\ GenInv.major_shape_view v g fp /\
                    (forall (x: obj_addr). v g' x == v g x))
          (ensures GenInv.major_shape_view v g' fp)

/// A view that recolouring does not change: it reads which blocks are free,
/// not the colours of the others.  `allocated` is one, and so is a sweep's
/// view with what is condemned fixed (`surviving_from`); the sweep's own view
/// (`surviving`) is not, since it reads white.
let colour_blind (v: view) : prop =
  forall (g g': heap) (x: obj_addr). recoloured g g' ==> v g' x == v g x

val colour_blind_elim (v: view) (g g': heap)
  : Lemma (requires colour_blind v /\ recoloured g g')
          (ensures forall (x: obj_addr). v g' x == v g x)

val allocated_colour_blind (_: unit) : Lemma (colour_blind allocated)

val surviving_from_colour_blind (st: sweep_state) (g0: heap)
  : Lemma (colour_blind (surviving_from st g0))

/// ---------------------------------------------------------------------------
/// Writes off the walk
/// ---------------------------------------------------------------------------

/// A write at a word that is not a position of the walk commutes with
/// painting.
val paint_write (c: nat) (g0 g: heap) (a: hp_addr) (v: U64.t)
  : Lemma (requires forall (x: nat). W.reaches g zero_addr x ==> x <> U64.v a)
          (ensures paint c g0 (write_word g a v) == write_word (paint c g0 g) a v)

/// So does the copy into an object's fields.
val paint_copy (c: nat) (g0 g: heap) (minor: minor_state) (src: U64.t) (dst: obj_addr) (i n: nat)
  : Lemma (requires Seq.mem dst (objects zero_addr g) /\ n <= U64.v (wosize_of_object dst g))
          (ensures paint c g0 (WB.copy_fields minor g src dst i n) ==
                   WB.copy_fields minor (paint c g0 g) src dst i n)

/// ---------------------------------------------------------------------------
/// `swept_tail`
/// ---------------------------------------------------------------------------

/// The last cell at or below `x` (0 when there is none).
let rec max_cell_below (g: heap) (x: nat) : GTot U64.t (decreases x) =
  if x = 0 then 0UL
  else if x < heap_size && FStar.IndefiniteDescription.strong_excluded_middle (FL.fl_cell g (U64.uint_to_t x))
  then U64.uint_to_t x
  else max_cell_below g (x - 1)

val max_cell_below_spec (g: heap) (x: nat)
  : Lemma (let m = max_cell_below g x in
           (m == 0UL \/ (FL.fl_cell g m /\ U64.v m <= x)) /\
           (forall (y: U64.t). FL.fl_cell g y /\ U64.v y <= x ==> m <> 0UL /\ U64.v y <= U64.v m))

/// Heaps with the same cells have the same last cells.
val max_cell_below_congr (g g': heap) (x: nat)
  : Lemma (requires forall (y: U64.t). FL.fl_cell g' y <==> FL.fl_cell g y)
          (ensures max_cell_below g' x == max_cell_below g x)

/// The phase, with `swept_tail` the last cell of `g` at or below where it was.
let phase_at (ph: GC.Spec.Phase.gc_phase) (g: heap) : GTot GC.Spec.Phase.gc_phase =
  match ph with
  | GC.Spec.Phase.Idle -> GC.Spec.Phase.Idle
  | GC.Spec.Phase.Sweeping st ->
      GC.Spec.Phase.Sweeping { st with swept_tail = max_cell_below g (U64.v st.swept_tail) }

/// A tail that is a cell (or the sentinel) is its own last cell.
val phase_at_self (ph: GC.Spec.Phase.gc_phase) (g: heap)
  : Lemma (requires (match ph with
                     | GC.Spec.Phase.Idle -> True
                     | GC.Spec.Phase.Sweeping st -> st.swept_tail == 0UL \/ FL.fl_cell g st.swept_tail))
          (ensures phase_at ph g == ph)

/// ---------------------------------------------------------------------------
/// One promotion
/// ---------------------------------------------------------------------------

/// What a promotion at a phase needs of the idle heap it paints: it keeps the
/// blocks the collection started with, and its list is ascending.
let paint_ok (g0 g: heap) (fp: U64.t) : prop = kept g0 g /\ FLA.fl_ascending g fp

/// A change that keeps the walk and every header keeps the blocks of `g0`.
val kept_heads (g0 g g': heap)
  : Lemma (requires kept g0 g /\ same_heads g g') (ensures kept g0 g')

/// **One promotion at the phase is the idle one, painted**, with the phase
/// at the idle result; and it keeps `paint_ok`.  `ph0` is the phase the
/// collection started in, and the promotion runs at `phase_at ph0 g`.
val paint_promote (ph0: GC.Spec.Phase.gc_phase) (g0 g: heap) (fp: U64.t)
                  (minor: minor_state) (obj: U64.t) (wz: nat{wz > 0})
  : Lemma (requires paint_ok g0 g fp /\ wz < pow2 54)
          (ensures (let r = Promote.promote_object minor g obj fp wz GC.Spec.Phase.Idle in
                    let r' = Promote.promote_object minor (paint_ph ph0 g0 g) obj fp wz (phase_at ph0 g) in
                    r'.Promote.major_out == paint_ph ph0 g0 r.Promote.major_out /\
                    r'.Promote.fp_out == r.Promote.fp_out /\
                    r'.Promote.new_addr == r.Promote.new_addr /\
                    r'.Promote.phase_out == phase_at ph0 r.Promote.major_out /\
                    paint_ok g0 r.Promote.major_out r.Promote.fp_out))

/// **Painting makes the new blocks in front of the cursor surviving**: on a
/// heap that kept every block of `g0`, the sweep's view of the painted heap
/// is the view of the heap with what is condemned read at `g0`.  A block of
/// `g0` keeps its header, so it is condemned exactly when it was; a new block
/// in front of the cursor is painted black, and one behind it is not in front
/// of the cursor, so neither is condemned.  This is `allocation_color` at
/// work: a white copy in front of the cursor would be condemned, and freed by
/// the sweep while reachable.
val paint_surviving (st: sweep_state) (g0 h: heap) (x: obj_addr)
  : Lemma (requires kept g0 h /\ U64.v st.cursor % 8 == 0)
          (ensures surviving st (paint (U64.v st.cursor) g0 h) x == surviving_from st g0 h x)

/// At the start of a collection there is nothing to paint.
val paint_start (ph0: GC.Spec.Phase.gc_phase) (g0: heap) (fp: U64.t)
  : Lemma (requires FLA.fl_ascending g0 fp)
          (ensures paint_ok g0 g0 fp /\ paint_ph ph0 g0 g0 == g0)

/// ---------------------------------------------------------------------------
/// The implementation's heap, against the idle one
/// ---------------------------------------------------------------------------

/// A minor collection's colouring: the phase it started in and the heap it
/// started from.
noeq type colouring = {
  c_phase: GC.Spec.Phase.gc_phase;
  c_base: heap;
}

/// The heap `ms` and phase `ph` the implementation holds, against the idle
/// heap `g` and free-list head `fp` the specification has reached: `ms` is
/// `g` painted, `ph` the phase at `g`, and `g` fit to keep painting.
let coloured (col: colouring) (ms: heap) (g: heap) (fp: U64.t) (ph: GC.Spec.Phase.gc_phase) : prop =
  ms == paint_ph col.c_phase col.c_base g /\
  ph == phase_at col.c_phase g /\
  paint_ok col.c_base g fp

/// The start of a collection: the implementation's heap is the idle one.
val coloured_start (ph: GC.Spec.Phase.gc_phase) (g: heap) (fp: U64.t)
  : Lemma (requires FLA.fl_ascending g fp /\ phase_at ph g == ph)
          (ensures coloured ({ c_phase = ph; c_base = g }) g g fp ph)

/// What the allocator needs, of both heaps.
val coloured_facts (col: colouring) (ms g: heap) (fp: U64.t) (ph: GC.Spec.Phase.gc_phase)
  : Lemma (requires coloured col ms g fp ph)
          (ensures blocks_fit g /\ FLA.fl_ascending g fp /\
                   GC.Spec.Allocator.Lemmas.fl_valid g fp heap_words /\
                   GC.Spec.Allocator.Lemmas.fl_chain_terminates g fp heap_words /\
                   blocks_fit ms /\ FLA.fl_ascending ms fp /\
                   GC.Spec.Allocator.Lemmas.fl_valid ms fp heap_words /\
                   GC.Spec.Allocator.Lemmas.fl_chain_terminates ms fp heap_words /\
                   recoloured g ms)

/// **One promotion, by the implementation, at the phase it holds**, is the
/// idle promotion of the specification, painted.
val coloured_promote (col: colouring) (ms g: heap) (fp: U64.t) (ph: GC.Spec.Phase.gc_phase)
                     (minor: minor_state) (obj: U64.t) (wz: nat{wz > 0})
  : Lemma (requires coloured col ms g fp ph /\ wz < pow2 54)
          (ensures (let r = Promote.promote_object minor g obj fp wz GC.Spec.Phase.Idle in
                    let r' = Promote.promote_object minor ms obj fp wz ph in
                    coloured col r'.Promote.major_out r.Promote.major_out r.Promote.fp_out r'.Promote.phase_out /\
                    r'.Promote.fp_out == r.Promote.fp_out /\
                    r'.Promote.new_addr == r.Promote.new_addr))

/// The phase depends only on the free-list cells, so a change that keeps the
/// walk and every header keeps it.
val phase_at_heads (ph: GC.Spec.Phase.gc_phase) (h h': heap)
  : Lemma (requires same_heads h h') (ensures phase_at ph h' == phase_at ph h)
