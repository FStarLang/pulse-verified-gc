/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPhase.Util - walk and header facts the sweep phase uses
/// ---------------------------------------------------------------------------
///
/// Small facts about the heap's walk and headers, shared by the sweep phase
/// (`GC.Spec.SweepPhase.Intrinsic`), its program events
/// (`GC.Spec.SweepPhase.Mutator`) and the allocator's shape lemmas
/// (`GC.Spec.Allocator.Shape`):
///
///   * headers: a header is its size, colour and tag (`header_eq`); part 1 of
///     well-formedness always holds (`part1_holds`);
///   * the walk: nothing of it lies inside one of its blocks
///     (`no_pos_inside`); replacing a stretch of it (`seg_replace`); a write
///     off it (`write_off_walk`); heaps with the same walk and headers have the
///     same free-list cells (`cells_transfer`);
///   * two heaps that agree from a common position of their walks on have
///     the same blocks there (`front_pos`);
///   * what a finished sweep leaves (`swept_clean`).

module GC.Spec.SweepPhase.Util

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending

/// ---------------------------------------------------------------------------
/// Headers
/// ---------------------------------------------------------------------------

/// A header is determined by its size, colour and tag.
val header_eq (h h': U64.t)
  : Lemma (requires getWosize h == getWosize h' /\ getColor h == getColor h' /\ getTag h == getTag h')
          (ensures h == h')

/// Every block of the walk fits in the heap, so the size clause of
/// well-formedness always holds.
val part1_holds (g: heap) : Lemma (blocks_fit g)

/// ---------------------------------------------------------------------------
/// The walk
/// ---------------------------------------------------------------------------

/// A block of `g`: a position of its walk from the heap's start, that can step.
let pos (g: heap) (p: hp_addr) : bool =
  W.reaches g zero_addr (U64.v p) && W.can_step g p

/// Nothing of a walk lies strictly inside one of its blocks.
val no_pos_inside (g: heap) (p: hp_addr) (q: nat)
  : Lemma (requires W.reaches g zero_addr (U64.v p) /\ W.reaches g zero_addr q /\
                    U64.v p < q /\ q < W.bnext g p)
          (ensures False)

/// Replacing a stretch `[a, b)` of the walk: if `g'` agrees with `g` outside
/// it and the walk of `g'` also crosses it from `a` to `b`, the two walks agree
/// outside it, and inside it `g'`'s walk is its own from `a`.
val seg_replace (g g': heap) (a: hp_addr) (b: nat)
  : Lemma (requires W.reaches g zero_addr (U64.v a) /\ W.reaches g a b /\ W.reaches g' a b /\
                    (forall (w: hp_addr). U64.v w < U64.v a ==> read_word g' w == read_word g w) /\
                    (forall (w: hp_addr). U64.v w >= b ==> read_word g' w == read_word g w))
          (ensures (forall (x: nat). (x <= U64.v a \/ x >= b) ==>
                      (W.reaches g' zero_addr x <==> W.reaches g zero_addr x)) /\
                   (forall (x: nat). (U64.v a <= x /\ x <= b) ==>
                      (W.reaches g' zero_addr x <==> W.reaches g' a x)))

/// A write at a word no position of the walk is at leaves the walk and every
/// header on it alone.
val write_off_walk (g: heap) (a: hp_addr) (v: U64.t)
  : Lemma (requires forall (x: nat). W.reaches g zero_addr x ==> x <> U64.v a)
          (ensures (forall (x: nat). W.reaches (write_word g a v) zero_addr x == W.reaches g zero_addr x) /\
                   objects zero_addr (write_word g a v) == objects zero_addr g /\
                   (forall (q: hp_addr). W.reaches g zero_addr (U64.v q) ==>
                      read_word (write_word g a v) q == read_word g q))

/// Two heaps with the same walk and the same headers on it have the same cells.
val cells_transfer (g g': heap)
  : Lemma (requires (forall (x: nat). W.reaches g' zero_addr x == W.reaches g zero_addr x) /\
                    (forall (q: hp_addr). W.reaches g zero_addr (U64.v q) ==> read_word g' q == read_word g q))
          (ensures forall (x: U64.t). FL.fl_cell g' x <==> FL.fl_cell g x)

/// Two heaps whose walks both reach `c` and that agree from `c` on have the
/// same blocks from `c` on, with the same headers.
val front_pos (g0 g: heap) (c: nat) (p: hp_addr)
  : Lemma (requires W.reaches g0 zero_addr c /\ W.reaches g zero_addr c /\
                    (forall (a: hp_addr). U64.v a >= c ==> read_word g a == read_word g0 a) /\
                    U64.v p >= c)
          (ensures (pos g p <==> pos g0 p) /\ read_word g p == read_word g0 p /\
                   W.bnext g p == W.bnext g0 p)

/// ---------------------------------------------------------------------------
/// What a sweep leaves
/// ---------------------------------------------------------------------------

/// The heap a sweep leaves: dense, with an exact ascending free list, every
/// object white or free, none infix.
let swept_clean (g: heap) (fp: U64.t) : prop =
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
  FLA.fl_ascending g fp /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> is_white x g \/ is_blue x g) /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> ~(is_infix x g))
