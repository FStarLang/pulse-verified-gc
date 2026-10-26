/// ---------------------------------------------------------------------------
/// GC.Spec.FusedSweep.Edit - the program's writes during the sweep phase
/// ---------------------------------------------------------------------------
///
/// Between sweep slices the program, and the minor collector on its behalf,
/// write the major heap.  Each such write keeps the sweep phase
/// (`GC.Spec.FusedSweep.Phase.sweeping`), with the reference heap updated
/// alongside:
///
///   * **a field write** (`write_sweeping`): a word in the body of a block that
///     is not free -- a field of a live object, which is all the program can
///     reach, all the pointer update after a minor collection rewrites, and
///     all promotion writes into the object it has just allocated.  The
///     reference heap takes the same write.
///   * **a retag** (`retag_sweeping`): rewriting the tag of an object
///     allocated since marking, keeping its size and colour -- what promotion
///     does to the object it has just filled.  The reference heap takes the
///     same rewrite, keeping its own colour.
///
/// Allocation is in `GC.Gen.SweepPhase`, which needs the generational
/// allocator lemmas.  This module also collects the frame facts both use.

module GC.Spec.FusedSweep.Edit

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.FusedSweep.Phase

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList

/// ---------------------------------------------------------------------------
/// Heaps
/// ---------------------------------------------------------------------------

/// `g` on `[lo, hi)`, `g1` elsewhere.
let splice (g1 g: heap) (lo hi: nat) : heap =
  Seq.init heap_size (fun (i: nat{i < heap_size}) ->
    if lo <= i && i < hi then Seq.index g i else Seq.index g1 i)

val splice_read (g1 g: heap) (lo hi: nat) (a: hp_addr)
  : Lemma (requires lo % 8 == 0 /\ hi % 8 == 0)
          (ensures read_word (splice g1 g lo hi) a ==
                   (if lo <= U64.v a && U64.v a < hi then read_word g a else read_word g1 a))

/// A header is determined by its size, colour and tag.
val header_eq (h h': U64.t)
  : Lemma (requires getWosize h == getWosize h' /\ getColor h == getColor h' /\ getTag h == getTag h')
          (ensures h == h')

/// Every block of the walk fits in the heap, so the size clause of
/// well-formedness always holds.
val part1_holds (g: heap) : Lemma (well_formed_heap_part1 g)

/// ---------------------------------------------------------------------------
/// The walk
/// ---------------------------------------------------------------------------

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

/// A dead run reads only the headers inside it.
val dead_run_frame (g g': heap) (a: hp_addr) (b: nat)
  : Lemma (requires forall (w: hp_addr). U64.v a <= U64.v w /\ U64.v w < b ==>
                      read_word g' w == read_word g w)
          (ensures dead_run g' a b == dead_run g a b)

/// ---------------------------------------------------------------------------
/// Swept blocks
/// ---------------------------------------------------------------------------

/// The two kinds of swept block, told apart by the reference heap's colour.
val swept_block_kinds (g1 g: heap) (p: hp_addr)
  : Lemma (requires swept_block g1 g p)
          (ensures W.can_step g p /\ W.can_step g1 p /\
                   (black_at g1 p ==> survivor g1 g p /\ W.bnext g1 p == W.bnext g p) /\
                   (not (black_at g1 p) ==> free_run g1 g p))

/// A swept block depends only on the reference heap's words inside it.
val swept_block_ref_frame (g1 g1' g: heap) (q: hp_addr)
  : Lemma (requires swept_block g1 g q /\
                    (forall (w: hp_addr). U64.v q <= U64.v w /\ U64.v w < W.bnext g q ==>
                       read_word g1' w == read_word g1 w))
          (ensures swept_block g1' g q)

/// Behind the cursor, every block of the current heap's walk is at a position
/// of the reference heap's walk.
val behind_pos_ref (g1 g: heap) (c: nat) (p: nat)
  : Lemma (requires W.reaches g zero_addr c /\ behind_ok g1 g c /\
                    W.reaches g zero_addr p /\ p <= c)
          (ensures W.reaches g1 zero_addr p)

/// During the sweep phase the current heap's walk covers the heap too.
val sweeping_dense (g0 g1 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweeping g0 g1 g fp st)
          (ensures heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                   W.reaches g zero_addr (W.walk_end g1 zero_addr) /\
                   W.walk_end g1 zero_addr + 8 >= heap_size)

/// A block of the current heap that is not free is a block of the reference
/// heap too, of the same size, black there.
val live_block_ref (g0 g1 g: heap) (fp: U64.t) (st: sweep_state) (p: hp_addr)
  : Lemma (requires sweeping g0 g1 g fp st /\ pos g p /\ not (blue_at g p))
          (ensures pos g1 p /\ W.bnext g1 p == W.bnext g p /\
                   (U64.v p >= U64.v st.cursor ==> read_word g1 p == read_word g p) /\
                   (U64.v p < U64.v st.cursor ==> black_at g1 p /\
                                                 read_word g p == white_header (read_word g1 p)))

/// ---------------------------------------------------------------------------
/// Field writes
/// ---------------------------------------------------------------------------

/// `a` is a word in the body of a block of `g` that is not free.
let live_word (g: heap) (a: hp_addr) : prop =
  exists (p: hp_addr). pos g p /\ not (blue_at g p) /\ U64.v p < U64.v a /\ U64.v a < W.bnext g p

/// A field write keeps the sweep phase; the reference heap takes the same write.
val write_sweeping (g0 g1 g: heap) (fp: U64.t) (st: sweep_state) (a: hp_addr) (v: U64.t)
  : Lemma (requires sweeping g0 g1 g fp st /\ live_word g a)
          (ensures sweeping g0 (write_word g1 a v) (write_word g a v) fp st)

/// ---------------------------------------------------------------------------
/// Retagging a new object
/// ---------------------------------------------------------------------------

/// Rewrite the tag of the object at `obj`, keeping its size and colour.
let retag (g: heap) (obj: U64.t) (tag: nat) : GTot heap =
  if tag >= 256 then g
  else if U64.v obj >= U64.v mword && U64.v obj < heap_size && U64.v obj % U64.v mword = 0 then
    let hd = hd_address (obj <: obj_addr) in
    let hdr = read_word g hd in
    write_word g hd (makeHeader (getWosize hdr) (getColor hdr) (U64.uint_to_t tag))
  else g

/// An object allocated since marking: black in the reference heap, and not a
/// block live after marking.
let new_object (g0 g1: heap) (p: hp_addr) : prop =
  pos g1 p /\ black_at g1 p /\ ~(pos g0 p /\ black_at g0 p)

/// Retagging a new object (with a tag other than the infix tag) keeps the
/// sweep phase; the reference heap is retagged too.
val retag_sweeping (g0 g1 g: heap) (fp: U64.t) (st: sweep_state) (obj: obj_addr) (tag: nat)
  : Lemma (requires sweeping g0 g1 g fp st /\ new_object g0 g1 (hd_address obj) /\
                    tag < 256 /\ U64.uint_to_t tag <> infix_tag)
          (ensures sweeping g0 (retag g1 obj tag) (retag g obj tag) fp st /\
                   new_object g0 (retag g1 obj tag) (hd_address obj))
