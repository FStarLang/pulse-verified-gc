/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPhase.Util - walk and header facts the sweep phase uses
/// ---------------------------------------------------------------------------
///
/// Small facts about the heap's walk and headers, shared by the sweep phase
/// (`GC.Spec.SweepPhase.Intrinsic`), its program events
/// (`GC.Gen.SweepPhase`) and the allocator's shape lemmas
/// (`GC.Gen.AllocShape`):
///
///   * headers: a header is its size, colour and tag (`header_eq`); part 1 of
///     well-formedness always holds (`part1_holds`);
///   * the walk: nothing of it lies inside one of its blocks
///     (`no_pos_inside`); replacing a stretch of it (`seg_replace`); a write
///     off it (`write_off_walk`); heaps with the same walk and headers have the
///     same free-list cells (`cells_transfer`);
///   * the stop-the-world sweep's invariant read block by block
///     (`swept_block_kinds`, `behind_pos_ref`, `front_pos`);
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

/// ---------------------------------------------------------------------------
/// The stop-the-world sweep's invariant, block by block
/// ---------------------------------------------------------------------------

/// The two kinds of swept block, told apart by the marked heap's colour.
val swept_block_kinds (g0 g: heap) (p: hp_addr)
  : Lemma (requires swept_block g0 g p)
          (ensures W.can_step g p /\ W.can_step g0 p /\
                   (black_at g0 p ==> marked_block g0 g p /\ W.bnext g0 p == W.bnext g p) /\
                   (not (black_at g0 p) ==> free_run g0 g p))

/// Behind the cursor, every block of the current heap's walk is at a position
/// of the marked heap's walk.
val behind_pos_ref (g0 g: heap) (c: nat) (p: nat)
  : Lemma (requires W.reaches g zero_addr c /\ behind_ok g0 g c /\
                    W.reaches g zero_addr p /\ p <= c)
          (ensures W.reaches g0 zero_addr p)

/// Two heaps whose walks both reach `c` and that agree from `c` on have the
/// same blocks from `c` on, with the same headers.
val front_pos (g0 g: heap) (c: nat) (p: hp_addr)
  : Lemma (requires W.reaches g0 zero_addr c /\ W.reaches g zero_addr c /\
                    front_same g0 g c /\ U64.v p >= c)
          (ensures (pos g p <==> pos g0 p) /\ read_word g p == read_word g0 p /\
                   W.bnext g p == W.bnext g0 p)

/// ---------------------------------------------------------------------------
/// Blackening a set of blocks
/// ---------------------------------------------------------------------------

/// A header, black, with the same size and tag.
let black_header (h: U64.t) : U64.t = makeHeader (getWosize h) GC.Lib.Header.Black (getTag h)

val black_header_facts (h: U64.t)
  : Lemma (getWosize (black_header h) == getWosize h /\
           getColor (black_header h) == GC.Lib.Header.Black /\
           getTag (black_header h) == getTag h)

/// Blacken the header of every block of the walk from `p` that `sel` picks.
/// `sel` is fixed in advance, so it is the heap's walk -- which blackening a
/// header does not change -- that decides which words are written.
let rec recolour (sel: hp_addr -> GTot bool) (g: heap) (p: hp_addr)
  : GTot heap (decreases (heap_size - U64.v p))
  = if not (W.can_step g p) then g
    else begin
      let g1 = if sel p then write_word g p (black_header (read_word g p)) else g in
      let n = W.bnext g p in
      if n >= heap_size then g1
      else begin
        W.bnext_facts g p;
        recolour sel g1 (mk_hp_addr n)
      end
    end

/// What `recolour` leaves at each word.
val recolour_read (sel: hp_addr -> GTot bool) (g: heap) (p: hp_addr) (a: hp_addr)
  : Lemma (read_word (recolour sel g p) a ==
           (if W.reaches g p (U64.v a) && W.can_step g a && sel a
            then black_header (read_word g a) else read_word g a))

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
