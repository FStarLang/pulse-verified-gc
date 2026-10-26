/// ---------------------------------------------------------------------------
/// GC.Spec.Walk - positions of the object walk
/// ---------------------------------------------------------------------------
///
/// `GC.Spec.Fields.objects` enumerates a heap by starting at a header and
/// jumping by each block's size.  This module names the positions that walk
/// lands on: `reaches g a b` says the walk of `g` started at `a` lands exactly
/// on `b` (a header, or the end of the heap).
///
/// The fused sweep (`GC.Spec.FusedSweep`) needs this vocabulary because it
/// changes the walk as it goes: a merge rewrites a free block's header to its
/// full size, so the walk jumps straight over the blocks it absorbed.  Stating
/// the sweep's invariant over walk positions, rather than over the sequence
/// `objects zero_addr g`, keeps each step local: a write either keeps every
/// block's size (`walk_write`), or merges a block with the next one
/// (`walk_merge`), and the walk changes in exactly the expected way.

module GC.Spec.Walk

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64

/// ---------------------------------------------------------------------------
/// One step
/// ---------------------------------------------------------------------------

/// The bytes the block whose header is at `p` occupies: header plus fields.
let bsize (g: heap) (p: hp_addr) : nat = (U64.v (getWosize (read_word g p)) + 1) * 8

/// The position just past the block at `p`.
let bnext (g: heap) (p: hp_addr) : nat = U64.v p + bsize g p

/// The walk can take a step at `p`: there is room for a header and the block
/// fits in the heap.  This is exactly the guard of `objects`.
let can_step (g: heap) (p: hp_addr) : bool =
  U64.v p + 8 < heap_size && bnext g p <= heap_size

/// `bnext` is word-aligned and strictly past `p`.
val bnext_facts (g: heap) (p: hp_addr)
  : Lemma (bnext g p % 8 == 0 /\ bnext g p >= U64.v p + 8)

/// ---------------------------------------------------------------------------
/// Walk positions
/// ---------------------------------------------------------------------------

/// `reaches g a b`: starting at `a` and jumping block by block, the walk of `g`
/// lands exactly on `b`.  Every block it jumps over can step, so `b` is either
/// a further header or the end of the last block.
let rec reaches (g: heap) (a: hp_addr) (b: nat)
  : Tot bool (decreases (heap_size - U64.v a))
  = if U64.v a = b then true
    else if U64.v a > b || not (can_step g a) then false
    else begin
      let n = bnext g a in
      if n = b then true
      else if n > b || n >= heap_size then false
      else begin
        aligned_plus_mul8 (U64.v a) (U64.v (getWosize (read_word g a)) + 1);
        reaches g (mk_hp_addr n) b
      end
    end

val reaches_bounds (g: heap) (a: hp_addr) (b: nat)
  : Lemma (requires reaches g a b)
          (ensures U64.v a <= b /\ b <= heap_size /\ b % 8 == 0)

val reaches_refl (g: heap) (a: hp_addr)
  : Lemma (reaches g a (U64.v a))

/// One step from `a`.
val reaches_step (g: heap) (a: hp_addr)
  : Lemma (requires can_step g a) (ensures reaches g a (bnext g a))

/// Unfold one step from `a`, when the target lies beyond `a`.
val reaches_unfold (g: heap) (a: hp_addr) (b: nat)
  : Lemma (requires reaches g a b /\ U64.v a < b)
          (ensures can_step g a /\ bnext g a <= b /\
                   (bnext g a < b ==> bnext g a < heap_size /\
                                      reaches g (mk_hp_addr (bnext g a)) b))

/// Extend a walk by the block at its end.
val reaches_snoc (g: heap) (a p: hp_addr)
  : Lemma (requires reaches g a (U64.v p) /\ can_step g p)
          (ensures reaches g a (bnext g p))

/// Concatenation.
val reaches_trans (g: heap) (a b: hp_addr) (c: nat)
  : Lemma (requires reaches g a (U64.v b) /\ reaches g b c)
          (ensures reaches g a c)

/// The walk is deterministic: of two of its positions, the later is reached
/// from the earlier.
val reaches_det (g: heap) (a b: hp_addr) (c: nat)
  : Lemma (requires reaches g a (U64.v b) /\ reaches g a c /\ U64.v b <= c)
          (ensures reaches g b c)

/// The blocks of a walk do not overlap: the block at a position ends at or
/// before any later position.
val reaches_block_before (g: heap) (a p: hp_addr) (q: nat)
  : Lemma (requires reaches g a (U64.v p) /\ reaches g a q /\ U64.v p < q)
          (ensures can_step g p /\ bnext g p <= q)

/// The block a walk ends with.
val last_block (g: heap) (a: hp_addr) (b: nat{reaches g a b /\ U64.v a < b})
  : GTot (p: hp_addr{reaches g a (U64.v p) /\ can_step g p /\ bnext g p == b})

/// The block of a walk that contains an address.
val block_at (g: heap) (a: hp_addr) (c: nat) (q: nat{reaches g a c /\ U64.v a <= q /\ q < c})
  : GTot (p: hp_addr{reaches g a (U64.v p) /\ U64.v p <= q /\ q < bnext g p /\
                     can_step g p /\ bnext g p <= c})

/// A walk that has reached the end of the heap stops there.
val reaches_stuck (g: heap) (a: hp_addr) (e: nat) (q: nat)
  : Lemma (requires reaches g a e /\ e + 8 >= heap_size /\ reaches g a q)
          (ensures q <= e)

/// ---------------------------------------------------------------------------
/// The walk and `objects`
/// ---------------------------------------------------------------------------

/// The objects of the walk from `a` are exactly the blocks at its positions
/// that can step.
val objects_mem_iff (g: heap) (a: hp_addr) (x: obj_addr)
  : Lemma (Seq.mem x (objects a g) <==>
           (U64.v x >= U64.v a + 8 /\ reaches g a (U64.v x - 8) /\
            can_step g (hd_address x)))

/// `hd_address`, as a walk position.
val hd_address_pos (x: obj_addr)
  : Lemma (U64.v (hd_address x) == U64.v x - 8 /\ hd_address x == mk_hp_addr (U64.v x - 8))

/// ---------------------------------------------------------------------------
/// Frames
/// ---------------------------------------------------------------------------

/// A walk up to `b` reads only the headers below `b`.
val reaches_frame_below (g g': heap) (a: hp_addr) (b: nat)
  : Lemma (requires forall (w: hp_addr). U64.v w < b ==> read_word g' w == read_word g w)
          (ensures reaches g' a b == reaches g a b)

/// Two heaps that agree from `a` on have the same walk from `a`.
val walk_frame_from (g g': heap) (a: hp_addr)
  : Lemma (requires forall (w: hp_addr). U64.v w >= U64.v a ==> read_word g' w == read_word g w)
          (ensures objects a g' == objects a g /\
                   (forall (b: nat). reaches g' a b == reaches g a b))

/// A write that keeps the size of every block the walk meets leaves the walk
/// alone.  Covers writing inside a block's body (not a walk position at all)
/// and recolouring a header (a walk position, same size).
val walk_write (g: heap) (a: hp_addr) (x: hp_addr) (v: U64.t)
  : Lemma (requires reaches g a (U64.v x) ==> getWosize v == getWosize (read_word g x))
          (ensures (let g' = write_word g x v in
                    objects a g' == objects a g /\
                    (forall (b: nat). reaches g' a b == reaches g a b)))

/// More generally: two heaps whose headers have the same size at every position
/// of the first one's walk have the same walk.
val walk_congr (g g': heap) (a: hp_addr)
  : Lemma (requires forall (q: hp_addr). reaches g a (U64.v q) ==>
                      getWosize (read_word g' q) == getWosize (read_word g q))
          (ensures objects a g' == objects a g /\
                   (forall (b: nat). reaches g' a b == reaches g a b))

/// Merging the block at `p` with the block after it: rewriting `p`'s header to
/// the combined size makes the walk jump over the second block's header and
/// nowhere else.
val walk_merge (g: heap) (a p: hp_addr) (v: U64.t)
  : Lemma (requires reaches g a (U64.v p) /\ can_step g p /\ bnext g p < heap_size /\
                    can_step g (mk_hp_addr (bnext g p)) /\
                    U64.v (getWosize v) ==
                      U64.v (getWosize (read_word g p)) +
                      U64.v (getWosize (read_word g (mk_hp_addr (bnext g p)))) + 1)
          (ensures (let g' = write_word g p v in
                    let b = bnext g p in
                    can_step g' p /\ bnext g' p == bnext g (mk_hp_addr b) /\
                    (forall (c: nat). reaches g' a c == (reaches g a c && c <> b))))

/// ---------------------------------------------------------------------------
/// Where the walk stops
/// ---------------------------------------------------------------------------

/// `walk_end g a`: the position at which the walk from `a` stops -- the end of
/// the heap, or the first position whose block cannot step.  It is the last
/// position the walk lands on (`reaches_walk_end`); when the walk runs to the
/// end of the heap it is that end (`walk_end_of_reaches`).
///
/// `heap_objects_dense` says that the walk tiles the heap: it stops only when
/// there is no room left for another header, never because a block claims
/// more space than the heap has.  As a scalar, density is the one equation
/// `walk_end g zero_addr + 8 >= heap_size` (`dense_of_reaches_end`,
/// `reaches_end_of_dense`), which a phase that changes block sizes preserves
/// exactly when it preserves that address.
let rec walk_end (g: heap) (a: hp_addr)
  : GTot nat (decreases (heap_size - U64.v a))
  = if not (can_step g a) then U64.v a
    else begin
      let n = bnext g a in
      if n >= heap_size then n
      else begin
        aligned_plus_mul8 (U64.v a) (U64.v (getWosize (read_word g a)) + 1);
        walk_end g (mk_hp_addr n)
      end
    end

/// A walk that lands at the end of the heap stops there.
val walk_end_of_reaches (g: heap) (a: hp_addr) (e: nat)
  : Lemma (requires reaches g a e /\ e + 8 >= heap_size)
          (ensures walk_end g a == e)

/// The walk lands on the position where it stops.
val reaches_walk_end (g: heap) (a: hp_addr)
  : Lemma (reaches g a (walk_end g a))

/// ---------------------------------------------------------------------------
/// Density
/// ---------------------------------------------------------------------------

/// A walk from `zero_addr` that reaches the end of the heap makes it dense.
val dense_of_reaches_end (g: heap) (e: nat)
  : Lemma (requires reaches g zero_addr e /\ e + 8 >= heap_size /\ can_step g zero_addr)
          (ensures heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0)

/// The walk of a dense heap reaches the end of the heap.
val reaches_end_of_dense (g: heap)
  : Lemma (requires heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0)
          (ensures can_step g zero_addr /\
                   reaches g zero_addr (walk_end g zero_addr) /\
                   walk_end g zero_addr + 8 >= heap_size)

/// On a walk that reaches the end of the heap, every position with room for a
/// header can step.
val can_step_before_end (g: heap) (a p: hp_addr) (e: nat)
  : Lemma (requires reaches g a e /\ e + 8 >= heap_size /\ reaches g a (U64.v p) /\
                    U64.v p + 8 < heap_size)
          (ensures can_step g p /\ U64.v p < e)
