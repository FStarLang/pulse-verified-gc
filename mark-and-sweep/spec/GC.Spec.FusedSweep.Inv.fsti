/// ---------------------------------------------------------------------------
/// GC.Spec.FusedSweep.Inv - the sweep's loop invariant
/// ---------------------------------------------------------------------------
///
/// `sweep_inv g0 g fp st` relates the heap right after marking (`g0`) to the
/// current heap (`g`) at sweep state `st`, with `fp` the head of the free list.
/// Writing `c` for the cursor:
///
///   1. *Behind the cursor* (`behind_ok`): every block of `g`'s walk below `c`
///      is either a survivor -- black in `g0`, now white, same size, tag and
///      fields -- or a free (blue) block covering a run of blocks that were
///      dead (white or blue) in `g0`.  No two free blocks are adjacent
///      (`no_adjacent_free`), and the block ending at `c` is free exactly
///      when `prev_free` says so (`ends_free`).
///   2. *In front of the cursor* (`front_same`): `g` is word for word `g0`.
///   3. *The free list* (`FLA.fl_ascending g fp`): every cell of the whole
///      heap, in ascending order.
///   4. *`swept_tail` and `last_fragment`* (`tail_ok`, `frag_ok`): the former
///      is the highest cell below `c` (or 0 when there is none); the latter,
///      when set, is the header-only free block ending at `c`.
///   5. *The walk*: `c` is a position of both walks, so the walk of `g` covers
///      the swept part of the heap block by block and continues as `g0`'s.
///
/// `sweep_start_inv` establishes it, `GC.Spec.FusedSweep.Step.sweep_step_inv`
/// keeps it, and `GC.Spec.FusedSweep.End` reads the post-collection facts off
/// it once the cursor reaches the end of the heap.

module GC.Spec.FusedSweep.Inv

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending

/// ---------------------------------------------------------------------------
/// Headers at walk positions
/// ---------------------------------------------------------------------------

let black_at (g: heap) (p: hp_addr) : bool = getColor (read_word g p) = Header.Black
let blue_at (g: heap) (p: hp_addr) : bool = getColor (read_word g p) = Header.Blue
let wz_at (g: heap) (p: hp_addr) : nat = U64.v (getWosize (read_word g p))

/// The header a survivor is given: same size and tag, white.
let white_header (h: U64.t) : U64.t = makeHeader (getWosize h) Header.White (getTag h)

val white_header_facts (h: U64.t)
  : Lemma (getWosize (white_header h) == getWosize h /\
           getColor (white_header h) == Header.White /\
           getTag (white_header h) == getTag h)

/// The fields of a fresh free header.
val free_header_facts (wz: nat{wz < pow2 54})
  : Lemma (U64.v (getWosize (free_header wz)) == wz /\
           getColor (free_header wz) == Header.Blue /\
           getTag (free_header wz) == 0UL)

/// ---------------------------------------------------------------------------
/// Dead runs of `g0`
/// ---------------------------------------------------------------------------

/// The walk of `g0` from `a` lands on `b`, and every block it crosses is dead
/// (not black).
let rec dead_run (g0: heap) (a: hp_addr) (b: nat)
  : Tot bool (decreases (heap_size - U64.v a))
  = if U64.v a = b then true
    else if U64.v a > b || not (W.can_step g0 a) || black_at g0 a then false
    else begin
      let n = W.bnext g0 a in
      if n = b then true
      else if n > b || n >= heap_size then false
      else begin
        aligned_plus_mul8 (U64.v a) (U64.v (getWosize (read_word g0 a)) + 1);
        dead_run g0 (mk_hp_addr n) b
      end
    end

val dead_run_reaches (g0: heap) (a: hp_addr) (b: nat)
  : Lemma (requires dead_run g0 a b) (ensures W.reaches g0 a b)

/// One dead block.
val dead_run_one (g0: heap) (p: hp_addr)
  : Lemma (requires W.can_step g0 p /\ not (black_at g0 p))
          (ensures dead_run g0 p (W.bnext g0 p))

/// Extend a dead run by the dead block at its end.
val dead_run_snoc (g0: heap) (a p: hp_addr)
  : Lemma (requires dead_run g0 a (U64.v p) /\ W.can_step g0 p /\ not (black_at g0 p))
          (ensures dead_run g0 a (W.bnext g0 p))

/// A block of `g0`'s walk inside a dead run is dead.
val dead_run_mem (g0: heap) (a: hp_addr) (b: nat) (q: hp_addr)
  : Lemma (requires dead_run g0 a b /\ W.reaches g0 a (U64.v q) /\ U64.v q < b)
          (ensures not (black_at g0 q))

/// ---------------------------------------------------------------------------
/// Blocks behind the cursor
/// ---------------------------------------------------------------------------

/// A survivor: black in `g0`; white in `g` with the same size and tag; the
/// same fields.
let survivor (g0 g: heap) (p: hp_addr) : prop =
  black_at g0 p /\
  read_word g p == white_header (read_word g0 p) /\
  (forall (a: hp_addr). U64.v p < U64.v a /\ U64.v a < W.bnext g p ==>
     read_word g a == read_word g0 a)

/// A free block over a dead run of `g0`.  Its header is the one `g0` had (a
/// free block left alone) or a fresh one, of tag 0.
let free_run (g0 g: heap) (p: hp_addr) : prop =
  blue_at g p /\
  dead_run g0 p (W.bnext g p) /\
  (read_word g p == read_word g0 p \/ getTag (read_word g p) == 0UL)

let swept_block (g0 g: heap) (p: hp_addr) : prop =
  W.can_step g p /\ (survivor g0 g p \/ free_run g0 g p)

/// A swept block depends only on its own words of `g` (and on `g0`).
val swept_block_frame (g0 g g': heap) (p: hp_addr)
  : Lemma (requires swept_block g0 g p /\
                    (forall (a: hp_addr). U64.v p <= U64.v a /\ U64.v a < W.bnext g p ==>
                       read_word g' a == read_word g a))
          (ensures swept_block g0 g' p)

/// A free block depends only on its header.
val swept_block_frame_free (g0 g g': heap) (p: hp_addr)
  : Lemma (requires swept_block g0 g p /\ blue_at g p /\ read_word g' p == read_word g p)
          (ensures swept_block g0 g' p)

/// ---------------------------------------------------------------------------
/// The invariant's clauses
/// ---------------------------------------------------------------------------

[@@"opaque_to_smt"]
let front_same (g0 g: heap) (c: nat) : prop =
  forall (a: hp_addr). U64.v a >= c ==> read_word g a == read_word g0 a

[@@"opaque_to_smt"]
let behind_ok (g0 g: heap) (c: nat) : prop =
  forall (p: hp_addr). W.reaches g zero_addr (U64.v p) /\ U64.v p < c ==> swept_block g0 g p

[@@"opaque_to_smt"]
let no_adjacent_free (g: heap) (c: nat) : prop =
  forall (p q: hp_addr).
    W.reaches g zero_addr (U64.v p) /\ W.can_step g p /\ W.bnext g p == U64.v q /\
    U64.v q < c /\ blue_at g p ==> not (blue_at g q)

[@@"opaque_to_smt"]
let ends_free (g: heap) (c: nat) (b: bool) : prop =
  forall (p: hp_addr).
    W.reaches g zero_addr (U64.v p) /\ W.can_step g p /\ W.bnext g p == c ==> blue_at g p == b

[@@"opaque_to_smt"]
let tail_ok (g: heap) (c: nat) (t: U64.t) : prop =
  (t == 0UL \/ (FLA.fl_cell g t /\ U64.v t + wosize_at g t * 8 <= c)) /\
  (forall (x: U64.t). FLA.fl_cell g x /\ U64.v x < c ==> t <> 0UL /\ U64.v x <= U64.v t)

let frag_ok (g: heap) (c: nat) (f: U64.t) : prop =
  f == 0UL \/
  (U64.v f == c /\
   (if c >= U64.v zero_addr + 8 && c < heap_size && c % 8 = 0 then begin
      let p = mk_hp_addr (c - 8) in
      W.reaches g zero_addr (c - 8) /\ W.can_step g p /\ blue_at g p /\ wz_at g p == 0
    end else False))

/// The invariant.
[@@"opaque_to_smt"]
let sweep_inv (g0 g: heap) (fp: U64.t) (st: sweep_state) : prop =
  let c = U64.v st.cursor in
  c % 8 == 0 /\ c <= heap_size /\
  W.reaches g0 zero_addr c /\ W.reaches g zero_addr c /\
  front_same g0 g c /\ behind_ok g0 g c /\ no_adjacent_free g c /\
  ends_free g c (prev_free g st) /\
  tail_ok g c st.swept_tail /\ frag_ok g c st.last_fragment /\
  FLA.fl_ascending g fp

/// What each step needs of the heap the sweep started on: its walk runs to
/// the end of the heap.
let sweep_g0 (g0: heap) : prop =
  heap_objects_dense g0 /\ Seq.length (objects zero_addr g0) > 0

/// What the sweep needs of the heap it starts on.
let sweep_pre (g0: heap) (fp: U64.t) : prop =
  well_formed_heap g0 /\ sweep_g0 g0 /\ FLA.fl_ascending g0 fp

/// ---------------------------------------------------------------------------
/// Opening and closing the clauses
/// ---------------------------------------------------------------------------

val sweep_inv_intro (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires (let c = U64.v st.cursor in
                     c % 8 == 0 /\ c <= heap_size /\
                     W.reaches g0 zero_addr c /\ W.reaches g zero_addr c /\
                     front_same g0 g c /\ behind_ok g0 g c /\ no_adjacent_free g c /\
                     ends_free g c (prev_free g st) /\
                     tail_ok g c st.swept_tail /\ frag_ok g c st.last_fragment /\
                     FLA.fl_ascending g fp))
          (ensures sweep_inv g0 g fp st)

val sweep_inv_elim (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_inv g0 g fp st)
          (ensures (let c = U64.v st.cursor in
                    c % 8 == 0 /\ c <= heap_size /\
                    W.reaches g0 zero_addr c /\ W.reaches g zero_addr c /\
                    front_same g0 g c /\ behind_ok g0 g c /\ no_adjacent_free g c /\
                    ends_free g c (prev_free g st) /\
                    tail_ok g c st.swept_tail /\ frag_ok g c st.last_fragment /\
                    FLA.fl_ascending g fp))

val front_same_elim (g0 g: heap) (c: nat) (a: hp_addr)
  : Lemma (requires front_same g0 g c /\ U64.v a >= c)
          (ensures read_word g a == read_word g0 a)

val front_same_intro (g0 g: heap) (c: nat)
  (pf: (a: hp_addr -> Lemma (requires U64.v a >= c) (ensures read_word g a == read_word g0 a)))
  : Lemma (front_same g0 g c)

val behind_ok_elim (g0 g: heap) (c: nat) (p: hp_addr)
  : Lemma (requires behind_ok g0 g c /\ W.reaches g zero_addr (U64.v p) /\ U64.v p < c)
          (ensures swept_block g0 g p)

val behind_ok_intro (g0 g: heap) (c: nat)
  (pf: (p: hp_addr -> Lemma (requires W.reaches g zero_addr (U64.v p) /\ U64.v p < c)
                           (ensures swept_block g0 g p)))
  : Lemma (behind_ok g0 g c)

val no_adjacent_free_elim (g: heap) (c: nat) (p q: hp_addr)
  : Lemma (requires no_adjacent_free g c /\ W.reaches g zero_addr (U64.v p) /\ W.can_step g p /\
                    W.bnext g p == U64.v q /\ U64.v q < c /\ blue_at g p)
          (ensures not (blue_at g q))

val no_adjacent_free_intro (g: heap) (c: nat)
  (pf: (p: hp_addr -> q: hp_addr -> Lemma
         (requires W.reaches g zero_addr (U64.v p) /\ W.can_step g p /\
                   W.bnext g p == U64.v q /\ U64.v q < c /\ blue_at g p)
         (ensures not (blue_at g q))))
  : Lemma (no_adjacent_free g c)

val ends_free_elim (g: heap) (c: nat) (b: bool) (p: hp_addr)
  : Lemma (requires ends_free g c b /\ W.reaches g zero_addr (U64.v p) /\ W.can_step g p /\
                    W.bnext g p == c)
          (ensures blue_at g p == b)

val ends_free_intro (g: heap) (c: nat) (b: bool)
  (pf: (p: hp_addr -> Lemma
         (requires W.reaches g zero_addr (U64.v p) /\ W.can_step g p /\ W.bnext g p == c)
         (ensures blue_at g p == b)))
  : Lemma (ends_free g c b)

val tail_ok_elim (g: heap) (c: nat) (t: U64.t)
  : Lemma (requires tail_ok g c t)
          (ensures (t == 0UL \/ (FLA.fl_cell g t /\ U64.v t + wosize_at g t * 8 <= c)) /\
                   (forall (x: U64.t). FLA.fl_cell g x /\ U64.v x < c ==>
                      t <> 0UL /\ U64.v x <= U64.v t))

val tail_ok_intro (g: heap) (c: nat) (t: U64.t)
  : Lemma (requires (t == 0UL \/ (FLA.fl_cell g t /\ U64.v t + wosize_at g t * 8 <= c)) /\
                    (forall (x: U64.t). FLA.fl_cell g x /\ U64.v x < c ==>
                       t <> 0UL /\ U64.v x <= U64.v t))
          (ensures tail_ok g c t)

/// ---------------------------------------------------------------------------
/// Cells, as walk positions
/// ---------------------------------------------------------------------------

/// A free-list cell at a walk position.
let pos_cell (g: heap) (q: hp_addr) : bool =
  W.reaches g zero_addr (U64.v q) && W.can_step g q && blue_at g q && wz_at g q >= 1

/// A cell is the object of a block at a walk position that is free and has
/// room for a link.
val fl_cell_iff (g: heap) (x: U64.t)
  : Lemma (FLA.fl_cell g x <==>
           (is_obj x /\ U64.v x >= U64.v zero_addr + 8 /\ pos_cell g (mk_hp_addr (U64.v x - 8))))

/// `wosize_at` is the header's size.
val wosize_at_hd (g: heap) (x: U64.t)
  : Lemma (requires is_obj x)
          (ensures U64.v x >= 8 /\ wosize_at g x == wz_at g (mk_hp_addr (U64.v x - 8)))

/// A cell's link word is never a walk position: it is strictly inside the
/// cell's own block.
val cell_link_not_pos (g: heap) (x: U64.t) (q: nat)
  : Lemma (requires FLA.fl_cell g x /\ W.reaches g zero_addr q)
          (ensures U64.v x <> q)

/// ---------------------------------------------------------------------------
/// Start and facts
/// ---------------------------------------------------------------------------

/// The invariant holds at the start, with the free list the previous cycle left.
val sweep_start_inv (g0: heap) (fp: U64.t)
  : Lemma (requires sweep_pre g0 fp)
          (ensures sweep_inv g0 g0 fp sweep_start)

/// What the implementation needs at each step: the step is defined, and the
/// guards of its defensive branches are false.
val sweep_inv_facts (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_g0 g0 /\ sweep_inv g0 g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (st.swept_tail == 0UL \/ is_obj st.swept_tail) /\
                   (st.last_fragment == 0UL \/ is_obj st.last_fragment) /\
                   (prev_free g st ==>
                     (let p = if st.last_fragment <> 0UL then st.last_fragment else st.swept_tail in
                      is_obj p /\
                      wosize_at g p + U64.v (getWosize (read_word g (st.cursor <: hp_addr))) + 1
                        < pow2 54)))
