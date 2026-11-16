/// ---------------------------------------------------------------------------
/// GC.Spec.FusedSweep.Inv - the sweep's clauses about the walk and the list
/// ---------------------------------------------------------------------------
///
/// The clauses of the sweep invariant
/// (`GC.Spec.SweepPhase.Intrinsic.sweep_inv_incremental`) that are about the
/// walk of the current heap `g`, its headers and its free list, at a cursor
/// `c` (a position of the walk):
///
///   * *behind the cursor* no two free blocks are adjacent
///     (`no_adjacent_free`), and the block ending at `c` is free exactly when
///     `prev_free` says so (`ends_free`);
///   * *the free list* (`FLA.fl_ascending g fp`): every cell of the whole
///     heap, in ascending order;
///   * *`swept_tail` and `last_fragment`* (`tail_ok`, `frag_ok`): the former
///     is the highest cell below `c` (or 0 when there is none); the latter,
///     when set, is the header-only free block ending at `c`.
///
/// `GC.Spec.FusedSweep.Step` proves one lemma per clause and per kind of step
/// (one that keeps the walk, one that merges two blocks), and
/// `step_guards` gives what the step needs to be safe to run.

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
/// The invariant's clauses
/// ---------------------------------------------------------------------------

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
  (t == 0UL \/ (FL.fl_cell g t /\ U64.v t + wosize_at g t * 8 <= c)) /\
  (forall (x: U64.t). FL.fl_cell g x /\ U64.v x < c ==> t <> 0UL /\ U64.v x <= U64.v t)

let frag_ok (g: heap) (c: nat) (f: U64.t) : prop =
  f == 0UL \/
  (U64.v f == c /\
   (if c >= U64.v zero_addr + 8 && c < heap_size && c % 8 = 0 then begin
      let p = mk_hp_addr (c - 8) in
      W.reaches g zero_addr (c - 8) /\ W.can_step g p /\ blue_at g p /\ wz_at g p == 0
    end else False))

/// The walk of the heap the sweep starts on runs to the end of the heap.
let sweep_g0 (g0: heap) : prop =
  heap_objects_dense g0 /\ Seq.length (objects zero_addr g0) > 0

/// What the sweep needs of the heap it starts on.
let sweep_pre (g0: heap) (fp: U64.t) : prop =
  well_formed_heap g0 /\ sweep_g0 g0 /\ FLA.fl_ascending g0 fp

/// ---------------------------------------------------------------------------
/// Opening and closing the clauses
/// ---------------------------------------------------------------------------

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
          (ensures (t == 0UL \/ (FL.fl_cell g t /\ U64.v t + wosize_at g t * 8 <= c)) /\
                   (forall (x: U64.t). FL.fl_cell g x /\ U64.v x < c ==>
                      t <> 0UL /\ U64.v x <= U64.v t))

val tail_ok_intro (g: heap) (c: nat) (t: U64.t)
  : Lemma (requires (t == 0UL \/ (FL.fl_cell g t /\ U64.v t + wosize_at g t * 8 <= c)) /\
                    (forall (x: U64.t). FL.fl_cell g x /\ U64.v x < c ==>
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
  : Lemma (FL.fl_cell g x <==>
           (is_obj x /\ U64.v x >= U64.v zero_addr + 8 /\ pos_cell g (mk_hp_addr (U64.v x - 8))))

/// `wosize_at` is the header's size.
val wosize_at_hd (g: heap) (x: U64.t)
  : Lemma (requires is_obj x)
          (ensures U64.v x >= 8 /\ wosize_at g x == wz_at g (mk_hp_addr (U64.v x - 8)))

/// A cell's link word is never a walk position: it is strictly inside the
/// cell's own block.
val cell_link_not_pos (g: heap) (x: U64.t) (q: nat)
  : Lemma (requires FL.fl_cell g x /\ W.reaches g zero_addr q)
          (ensures U64.v x <> q)

/// ---------------------------------------------------------------------------
/// Facts at a step
/// ---------------------------------------------------------------------------

/// The walk of a dense heap steps at every position with room for a header.
val dense_can_step (g: heap) (c: hp_addr)
  : Lemma (requires heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                    W.reaches g zero_addr (U64.v c) /\ U64.v c + 8 < heap_size)
          (ensures W.can_step g c)

/// What the implementation needs at each step: the step is defined, and the
/// guards of its defensive branches are false.
val step_guards (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                    W.reaches g zero_addr (U64.v st.cursor) /\
                    tail_ok g (U64.v st.cursor) st.swept_tail /\
                    frag_ok g (U64.v st.cursor) st.last_fragment /\
                    FLA.fl_ascending g fp /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (st.swept_tail == 0UL \/ is_obj st.swept_tail) /\
                   (st.last_fragment == 0UL \/ is_obj st.last_fragment) /\
                   (prev_free g st ==>
                     (let p = if st.last_fragment <> 0UL then st.last_fragment else st.swept_tail in
                      is_obj p /\
                      wosize_at g p + U64.v (getWosize (read_word g (st.cursor <: hp_addr))) + 1
                        < pow2 54)))
