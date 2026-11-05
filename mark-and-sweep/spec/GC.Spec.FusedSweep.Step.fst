module GC.Spec.FusedSweep.Step

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Intrinsic

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module Util = GC.Spec.SweepPhase.Util

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Small facts about positions
/// ---------------------------------------------------------------------------

/// Nothing of a walk lies strictly inside one of its blocks.
let no_pos_inside (g: heap) (p: hp_addr) (q: nat)
  : Lemma (requires W.reaches g zero_addr (U64.v p) /\ W.reaches g zero_addr q /\
                    U64.v p < q /\ q < W.bnext g p)
          (ensures False)
  = W.reaches_block_before g zero_addr p q

/// A cell's link word lies in its own block and in no other.
#push-options "--z3rlimit 30"
let cell_link_own_block (g: heap) (x: U64.t) (p: hp_addr)
  : Lemma (requires FL.fl_cell g x /\ W.reaches g zero_addr (U64.v p) /\
                    U64.v p <> U64.v x - 8)
          (ensures U64.v x < U64.v p \/ U64.v x >= W.bnext g p)
  = fl_cell_iff g x;
    let q = mk_hp_addr (U64.v x - 8) in
    W.bnext_facts g q;
    W.bnext_facts g p;
    if U64.v p < U64.v q then W.reaches_block_before g zero_addr p (U64.v q)
    else W.reaches_block_before g zero_addr q (U64.v p)
#pop-options

/// The cell at a walk position.
let cell_at (g: heap) (q: hp_addr)
  : Lemma (requires pos_cell g q /\ U64.v q + 8 < heap_size)
          (ensures FL.fl_cell g (U64.add q mword) /\
                   U64.v (U64.add q mword) == U64.v q + 8)
  = W.reaches_bounds g zero_addr (U64.v q);
    fl_cell_iff g (U64.add q mword);
    assert (mk_hp_addr (U64.v q) == q)

/// A cell is at a walk position.
let cell_pos (g: heap) (x: U64.t)
  : Lemma (requires FL.fl_cell g x)
          (ensures U64.v x >= U64.v zero_addr + 8 /\ is_obj x /\
                   W.reaches g zero_addr (U64.v x - 8) /\
                   pos_cell g (mk_hp_addr (U64.v x - 8)) /\
                   wosize_at g x == wz_at g (mk_hp_addr (U64.v x - 8)) /\
                   W.bnext g (mk_hp_addr (U64.v x - 8)) == U64.v x + wosize_at g x * 8)
  = fl_cell_iff g x;
    wosize_at_hd g x

/// ---------------------------------------------------------------------------
/// Steps that keep the walk
/// ---------------------------------------------------------------------------
///
/// The survivor step, and the steps that leave or free a block without
/// merging, keep every block's size.  Besides the header at the cursor they
/// write at most the block's own link word and the link word `w` of the cell
/// it is linked after.

let nm_frame (g g': heap) (c: hp_addr) (n: nat) (w: U64.t) : prop =
  getWosize (read_word g' c) == getWosize (read_word g c) /\
  (forall (a: hp_addr). U64.v a >= n ==> read_word g' a == read_word g a) /\
  (forall (a: hp_addr). U64.v a < U64.v c /\ (w == 0UL \/ U64.v a <> U64.v w) ==>
     read_word g' a == read_word g a)

let nm_ctx (g g': heap) (c: hp_addr) (w: U64.t) : prop =
  W.reaches g zero_addr (U64.v c) /\ W.can_step g c /\
  nm_frame g g' c (W.bnext g c) w /\
  (w == 0UL \/ (FL.fl_cell g w /\ U64.v w < U64.v c))

#push-options "--z3rlimit 40"
let nm_walk (g g': heap) (c: hp_addr) (w: U64.t)
  : Lemma (requires nm_ctx g g' c w)
          (ensures objects zero_addr g' == objects zero_addr g /\
                   (forall (b: nat). W.reaches g' zero_addr b == W.reaches g zero_addr b))
  = let n = W.bnext g c in
    let aux (q: hp_addr)
      : Lemma (requires W.reaches g zero_addr (U64.v q))
              (ensures getWosize (read_word g' q) == getWosize (read_word g q))
      = if q = c then ()
        else if U64.v q < U64.v c then begin
          (if w <> 0UL then cell_link_not_pos g w (U64.v q));
          ()
        end
        else if U64.v q < n then no_pos_inside g c (U64.v q)
        else ()
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    W.walk_congr g g' zero_addr
#pop-options

/// The header at a walk position other than the cursor is unchanged.
let nm_header (g g': heap) (c: hp_addr) (w: U64.t) (p: hp_addr)
  : Lemma (requires nm_ctx g g' c w /\ W.reaches g zero_addr (U64.v p) /\ p <> c)
          (ensures read_word g' p == read_word g p /\ W.bnext g' p == W.bnext g p /\
                   W.can_step g' p == W.can_step g p)
  = W.bnext_facts g c;
    if U64.v p < U64.v c then (if w <> 0UL then cell_link_not_pos g w (U64.v p))
    else if U64.v p < W.bnext g c then no_pos_inside g c (U64.v p)

#push-options "--z3rlimit 40"
let nm_noadj (g g': heap) (c: hp_addr) (w: U64.t) (pf: bool)
  : Lemma (requires nm_ctx g g' c w /\ no_adjacent_free g (U64.v c) /\
                    ends_free g (U64.v c) pf /\ (blue_at g' c ==> not pf))
          (ensures no_adjacent_free g' (W.bnext g c))
  = nm_walk g g' c w;
    let aux (p q: hp_addr)
      : Lemma (requires W.reaches g' zero_addr (U64.v p) /\ W.can_step g' p /\
                        W.bnext g' p == U64.v q /\ U64.v q < W.bnext g c /\ blue_at g' p)
              (ensures not (blue_at g' q))
      = W.bnext_facts g c;
        if p = c then ()
        else if U64.v p > U64.v c then no_pos_inside g c (U64.v p)
        else begin
          nm_header g g' c w p;
          W.reaches_snoc g zero_addr p;
          W.reaches_block_before g zero_addr p (U64.v c);
          if q = c then ends_free_elim g (U64.v c) pf p
          else if U64.v q > U64.v c then no_pos_inside g c (U64.v q)
          else begin
            no_adjacent_free_elim g (U64.v c) p q;
            nm_header g g' c w q
          end
        end
    in
    no_adjacent_free_intro g' (W.bnext g c) aux
#pop-options

let nm_ends (g g': heap) (c: hp_addr) (w: U64.t)
  : Lemma (requires nm_ctx g g' c w)
          (ensures ends_free g' (W.bnext g c) (blue_at g' c))
  = nm_walk g g' c w;
    let aux (p: hp_addr)
      : Lemma (requires W.reaches g' zero_addr (U64.v p) /\ W.can_step g' p /\
                        W.bnext g' p == W.bnext g c)
              (ensures blue_at g' p == blue_at g' c)
      = W.bnext_facts g c;
        if p = c then ()
        else if U64.v p > U64.v c then no_pos_inside g c (U64.v p)
        else begin
          nm_header g g' c w p;
          W.reaches_block_before g zero_addr p (U64.v c)
        end
    in
    ends_free_intro g' (W.bnext g c) (blue_at g' c) aux

/// The cells: those of `g`, except possibly the block at the cursor.
#push-options "--z3rlimit 40"
let nm_cells (g g': heap) (c: hp_addr) (w: U64.t) (x: U64.t)
  : Lemma (requires nm_ctx g g' c w)
          (ensures (U64.v x <> U64.v c + 8 ==> (FL.fl_cell g' x <==> FL.fl_cell g x)) /\
                   (U64.v x == U64.v c + 8 ==>
                     (FL.fl_cell g' x <==> blue_at g' c /\ wz_at g c >= 1) /\
                     (FL.fl_cell g x <==> blue_at g c /\ wz_at g c >= 1)))
  = nm_walk g g' c w;
    fl_cell_iff g x;
    fl_cell_iff g' x;
    W.reaches_bounds g zero_addr (U64.v c);
    if U64.v x = U64.v c + 8 then begin
      assert (is_obj x);
      assert (mk_hp_addr (U64.v x - 8) == c);
      assert (W.can_step g' c);
      assert (wz_at g' c == wz_at g c)
    end
    else if is_obj x && U64.v x >= U64.v zero_addr + 8 then begin
      let q = mk_hp_addr (U64.v x - 8) in
      if W.reaches g zero_addr (U64.v q) then nm_header g g' c w q
    end
#pop-options

/// Links of cells are unchanged, other than `w`'s and the cursor block's own.
let nm_links (g g': heap) (c: hp_addr) (w: U64.t) (x: U64.t)
  : Lemma (requires nm_ctx g g' c w /\ FL.fl_cell g x /\ x <> w /\ U64.v x <> U64.v c + 8)
          (ensures FL.fl_next g' x == FL.fl_next g x)
  = cell_pos g x;
    let q = mk_hp_addr (U64.v x - 8) in
    W.bnext_facts g c;
    if U64.v q < U64.v c then W.reaches_block_before g zero_addr q (U64.v c)
    else if U64.v q < W.bnext g c then no_pos_inside g c (U64.v q)

/// `w`'s size is unchanged.
let nm_wosize (g g': heap) (c: hp_addr) (w: U64.t) (x: U64.t)
  : Lemma (requires nm_ctx g g' c w /\ FL.fl_cell g x /\ U64.v x < U64.v c)
          (ensures wosize_at g' x == wosize_at g x)
  = cell_pos g x;
    let q = mk_hp_addr (U64.v x - 8) in
    nm_header g g' c w q;
    wosize_at_hd g' x

/// ---------------------------------------------------------------------------
/// Merges
/// ---------------------------------------------------------------------------
///
/// The free block whose header is at `ph` ends at the cursor and grows over
/// the block at the cursor.  Besides `ph`'s header the step may write the
/// grown block's link word (at `ph + 8`, which can be the cursor itself) and
/// `swept_tail`'s link word `w`; everything in front of the absorbed block is
/// untouched.

let mg_ctx (g g': heap) (ph c: hp_addr) (w: U64.t) : prop =
  W.reaches g zero_addr (U64.v ph) /\ W.can_step g ph /\ W.bnext g ph == U64.v c /\
  W.reaches g zero_addr (U64.v c) /\ W.can_step g c /\
  wz_at g ph + wz_at g c + 1 < pow2 54 /\
  read_word g' ph == free_header (wz_at g ph + wz_at g c + 1) /\
  (forall (a: hp_addr). U64.v a >= W.bnext g c ==> read_word g' a == read_word g a) /\
  (forall (a: hp_addr). U64.v a < U64.v c /\ a <> ph /\ U64.v a <> U64.v ph + 8 /\
                        (w == 0UL \/ U64.v a <> U64.v w) ==>
     read_word g' a == read_word g a) /\
  (w == 0UL \/ (FL.fl_cell g w /\ U64.v w < U64.v c))

#push-options "--z3rlimit 40"
let mg_walk (g g': heap) (ph c: hp_addr) (w: U64.t)
  : Lemma (requires mg_ctx g g' ph c w)
          (ensures W.can_step g' ph /\ W.bnext g' ph == W.bnext g c /\
                   (forall (b: nat). W.reaches g' zero_addr b ==
                                     (W.reaches g zero_addr b && b <> U64.v c)))
  = let hnew = free_header (wz_at g ph + wz_at g c + 1) in
    free_header_facts (wz_at g ph + wz_at g c + 1);
    W.bnext_facts g ph;
    W.bnext_facts g c;
    let g1 = write_word g ph hnew in
    assert (mk_hp_addr (W.bnext g ph) == c);
    W.walk_merge g zero_addr ph hnew;
    read_write_same g ph hnew;
    let aux (q: hp_addr)
      : Lemma (requires W.reaches g1 zero_addr (U64.v q))
              (ensures getWosize (read_word g' q) == getWosize (read_word g1 q))
      = if q = ph then ()
        else begin
          read_write_different g ph q hnew;
          assert (W.reaches g zero_addr (U64.v q) /\ U64.v q <> U64.v c);
          if U64.v q < U64.v ph then begin
            (if w <> 0UL then cell_link_not_pos g w (U64.v q));
            W.reaches_block_before g zero_addr q (U64.v ph)
          end
          else if U64.v q < U64.v c then no_pos_inside g ph (U64.v q)
          else if U64.v q < W.bnext g c then no_pos_inside g c (U64.v q)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    W.walk_congr g1 g' zero_addr
#pop-options

/// Headers below `ph` are unchanged.
let mg_header (g g': heap) (ph c: hp_addr) (w: U64.t) (p: hp_addr)
  : Lemma (requires mg_ctx g g' ph c w /\ W.reaches g zero_addr (U64.v p) /\ U64.v p < U64.v ph)
          (ensures read_word g' p == read_word g p /\ W.bnext g' p == W.bnext g p /\
                   W.can_step g' p == W.can_step g p /\ W.bnext g p <= U64.v ph)
  = (if w <> 0UL then cell_link_not_pos g w (U64.v p));
    W.reaches_block_before g zero_addr p (U64.v ph)

/// The positions of the merged walk below the end of the absorbed block.
let mg_pos (g g': heap) (ph c: hp_addr) (w: U64.t) (p: hp_addr)
  : Lemma (requires mg_ctx g g' ph c w /\ W.reaches g' zero_addr (U64.v p) /\
                    U64.v p < W.bnext g c)
          (ensures W.reaches g zero_addr (U64.v p) /\ U64.v p <= U64.v ph)
  = mg_walk g g' ph c w;
    if U64.v p > U64.v ph then begin
      if U64.v p < U64.v c then no_pos_inside g ph (U64.v p)
      else no_pos_inside g c (U64.v p)
    end

#push-options "--z3rlimit 40"
let mg_noadj (g g': heap) (ph c: hp_addr) (w: U64.t)
  : Lemma (requires mg_ctx g g' ph c w /\ no_adjacent_free g (U64.v c) /\ blue_at g ph)
          (ensures no_adjacent_free g' (W.bnext g c))
  = mg_walk g g' ph c w;
    let aux (p q: hp_addr)
      : Lemma (requires W.reaches g' zero_addr (U64.v p) /\ W.can_step g' p /\
                        W.bnext g' p == U64.v q /\ U64.v q < W.bnext g c /\ blue_at g' p)
              (ensures not (blue_at g' q))
      = mg_pos g g' ph c w p;
        if p = ph then ()
        else begin
          mg_header g g' ph c w p;
          W.reaches_snoc g zero_addr p;
          if q = ph then no_adjacent_free_elim g (U64.v c) p ph
          else begin
            no_adjacent_free_elim g (U64.v c) p q;
            mg_header g g' ph c w q
          end
        end
    in
    no_adjacent_free_intro g' (W.bnext g c) aux
#pop-options

let mg_ends (g g': heap) (ph c: hp_addr) (w: U64.t)
  : Lemma (requires mg_ctx g g' ph c w)
          (ensures ends_free g' (W.bnext g c) true)
  = mg_walk g g' ph c w;
    free_header_facts (wz_at g ph + wz_at g c + 1);
    let aux (p: hp_addr)
      : Lemma (requires W.reaches g' zero_addr (U64.v p) /\ W.can_step g' p /\
                        W.bnext g' p == W.bnext g c)
              (ensures blue_at g' p == true)
      = W.bnext_facts g' p;
        mg_pos g g' ph c w p;
        if p <> ph then mg_header g g' ph c w p
    in
    ends_free_intro g' (W.bnext g c) true aux

/// The cells: the grown block, and those of `g` other than the absorbed block.
#push-options "--z3rlimit 40"
let mg_cells (g g': heap) (ph c: hp_addr) (w: U64.t) (x: U64.t)
  : Lemma (requires mg_ctx g g' ph c w)
          (ensures FL.fl_cell g' x <==>
                   (U64.v x == U64.v ph + 8 \/ (FL.fl_cell g x /\ U64.v x <> U64.v c + 8)))
  = mg_walk g g' ph c w;
    free_header_facts (wz_at g ph + wz_at g c + 1);
    fl_cell_iff g x;
    fl_cell_iff g' x;
    W.bnext_facts g ph;
    W.reaches_bounds g zero_addr (U64.v ph);
    if is_obj x && U64.v x >= U64.v zero_addr + 8 then begin
      let q = mk_hp_addr (U64.v x - 8) in
      if q = ph then ()
      else if q = c then ()
      else if W.reaches g zero_addr (U64.v q) then begin
        if U64.v q < U64.v ph then mg_header g g' ph c w q
        else if U64.v q < U64.v c then no_pos_inside g ph (U64.v q)
        else if U64.v q < W.bnext g c then no_pos_inside g c (U64.v q)
        else ()
      end
    end
#pop-options

/// Links of cells below the grown block are unchanged, other than `w`'s.
let mg_links (g g': heap) (ph c: hp_addr) (w: U64.t) (x: U64.t)
  : Lemma (requires mg_ctx g g' ph c w /\ FL.fl_cell g x /\ x <> w /\
                    U64.v x <> U64.v ph + 8 /\ U64.v x <> U64.v c + 8)
          (ensures FL.fl_next g' x == FL.fl_next g x)
  = cell_pos g x;
    let q = mk_hp_addr (U64.v x - 8) in
    W.bnext_facts g ph;
    W.bnext_facts g c;
    if U64.v q < U64.v ph then W.reaches_block_before g zero_addr q (U64.v ph)
    else if U64.v q < U64.v c then no_pos_inside g ph (U64.v q)
    else if U64.v q < W.bnext g c then no_pos_inside g c (U64.v q)

let mg_wosize (g g': heap) (ph c: hp_addr) (w: U64.t)
  : Lemma (requires mg_ctx g g' ph c w)
          (ensures wosize_at g' (U64.add ph mword) == wz_at g ph + wz_at g c + 1)
  = free_header_facts (wz_at g ph + wz_at g c + 1);
    W.bnext_facts g ph;
    wosize_at_hd g' (U64.add ph mword);
    assert (mk_hp_addr (U64.v (U64.add ph mword) - 8) == ph)

/// ---------------------------------------------------------------------------
/// The sweep invariant's own clauses, across a step
/// ---------------------------------------------------------------------------
///
/// Behind the new cursor the block just swept is white or free; from the new
/// cursor on nothing changed; and the blocks that are not free (`live_pos`)
/// are the same blocks before and after, with the same size, tag and fields.

/// A step that keeps the walk: behind the new cursor, every block is white
/// or free.
let nm_behind (g g': heap) (c: hp_addr) (w: U64.t)
  : Lemma (requires nm_ctx g g' c w /\ behind_swept g (U64.v c) /\ (white_at g' c \/ blue_at g' c))
          (ensures behind_swept g' (W.bnext g c))
  = nm_walk g g' c w;
    W.bnext_facts g c;
    let aux (p: hp_addr)
      : Lemma (requires W.reaches g' zero_addr (U64.v p) /\ U64.v p < W.bnext g c)
              (ensures W.can_step g' p /\ (white_at g' p \/ blue_at g' p))
      = if p = c then ()
        else if U64.v p > U64.v c then no_pos_inside g c (U64.v p)
        else begin
          nm_header g g' c w p;
          behind_swept_elim g (U64.v c) p
        end
    in
    behind_swept_intro g' (W.bnext g c) aux

/// A block behind the cursor that is not free lies below the cursor and is
/// no cell's block, so a write to a cell's link word or at the cursor's block
/// misses its body.
let behind_body (g: heap) (c: hp_addr) (w: U64.t) (q: hp_addr) (a: hp_addr)
  : Lemma (requires W.reaches g zero_addr (U64.v q) /\ W.reaches g zero_addr (U64.v c) /\
                    U64.v q < U64.v c /\ not (blue_at g q) /\
                    U64.v q < U64.v a /\ U64.v a < W.bnext g q /\
                    (w == 0UL \/ FL.fl_cell g w))
          (ensures W.bnext g q <= U64.v c /\ U64.v a < U64.v c /\ (w == 0UL \/ U64.v a <> U64.v w))
  = W.reaches_block_before g zero_addr q (U64.v c);
    if w <> 0UL then begin
      fl_cell_iff g w;
      cell_link_own_block g w q
    end

/// A step that keeps the walk: the blocks that are not free are the same.
/// The block at the cursor is not free before exactly when it is black
/// (nothing in front of the cursor is grey), and then it keeps its size, tag
/// and fields; otherwise it is free after.
let nm_live (g g': heap) (c: hp_addr) (w: U64.t) (q: hp_addr)
  : Lemma (requires nm_ctx g g' c w /\
                    (black_at g c \/ white_at g c \/ blue_at g c) /\
                    (black_at g c ==>
                      not (blue_at g' c) /\ getTag (read_word g' c) == getTag (read_word g c) /\
                      (forall (a: hp_addr). U64.v c < U64.v a /\ U64.v a < W.bnext g c ==>
                         read_word g' a == read_word g a)) /\
                    (not (black_at g c) ==> blue_at g' c))
          (ensures (live_pos g' (W.bnext g c) q == live_pos g (U64.v c) q) /\
                   (live_pos g (U64.v c) q ==> same_block g g' q))
  = nm_walk g g' c w;
    W.bnext_facts g c;
    let n = W.bnext g c in
    if q = c then ()
    else if U64.v q >= n then ()
    else if U64.v q > U64.v c then begin
      if W.reaches g zero_addr (U64.v q) then no_pos_inside g c (U64.v q)
    end else if W.reaches g zero_addr (U64.v q) then begin
      nm_header g g' c w q;
      if W.can_step g q && not (blue_at g q) then begin
        let body (a: hp_addr)
          : Lemma (requires U64.v q < U64.v a /\ U64.v a < W.bnext g q)
                  (ensures read_word g' a == read_word g a)
          = behind_body g c w q a
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires body)
      end
    end

let nm_live_all (g g': heap) (c: hp_addr) (w: U64.t)
  : Lemma (requires nm_ctx g g' c w /\
                    (black_at g c \/ white_at g c \/ blue_at g c) /\
                    (black_at g c ==>
                      not (blue_at g' c) /\ getTag (read_word g' c) == getTag (read_word g c) /\
                      (forall (a: hp_addr). U64.v c < U64.v a /\ U64.v a < W.bnext g c ==>
                         read_word g' a == read_word g a)) /\
                    (not (black_at g c) ==> blue_at g' c))
          (ensures (forall (q: hp_addr). live_pos g' (W.bnext g c) q == live_pos g (U64.v c) q) /\
                   (forall (q: hp_addr). live_pos g (U64.v c) q ==> same_block g g' q))
  = FStar.Classical.forall_intro (nm_live g g' c w)

/// A step that keeps the walk, and gives the block at the cursor its old tag
/// or tag 0, makes no block infix.
let nm_no_infix (g g': heap) (c: hp_addr) (w: U64.t)
  : Lemma (requires nm_ctx g g' c w /\ no_infix_block g /\
                    (getTag (read_word g' c) == getTag (read_word g c) \/ getTag (read_word g' c) == 0UL))
          (ensures no_infix_block g')
  = nm_walk g g' c w;
    let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g')) (ensures ~(is_infix x g'))
      = obj_pos g x;
        let q = hd_address x in
        colour_of g x; colour_of g' x;
        is_infix_spec x g; is_infix_spec x g';
        infix_tag_val ();
        if q <> c then nm_header g g' c w q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// A merge: behind the new cursor, every block is white or free.
let mg_behind (g g': heap) (ph c: hp_addr) (w: U64.t)
  : Lemma (requires mg_ctx g g' ph c w /\ behind_swept g (U64.v c))
          (ensures behind_swept g' (W.bnext g c))
  = mg_walk g g' ph c w;
    free_header_facts (wz_at g ph + wz_at g c + 1);
    let aux (p: hp_addr)
      : Lemma (requires W.reaches g' zero_addr (U64.v p) /\ U64.v p < W.bnext g c)
              (ensures W.can_step g' p /\ (white_at g' p \/ blue_at g' p))
      = mg_pos g g' ph c w p;
        if p = ph then ()
        else begin
          mg_header g g' ph c w p;
          behind_swept_elim g (U64.v c) p
        end
    in
    behind_swept_intro g' (W.bnext g c) aux

/// A merge: the blocks that are not free are the same.  The two blocks
/// merged are free before (the one at the cursor is not black, and nothing in
/// front of the cursor is grey) and after.
let mg_live (g g': heap) (ph c: hp_addr) (w: U64.t) (q: hp_addr)
  : Lemma (requires mg_ctx g g' ph c w /\ blue_at g ph /\ (white_at g c \/ blue_at g c))
          (ensures (live_pos g' (W.bnext g c) q == live_pos g (U64.v c) q) /\
                   (live_pos g (U64.v c) q ==> same_block g g' q))
  = mg_walk g g' ph c w;
    free_header_facts (wz_at g ph + wz_at g c + 1);
    W.bnext_facts g ph;
    W.bnext_facts g c;
    let n = W.bnext g c in
    if U64.v q >= n then ()
    else if q = ph then ()
    else if U64.v q < U64.v ph then begin
      if W.reaches g zero_addr (U64.v q) then begin
        mg_header g g' ph c w q;
        if W.can_step g q && not (blue_at g q) then begin
          let body (a: hp_addr)
            : Lemma (requires U64.v q < U64.v a /\ U64.v a < W.bnext g q)
                    (ensures read_word g' a == read_word g a)
            = behind_body g c w q a
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires body)
        end
      end
    end else begin
      (if W.reaches g' zero_addr (U64.v q) then mg_pos g g' ph c w q);
      if W.reaches g zero_addr (U64.v q) then begin
        if U64.v q < U64.v c then no_pos_inside g ph (U64.v q)
        else if U64.v q > U64.v c then no_pos_inside g c (U64.v q)
      end
    end

let mg_live_all (g g': heap) (ph c: hp_addr) (w: U64.t)
  : Lemma (requires mg_ctx g g' ph c w /\ blue_at g ph /\ (white_at g c \/ blue_at g c))
          (ensures (forall (q: hp_addr). live_pos g' (W.bnext g c) q == live_pos g (U64.v c) q) /\
                   (forall (q: hp_addr). live_pos g (U64.v c) q ==> same_block g g' q))
  = FStar.Classical.forall_intro (mg_live g g' ph c w)

/// A merge makes no block infix: the grown block has tag 0.
let mg_no_infix (g g': heap) (ph c: hp_addr) (w: U64.t)
  : Lemma (requires mg_ctx g g' ph c w /\ no_infix_block g)
          (ensures no_infix_block g')
  = mg_walk g g' ph c w;
    free_header_facts (wz_at g ph + wz_at g c + 1);
    W.bnext_facts g c;
    let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g')) (ensures ~(is_infix x g'))
      = obj_pos g' x; obj_pos g x;
        let q = hd_address x in
        colour_of g x; colour_of g' x;
        is_infix_spec x g; is_infix_spec x g';
        infix_tag_val ();
        if q <> ph then begin
          if U64.v q < W.bnext g c then begin
            mg_pos g g' ph c w q;
            mg_header g g' ph c w q
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// The free list around the cursor
/// ---------------------------------------------------------------------------

/// A linked block at the cursor is the one that follows `swept_tail`.
#push-options "--z3rlimit 40"
let linked_follows_tail (g: heap) (fp: U64.t) (c: hp_addr) (t: U64.t)
  : Lemma (requires FLA.fl_ascending g fp /\ tail_ok g (U64.v c) t /\
                    W.reaches g zero_addr (U64.v c) /\ FL.fl_cell g (U64.add c mword) /\
                    U64.v (U64.add c mword) == U64.v c + 8)
          (ensures (t == 0UL ==> fp == U64.add c mword) /\
                   (t <> 0UL ==> FL.fl_next g t == U64.add c mword))
  = let b = U64.add c mword in
    tail_ok_elim g (U64.v c) t;
    let n = if t = 0UL then fp else FL.fl_next g t in
    (if t = 0UL then FLA.fl_ascending_head g fp
     else FLA.fl_ascending_next g fp t);
    // n is the first cell above t; b is a cell above t
    assert (n <> 0UL);
    if n <> b then begin
      assert (U64.v n < U64.v b);
      cell_pos g n;
      let q = mk_hp_addr (U64.v n - 8) in
      if U64.v q < U64.v c then W.reaches_block_before g zero_addr q (U64.v c)
      else no_pos_inside g q (U64.v c)
    end
#pop-options

/// A cell below the cursor's block is below the cursor, hence at most `swept_tail`.
let cell_below (g: heap) (c: hp_addr) (t: U64.t) (x: U64.t)
  : Lemma (requires tail_ok g (U64.v c) t /\ W.reaches g zero_addr (U64.v c) /\
                    FL.fl_cell g x /\ U64.v x <= U64.v c + 8 /\ U64.v x <> U64.v c + 8)
          (ensures U64.v x < U64.v c /\ t <> 0UL /\ U64.v x <= U64.v t)
  = cell_pos g x;
    cell_link_not_pos g x (U64.v c);
    let q = mk_hp_addr (U64.v x - 8) in
    if U64.v q < U64.v c then W.reaches_block_before g zero_addr q (U64.v c);
    tail_ok_elim g (U64.v c) t

/// ---------------------------------------------------------------------------
/// The cases
/// ---------------------------------------------------------------------------


/// Reading through one write.
let read_w1 (g: heap) (x: hp_addr) (v: U64.t) (a: hp_addr)
  : Lemma (read_word (write_word g x v) a == (if a = x then v else read_word g a))
  = if a = x then read_write_same g x v else read_write_different g x a v

/// Reading through `set_after_tail`.
let read_sat (g: heap) (fp t v: U64.t) (a: hp_addr)
  : Lemma (requires t == 0UL \/ is_obj t)
          (ensures (let r = set_after_tail g fp t v in
                    (t == 0UL ==> fst r == g /\ snd r == v) /\
                    (t <> 0UL ==> snd r == fp /\
                                  read_word (fst r) a == (if U64.v a = U64.v t then v else read_word g a))))
  = if t <> 0UL then read_w1 g (t <: hp_addr) v a

/// The link that follows `swept_tail` is the list's.
let after_tail_next (g: heap) (fp t: U64.t)
  : Lemma (requires t == 0UL \/ FL.fl_cell g t)
          (ensures after_tail g fp t == (if t = 0UL then fp else FL.fl_next g t))
  = if t <> 0UL then FLA.fl_cell_facts g t

/// ---------------------------------------------------------------------------
/// The step, case by case
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let step_eq_black g fp st = ()
let step_eq_blue g fp st = ()
let step_eq_white g fp st = ()
let step_eq_merge g fp st = ()
#pop-options

/// Everything the cases share.
let step_ctx (g: heap) (fp: U64.t) (st: sweep_state) (c: hp_addr) : prop =
  sweep_inv_incremental g fp c /\ st == state_at g c /\ st.cursor == c /\ U64.v c + 8 < heap_size

let opened (g: heap) (fp: U64.t) (st: sweep_state) (c: hp_addr) : prop =
  let n = W.bnext g c in
  W.can_step g c /\ can_sweep g st /\ step_next g st == n /\
  W.reaches g zero_addr (U64.v c) /\ W.reaches g zero_addr n /\
  n % 8 == 0 /\ n <= heap_size /\ n >= U64.v c + 8 /\
  U64.v c >= U64.v zero_addr /\
  behind_swept g (U64.v c) /\ (black_at g c \/ white_at g c \/ blue_at g c) /\
  no_infix_block g /\
  no_adjacent_free g (U64.v c) /\ ends_free g (U64.v c) (prev_free g st) /\
  tail_ok g (U64.v c) st.swept_tail /\ frag_ok g (U64.v c) st.last_fragment /\
  FLA.fl_ascending g fp /\
  (st.swept_tail == 0UL \/
    (FL.fl_cell g st.swept_tail /\ is_obj st.swept_tail /\
     U64.v st.swept_tail + wosize_at g st.swept_tail * 8 <= U64.v c /\
     U64.v st.swept_tail < U64.v c))

#push-options "--z3rlimit 40"
let open_ctx (g: heap) (fp: U64.t) (st: sweep_state) (c: hp_addr)
  : Lemma (requires step_ctx g fp st c) (ensures opened g fp st c)
  = sweep_inv_incremental_elim g fp c;
    dense_can_step g c;
    W.reaches_snoc g zero_addr c;
    front_unswept_elim g (U64.v c) c;
    wf_with_parts ();
    W.bnext_facts g c;
    W.reaches_bounds g zero_addr (W.bnext g c);
    W.reaches_bounds g zero_addr (U64.v c);
    tail_ok_elim g (U64.v c) st.swept_tail;
    if st.swept_tail <> 0UL then begin cell_pos g st.swept_tail; FLA.fl_cell_facts g st.swept_tail end
#pop-options

/// What each case leaves: the clauses of the sweep invariant at the new
/// cursor `n` other than well-formedness and density, the heap from `n` on
/// unchanged, and the same blocks not free, with the same contents.
let stepped (g: heap) (c: hp_addr) (g': heap) (fp': U64.t) (st': sweep_state) : prop =
  let n = W.bnext g c in
  U64.v st'.cursor == n /\ W.reaches g' zero_addr n /\
  behind_swept g' n /\ no_infix_block g' /\
  no_adjacent_free g' n /\ ends_free g' n (prev_free g' st') /\
  tail_ok g' n st'.swept_tail /\ frag_ok g' n st'.last_fragment /\
  FLA.fl_ascending g' fp' /\
  (forall (a: hp_addr). U64.v a >= n ==> read_word g' a == read_word g a) /\
  (forall (q: hp_addr). live_pos g' n q == live_pos g (U64.v c) q) /\
  (forall (q: hp_addr). live_pos g (U64.v c) q ==> same_block g g' q)

/// A cell below the end of the cursor's block, other than the block itself,
/// lies below the cursor.
let cell_below_n (g: heap) (c: hp_addr) (x: U64.t)
  : Lemma (requires W.reaches g zero_addr (U64.v c) /\ W.can_step g c /\
                    FL.fl_cell g x /\ U64.v x < W.bnext g c /\ U64.v x <> U64.v c + 8)
          (ensures U64.v x < U64.v c)
  = cell_pos g x;
    cell_link_not_pos g x (U64.v c);
    let q = mk_hp_addr (U64.v x - 8) in
    if U64.v q < U64.v c then W.reaches_block_before g zero_addr q (U64.v c)
    else if U64.v q > U64.v c then no_pos_inside g c (U64.v q)

/// The tail clause after a step that keeps the walk and leaves `swept_tail`.
#push-options "--z3rlimit 40"
let nm_tail_keep (g g': heap) (c: hp_addr) (w t: U64.t)
  : Lemma (requires nm_ctx g g' c w /\ tail_ok g (U64.v c) t /\
                    (t == 0UL \/ (FL.fl_cell g t /\ U64.v t < U64.v c)) /\
                    not (FL.fl_cell g' (U64.add c mword) && U64.v (U64.add c mword) = U64.v c + 8))
          (ensures tail_ok g' (W.bnext g c) t)
  = tail_ok_elim g (U64.v c) t;
    W.bnext_facts g c;
    (if t <> 0UL then begin nm_wosize g g' c w t; nm_cells g g' c w t end);
    let below (x: U64.t)
      : Lemma (requires FL.fl_cell g' x /\ U64.v x < W.bnext g c)
              (ensures t <> 0UL /\ U64.v x <= U64.v t)
      = nm_cells g g' c w x;
        if U64.v x = U64.v c + 8 then assert (x == U64.add c mword)
        else cell_below_n g c x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    tail_ok_intro g' (W.bnext g c) t
#pop-options

/// The tail clause after a step that keeps the walk and makes the cursor's
/// block, now a cell, the new `swept_tail`.
#push-options "--z3rlimit 40"
let nm_tail_new (g g': heap) (c: hp_addr) (w t: U64.t)
  : Lemma (requires nm_ctx g g' c w /\ tail_ok g (U64.v c) t /\
                    (t == 0UL \/ U64.v t < U64.v c) /\
                    FL.fl_cell g' (U64.add c mword) /\ U64.v (U64.add c mword) = U64.v c + 8)
          (ensures tail_ok g' (W.bnext g c) (U64.add c mword))
  = let b = U64.add c mword in
    tail_ok_elim g (U64.v c) t;
    W.bnext_facts g c;
    wosize_at_hd g' b;
    assert (mk_hp_addr (U64.v b - 8) == c);
    let below (x: U64.t)
      : Lemma (requires FL.fl_cell g' x /\ U64.v x < W.bnext g c)
              (ensures U64.v x <= U64.v b)
      = nm_cells g g' c w x;
        if U64.v x = U64.v c + 8 then ()
        else cell_below_n g c x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    tail_ok_intro g' (W.bnext g c) b
#pop-options

/// A step that keeps the walk and the cells keeps the list.
#push-options "--z3rlimit 40"
let nm_same_list (g g': heap) (fp: U64.t) (c: hp_addr) (w: U64.t)
  : Lemma (requires nm_ctx g g' c w /\ FLA.fl_ascending g fp /\
                    (FL.fl_cell g (U64.add c mword) <==> FL.fl_cell g' (U64.add c mword)) /\
                    U64.v (U64.add c mword) = U64.v c + 8 /\
                    (forall (x: U64.t). FL.fl_cell g x ==> FL.fl_next g' x == FL.fl_next g x))
          (ensures FLA.fl_ascending g' fp)
  = let cells (x: U64.t) : Lemma (FL.fl_cell g' x <==> FL.fl_cell g x)
      = nm_cells g g' c w x;
        if U64.v x = U64.v c + 8 then assert (x == U64.add c mword)
    in
    FStar.Classical.forall_intro cells;
    FLA.fl_ascending_transfer g g' fp
#pop-options

/// ---------------------------------------------------------------------------
/// Cases that keep the walk
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 60"
let case_black (g: heap) (fp: U64.t) (st: sweep_state) (c: hp_addr)
  : Lemma (requires step_ctx g fp st c /\ black_at g c)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in stepped g c g' fp' st'))
  = open_ctx g fp st c;
    let h = read_word g c in
    let n = W.bnext g c in
    let t = st.swept_tail in
    let g' = write_word g c (white_header h) in
    let st' = advance st (nx_of g st) in
    step_eq_black g fp st;
    white_header_facts h;
    FStar.Classical.forall_intro (read_w1 g c (white_header h));
    assert (nm_ctx g g' c 0UL);
    nm_walk g g' c 0UL;
    nm_behind g g' c 0UL;
    nm_live_all g g' c 0UL;
    nm_no_infix g g' c 0UL;
    nm_noadj g g' c 0UL (prev_free g st);
    nm_ends g g' c 0UL;
    (if t <> 0UL then nm_wosize g g' c 0UL t);
    assert (prev_free g' st' == false);
    nm_cells g g' c 0UL (U64.add c mword);
    nm_tail_keep g g' c 0UL t;
    let links (x: U64.t) : Lemma (requires FL.fl_cell g x) (ensures FL.fl_next g' x == FL.fl_next g x)
      = FLA.fl_cell_facts g x;
        cell_link_not_pos g x (U64.v c)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires links);
    nm_same_list g g' fp c 0UL
#pop-options

#push-options "--z3rlimit 60"
let case_blue (g: heap) (fp: U64.t) (st: sweep_state) (c: hp_addr)
  : Lemma (requires step_ctx g fp st c /\ blue_at g c /\ not (prev_free g st))
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in stepped g c g' fp' st'))
  = open_ctx g fp st c;
    let n = W.bnext g c in
    let t = st.swept_tail in
    let b = bx_of st in
    step_eq_blue g fp st;
    assert (nm_ctx g g c 0UL);
    nm_behind g g c 0UL;
    nm_live_all g g c 0UL;
    nm_no_infix g g c 0UL;
    nm_noadj g g c 0UL (prev_free g st);
    nm_ends g g c 0UL;
    nm_cells g g c 0UL b;
    wosize_at_hd g b;
    assert (mk_hp_addr (U64.v b - 8) == c);
    if wz_at g c >= 1 then begin
      let st' = { cursor = nx_of g st; swept_tail = b; last_fragment = 0UL } in
      assert (prev_free g st' == true);
      nm_tail_new g g c 0UL t
    end else begin
      let st' = { cursor = nx_of g st; swept_tail = t; last_fragment = b } in
      assert (prev_free g st' == true);
      nm_tail_keep g g c 0UL t;
      assert (U64.v b == n);
      assert (frag_ok g n b)
    end
#pop-options

#push-options "--z3rlimit 60"
let case_white_cell (g: heap) (fp: U64.t) (st: sweep_state) (c: hp_addr)
  : Lemma (requires step_ctx g fp st c /\ not (black_at g c) /\ not (blue_at g c) /\
                    not (prev_free g st) /\ wz_at g c >= 1)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in stepped g c g' fp' st'))
  = open_ctx g fp st c;
    let n = W.bnext g c in
    let t = st.swept_tail in
    let b = bx_of st in
    let wz = wz_at g c in
    let nl = after_tail g fp t in
    let g1 = write_word g c (free_header wz) in
    let g2 = write_word g1 b nl in
    let r = set_after_tail g2 fp t b in
    let g3 = fst r in
    let fp3 = snd r in
    let st' = { cursor = nx_of g st; swept_tail = b; last_fragment = 0UL } in
    step_eq_white g fp st;
    free_header_facts wz;
    W.bnext_facts g c;
    // the three writes
    let rd (a: hp_addr)
      : Lemma (read_word g3 a ==
               (if t <> 0UL && U64.v a = U64.v t then b
                else if a = b then nl
                else if a = c then free_header wz
                else read_word g a))
      = read_sat g2 fp t b a; read_w1 g1 b nl a; read_w1 g c (free_header wz) a
    in
    FStar.Classical.forall_intro rd;
    read_sat g2 fp t b c;
    assert (nm_ctx g g3 c t);
    nm_walk g g3 c t;
    nm_behind g g3 c t;
    nm_live_all g g3 c t;
    nm_no_infix g g3 c t;
    nm_noadj g g3 c t (prev_free g st);
    nm_ends g g3 c t;
    nm_cells g g3 c t b;
    wosize_at_hd g3 b;
    assert (mk_hp_addr (U64.v b - 8) == c);
    assert (prev_free g3 st' == true);
    nm_tail_new g g3 c t t;
    // the list: b is inserted after t
    let cells (x: U64.t) : Lemma (FL.fl_cell g3 x <==> (FL.fl_cell g x \/ x == b))
      = nm_cells g g3 c t x;
        if U64.v x = U64.v c + 8 then assert (x == b)
    in
    FStar.Classical.forall_intro cells;
    let below (x: U64.t) : Lemma (requires FL.fl_cell g x /\ U64.v x < U64.v b)
                                 (ensures t <> 0UL /\ U64.v x <= U64.v t)
      = cell_below g c t x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    after_tail_next g fp t;
    let links (x: U64.t) : Lemma (requires FL.fl_cell g x /\ x <> t)
                                 (ensures FL.fl_next g3 x == FL.fl_next g x)
      = nm_links g g3 c t x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires links);
    (if t <> 0UL then FLA.fl_cell_facts g t);
    FLA.fl_ascending_insert g g3 fp fp3 t b
#pop-options

#push-options "--z3rlimit 60"
let case_white_frag (g: heap) (fp: U64.t) (st: sweep_state) (c: hp_addr)
  : Lemma (requires step_ctx g fp st c /\ not (black_at g c) /\ not (blue_at g c) /\
                    not (prev_free g st) /\ wz_at g c == 0)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in stepped g c g' fp' st'))
  = open_ctx g fp st c;
    let n = W.bnext g c in
    let t = st.swept_tail in
    let b = bx_of st in
    let g1 = write_word g c (free_header 0) in
    let st' = { cursor = nx_of g st; swept_tail = t; last_fragment = b } in
    step_eq_white g fp st;
    free_header_facts 0;
    FStar.Classical.forall_intro (read_w1 g c (free_header 0));
    assert (nm_ctx g g1 c 0UL);
    nm_walk g g1 c 0UL;
    nm_behind g g1 c 0UL;
    nm_live_all g g1 c 0UL;
    nm_no_infix g g1 c 0UL;
    nm_noadj g g1 c 0UL (prev_free g st);
    nm_ends g g1 c 0UL;
    nm_cells g g1 c 0UL b;
    assert (prev_free g1 st' == true);
    nm_tail_keep g g1 c 0UL t;
    W.bnext_facts g c;
    assert (U64.v b == n);
    assert (frag_ok g1 n b);
    let links (x: U64.t) : Lemma (requires FL.fl_cell g x) (ensures FL.fl_next g1 x == FL.fl_next g x)
      = FLA.fl_cell_facts g x;
        cell_link_not_pos g x (U64.v c)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires links);
    nm_same_list g g1 fp c 0UL
#pop-options

/// ---------------------------------------------------------------------------
/// Merges
/// ---------------------------------------------------------------------------

/// The free block before the cursor.
#push-options "--z3rlimit 40"
let merge_setup (g: heap) (fp: U64.t) (st: sweep_state) (c: hp_addr)
  : Lemma (requires step_ctx g fp st c /\ prev_free g st)
          (ensures (let p = if st.last_fragment <> 0UL then st.last_fragment else st.swept_tail in
                    is_obj p /\ U64.v p >= U64.v zero_addr + 8 /\
                    (let ph = mk_hp_addr (U64.v p - 8) in
                     hd_address (p <: obj_addr) == ph /\
                     W.reaches g zero_addr (U64.v ph) /\ W.can_step g ph /\
                     W.bnext g ph == U64.v c /\ blue_at g ph /\
                     wz_at g ph == wosize_at g p /\
                     wosize_at g p + wz_at g c + 1 < pow2 54 /\
                     (st.last_fragment <> 0UL ==> U64.v p == U64.v c /\
                        wz_at g ph == 0 /\ ~(FL.fl_cell g p) /\
                        (st.swept_tail == 0UL \/ U64.v st.swept_tail + 8 <= U64.v ph)) /\
                     (st.last_fragment == 0UL ==> p == st.swept_tail /\ FL.fl_cell g p))))
  = open_ctx g fp st c;
    sweep_inv_incremental_elim g fp c;
    step_guards g fp st;
    let p = if st.last_fragment <> 0UL then st.last_fragment else st.swept_tail in
    W.hd_address_pos (p <: obj_addr);
    wosize_at_hd g p;
    if st.last_fragment <> 0UL then begin
      let ph = mk_hp_addr (U64.v c - 8) in
      assert (frag_ok g (U64.v c) st.last_fragment);
      W.bnext_facts g ph;
      (if FL.fl_cell g p then cell_link_not_pos g p (U64.v c));
      if st.swept_tail <> 0UL then begin
        cell_pos g st.swept_tail;
        let tq = mk_hp_addr (U64.v st.swept_tail - 8) in
        if U64.v tq < U64.v ph then W.reaches_block_before g zero_addr tq (U64.v ph)
        else if U64.v tq = U64.v ph then ()
        else no_pos_inside g ph (U64.v tq)
      end
    end else
      cell_pos g p
#pop-options

/// The tail clause after a merge: the grown block is the new `swept_tail`.
#push-options "--z3rlimit 40"
let mg_tail (g g': heap) (ph c: hp_addr) (w: U64.t)
  : Lemma (requires mg_ctx g g' ph c w)
          (ensures tail_ok g' (W.bnext g c) (U64.add ph mword) /\
                   U64.v (U64.add ph mword) == U64.v ph + 8 /\
                   FL.fl_cell g' (U64.add ph mword) /\
                   U64.v (U64.add ph mword) + wosize_at g' (U64.add ph mword) * 8 == W.bnext g c)
  = let t' = U64.add ph mword in
    W.bnext_facts g ph;
    W.bnext_facts g c;
    mg_wosize g g' ph c w;
    mg_cells g g' ph c w t';
    let below (x: U64.t)
      : Lemma (requires FL.fl_cell g' x /\ U64.v x < W.bnext g c)
              (ensures U64.v x <= U64.v t')
      = mg_cells g g' ph c w x;
        if U64.v x = U64.v ph + 8 then ()
        else begin
          cell_below_n g c x;
          cell_pos g x;
          let q = mk_hp_addr (U64.v x - 8) in
          if U64.v q > U64.v ph then no_pos_inside g ph (U64.v q)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    tail_ok_intro g' (W.bnext g c) t'
#pop-options

/// Merging into `swept_tail`.
#push-options "--z3rlimit 80"
let case_merge_tail (g: heap) (fp: U64.t) (st: sweep_state) (c: hp_addr)
  : Lemma (requires step_ctx g fp st c /\ not (black_at g c) /\ prev_free g st /\
                    st.last_fragment == 0UL)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in stepped g c g' fp' st'))
  = open_ctx g fp st c;
    merge_setup g fp st c;
    let n = W.bnext g c in
    let t = st.swept_tail in
    let b = bx_of st in
    let ph = mk_hp_addr (U64.v t - 8) in
    let wz = wz_at g c in
    let hnew = free_header (wz_at g ph + wz + 1) in
    let g1 = write_word g ph hnew in
    let linked = blue_at g c && wz >= 1 in
    let st' = advance st (nx_of g st) in
    step_eq_merge g fp st;
    W.bnext_facts g ph;
    W.bnext_facts g c;
    assert (U64.v t == U64.v ph + 8);
    assert (U64.add ph mword == t);
    nm_cells g g c 0UL b;
    if linked then begin
      let r = set_after_tail g1 fp t (read_word g b) in
      let g2 = fst r in
      let rd (a: hp_addr)
        : Lemma (read_word g2 a == (if U64.v a = U64.v t then read_word g b
                                    else if a = ph then hnew else read_word g a))
        = read_sat g1 fp t (read_word g b) a; read_w1 g ph hnew a
      in
      FStar.Classical.forall_intro rd;
      assert (snd r == fp);
      assert (mg_ctx g g2 ph c t);
      mg_walk g g2 ph c t;
      mg_behind g g2 ph c t;
      mg_live_all g g2 ph c t;
      mg_no_infix g g2 ph c t;
      mg_noadj g g2 ph c t;
      mg_ends g g2 ph c t;
      mg_tail g g2 ph c t;
      assert (prev_free g2 st' == true);
      // the list: b is unlinked from after t
      linked_follows_tail g fp c t;
      let cells (x: U64.t) : Lemma (FL.fl_cell g2 x <==> (FL.fl_cell g x /\ x <> b))
        = mg_cells g g2 ph c t x;
          if U64.v x = U64.v c + 8 then assert (x == b)
      in
      FStar.Classical.forall_intro cells;
      FLA.fl_cell_facts g t;
      FLA.fl_cell_facts g b;
      let links (x: U64.t) : Lemma (requires FL.fl_cell g x /\ x <> t /\ x <> b)
                                   (ensures FL.fl_next g2 x == FL.fl_next g x)
        = mg_links g g2 ph c t x
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires links);
      FLA.fl_ascending_remove g g2 fp fp t b
    end else begin
      let rd (a: hp_addr) : Lemma (read_word g1 a == (if a = ph then hnew else read_word g a))
        = read_w1 g ph hnew a
      in
      FStar.Classical.forall_intro rd;
      assert (mg_ctx g g1 ph c 0UL);
      mg_walk g g1 ph c 0UL;
      mg_behind g g1 ph c 0UL;
      mg_live_all g g1 ph c 0UL;
      mg_no_infix g g1 ph c 0UL;
      mg_noadj g g1 ph c 0UL;
      mg_ends g g1 ph c 0UL;
      mg_tail g g1 ph c 0UL;
      assert (prev_free g1 st' == true);
      let cells (x: U64.t) : Lemma (FL.fl_cell g1 x <==> FL.fl_cell g x)
        = mg_cells g g1 ph c 0UL x;
          if U64.v x = U64.v c + 8 then assert (x == b)
      in
      FStar.Classical.forall_intro cells;
      let links (x: U64.t) : Lemma (requires FL.fl_cell g x) (ensures FL.fl_next g1 x == FL.fl_next g x)
        = FLA.fl_cell_facts g x;
          cell_link_not_pos g x (U64.v ph)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires links);
      FLA.fl_ascending_transfer g g1 fp
    end
#pop-options

/// Merging into the fragment just before the cursor, which thereby gains a
/// link field and joins the list after `swept_tail`.
#push-options "--z3rlimit 80"
let case_merge_frag (g: heap) (fp: U64.t) (st: sweep_state) (c: hp_addr)
  : Lemma (requires step_ctx g fp st c /\ not (black_at g c) /\ prev_free g st /\
                    st.last_fragment <> 0UL)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in stepped g c g' fp' st'))
  = open_ctx g fp st c;
    merge_setup g fp st c;
    let n = W.bnext g c in
    let t = st.swept_tail in
    let b = bx_of st in
    let f = st.last_fragment in
    let ph = mk_hp_addr (U64.v c - 8) in
    let wz = wz_at g c in
    let hnew = free_header (wz_at g ph + wz + 1) in
    let g1 = write_word g ph hnew in
    let linked = blue_at g c && wz >= 1 in
    let nxt = if linked then read_word g b else after_tail g fp t in
    let g2 = write_word g1 (f <: hp_addr) nxt in
    let r = set_after_tail g2 fp t f in
    let g3 = fst r in
    let fp3 = snd r in
    let st' = { cursor = nx_of g st; swept_tail = f; last_fragment = 0UL } in
    step_eq_merge g fp st;
    W.bnext_facts g ph;
    W.bnext_facts g c;
    assert (U64.add ph mword == f);
    assert (U64.v f == U64.v c);
    let rd (a: hp_addr)
      : Lemma (read_word g3 a == (if t <> 0UL && U64.v a = U64.v t then f
                                  else if U64.v a = U64.v f then nxt
                                  else if a = ph then hnew else read_word g a))
      = read_sat g2 fp t f a; read_w1 g1 (f <: hp_addr) nxt a; read_w1 g ph hnew a
    in
    FStar.Classical.forall_intro rd;
    assert (mg_ctx g g3 ph c t);
    mg_walk g g3 ph c t;
    mg_behind g g3 ph c t;
      mg_live_all g g3 ph c t;
      mg_no_infix g g3 ph c t;
    mg_noadj g g3 ph c t;
    mg_ends g g3 ph c t;
    mg_tail g g3 ph c t;
    assert (prev_free g3 st' == true);
    nm_cells g g c 0UL b;
    let links (x: U64.t) : Lemma (requires FL.fl_cell g x /\ x <> t /\ x <> b)
                                 (ensures FL.fl_next g3 x == FL.fl_next g x)
      = cell_link_not_pos g x (U64.v c);
        mg_links g g3 ph c t x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires links);
    (if t <> 0UL then FLA.fl_cell_facts g t);
    after_tail_next g fp t;
    if linked then begin
      // f takes b's place on the list
      linked_follows_tail g fp c t;
      let cells (x: U64.t) : Lemma (FL.fl_cell g3 x <==> ((FL.fl_cell g x /\ x <> b) \/ x == f))
        = mg_cells g g3 ph c t x;
          if U64.v x = U64.v c + 8 then assert (x == b);
          if U64.v x = U64.v ph + 8 then assert (x == f)
      in
      FStar.Classical.forall_intro cells;
      FLA.fl_cell_facts g b;
      FLA.fl_ascending_replace g g3 fp fp3 t b f
    end else begin
      // f joins the list after t
      let cells (x: U64.t) : Lemma (FL.fl_cell g3 x <==> (FL.fl_cell g x \/ x == f))
        = mg_cells g g3 ph c t x;
          if U64.v x = U64.v c + 8 then assert (x == b);
          if U64.v x = U64.v ph + 8 then assert (x == f)
      in
      FStar.Classical.forall_intro cells;
      let below (x: U64.t) : Lemma (requires FL.fl_cell g x /\ U64.v x < U64.v f)
                                   (ensures t <> 0UL /\ U64.v x <= U64.v t)
        = tail_ok_elim g (U64.v c) t
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires below);
      let links' (x: U64.t) : Lemma (requires FL.fl_cell g x /\ x <> t)
                                    (ensures FL.fl_next g3 x == FL.fl_next g x)
        = links x
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires links');
      FLA.fl_ascending_insert g g3 fp fp3 t f
    end
#pop-options


/// ---------------------------------------------------------------------------
/// One step
/// ---------------------------------------------------------------------------

/// The cases, by the colour at the cursor and whether the block before it is
/// free.
let step_cases (g: heap) (fp: U64.t) (c: hp_addr)
  : Lemma (requires sweep_inv_incremental g fp c /\ U64.v c + 8 < heap_size)
          (ensures can_sweep g (state_at g c) /\
                   (let (g', fp', st') = sweep_step g fp (state_at g c) in
                    stepped g c g' fp' st'))
  = let st = state_at g c in
    if black_at g c then case_black g fp st c
    else if prev_free g st then begin
      if st.last_fragment <> 0UL then case_merge_frag g fp st c
      else case_merge_tail g fp st c
    end
    else if blue_at g c then case_blue g fp st c
    else if wz_at g c >= 1 then case_white_cell g fp st c
    else case_white_frag g fp st c

/// The walk of the heap after a step still covers the heap: it reaches the
/// new cursor, from which the heap is unchanged.
let dense_after (g g': heap) (n: nat)
  : Lemma (requires heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                    W.reaches g zero_addr n /\ W.reaches g' zero_addr n /\ U64.v zero_addr < n /\
                    (forall (a: hp_addr). U64.v a >= n ==> read_word g' a == read_word g a))
          (ensures heap_objects_dense g' /\ Seq.length (objects zero_addr g') > 0)
  = W.reaches_unfold g' zero_addr n;
    W.reaches_bounds g' zero_addr n;
    W.reaches_end_of_dense g;
    let e = W.walk_end g zero_addr in
    W.reaches_stuck g zero_addr e n;
    W.reaches_bounds g zero_addr e;
    if n < e then begin
      let na = mk_hp_addr n in
      W.reaches_det g zero_addr na e;
      W.walk_frame_from g g' na;
      W.reaches_trans g' zero_addr na e
    end;
    W.dense_of_reaches_end g' e

/// In front of the new cursor the blocks are those of the heap before.
let front_after (g g': heap) (c n: nat) (p: hp_addr)
  : Lemma (requires W.reaches g zero_addr n /\ W.reaches g' zero_addr n /\ c < n /\
                    front_unswept g c /\
                    (forall (a: hp_addr). U64.v a >= n ==> read_word g' a == read_word g a) /\
                    Util.pos g' p /\ U64.v p >= n)
          (ensures black_at g' p \/ white_at g' p \/ blue_at g' p)
  = Util.front_pos g g' n p;
    front_unswept_elim g c p

/// So are the blocks pending free.
let pending_after (g g': heap) (c c': U64.t) (x: obj_addr)
  : Lemma (requires W.reaches g zero_addr (U64.v c') /\ W.reaches g' zero_addr (U64.v c') /\
                    U64.v c < U64.v c' /\
                    (forall (a: hp_addr). U64.v a >= U64.v c' ==> read_word g' a == read_word g a))
          (ensures pending_free c' g' x ==> pending_free c g x)
  = W.reaches_bounds g' zero_addr (U64.v c');
    obj_pos g x; obj_pos g' x;
    colour_of g x; colour_of g' x;
    let q = hd_address x in
    if U64.v q >= U64.v c' then Util.front_pos g g' (U64.v c') q

/// The step's frame, as the stop-the-world relation reads it: the heap from
/// the new cursor `n` on is unchanged, and the blocks not free are the same.
let step_frame (g: heap) (c: hp_addr) (g': heap) (n: nat) : prop =
  Util.pos g c /\ n == W.bnext g c /\
  (forall (a: hp_addr). U64.v a >= n ==> read_word g' a == read_word g a) /\
  (forall (q: hp_addr). live_pos g' n q == live_pos g (U64.v c) q) /\
  (forall (q: hp_addr). live_pos g (U64.v c) q ==> same_block g g' q)

let step_st (g: heap) (fp: U64.t) (c: hp_addr)
  : Lemma (requires sweep_inv_incremental g fp c /\ U64.v c + 8 < heap_size)
          (ensures can_sweep g (state_at g c) /\
                   (let (g', fp', st') = sweep_step g fp (state_at g c) in
                    let c' = st'.cursor in
                    st' == state_at g' c' /\
                    sweep_inv_incremental g' fp' c' /\
                    (forall (x: obj_addr). in_use (free_incremental c') g' x == in_use (free_incremental c) g x) /\
                    (forall (x: obj_addr). in_use (free_incremental c) g x ==> same_block g g' (hd_address x)) /\
                    (forall (x: obj_addr). pending_free c' g' x ==> pending_free c g x) /\
                    U64.v c' > U64.v c /\ U64.v c' <= heap_size /\
                    step_frame g c g' (U64.v c')))
  = step_cases g fp c;
    sweep_inv_incremental_elim g fp c;
    let st = state_at g c in
    let (g', fp', st') = sweep_step g fp st in
    let n = U64.v st'.cursor in
    dense_can_step g c;
    W.reaches_snoc g zero_addr c;
    W.bnext_facts g c;
    W.reaches_bounds g zero_addr (U64.v c);
    W.reaches_bounds g' zero_addr n;
    dense_after g g' n;
    front_unswept_intro g' n (fun p -> front_after g g' (U64.v c) n p);
    let keep (x: obj_addr)
      : Lemma ((in_use (free_incremental st'.cursor) g' x == in_use (free_incremental c) g x) /\
               (in_use (free_incremental c) g x ==> same_block g g' (hd_address x)))
      = live_obj g c x; live_obj g' st'.cursor x
    in
    FStar.Classical.forall_intro keep;
    free_incremental_ok st'.cursor;
    wf_transport g g' (free_incremental c) (free_incremental st'.cursor);
    sweep_inv_incremental_intro g' fp' st';
    FStar.Classical.forall_intro (pending_after g g' c st'.cursor)

let sweep_inv_incremental_step g fp c =
  let c : hp_addr = (sweep_inv_incremental_elim g fp c; c) in
  step_st g fp c

let pending_free_within_step g fp c dead =
  let c : hp_addr = (sweep_inv_incremental_elim g fp c; c) in
  step_st g fp c

/// ---------------------------------------------------------------------------
/// One step, stop-the-world
/// ---------------------------------------------------------------------------

/// A block black in the marked heap is not free before the step, so it is
/// not free after, with the same contents.
let stw_marked (g0 g: heap) (fp: U64.t) (c: hp_addr) (p: hp_addr)
  : Lemma (requires sweep_inv_stw g0 g fp c /\ U64.v c + 8 < heap_size /\
                    Util.pos g0 p /\ black_at g0 p)
          (ensures can_sweep g (state_at g c) /\
                   (let (g', fp', st') = sweep_step g fp (state_at g c) in
                    Util.pos g' p /\ not (blue_at g' p) /\ wz_at g' p == wz_at g0 p /\
                    getTag (read_word g' p) == getTag (read_word g0 p) /\
                    (forall (a: hp_addr). U64.v p < U64.v a /\ U64.v a < W.bnext g0 p ==>
                       read_word g' a == read_word g0 a)))
  = step_st g fp c;
    marked_survive_elim g0 g p;
    if U64.v p >= U64.v c then front_unchanged_elim g0 g (U64.v c) p

/// A block behind the new cursor that is not free was not free before the
/// step: behind the old cursor, then black in the marked heap; or the block
/// at the old cursor, black, as in the marked heap.
let stw_behind (g0 g: heap) (fp: U64.t) (c: hp_addr) (p: hp_addr)
  : Lemma (requires sweep_inv_stw g0 g fp c /\ U64.v c + 8 < heap_size)
          (ensures can_sweep g (state_at g c) /\
                   (let (g', fp', st') = sweep_step g fp (state_at g c) in
                    Util.pos g' p /\ U64.v p < U64.v st'.cursor /\ not (blue_at g' p) ==>
                      Util.pos g0 p /\ black_at g0 p))
  = step_st g fp c;
    sweep_inv_incremental_elim g fp c;
    let (g', fp', st') = sweep_step g fp (state_at g c) in
    let n = U64.v st'.cursor in
    if Util.pos g' p && U64.v p < n && not (blue_at g' p) then begin
      assert (live_pos g' n p);
      if U64.v p < U64.v c then survivors_were_marked_elim g0 g (U64.v c) p
      else begin
        if U64.v p > U64.v c then no_pos_inside g c (U64.v p);
        front_unswept_elim g (U64.v c) p;
        front_unchanged_elim g0 g (U64.v c) p
      end
    end

let stw_step (g0 g: heap) (fp: U64.t) (c: hp_addr)
  : Lemma (requires sweep_inv_stw g0 g fp c /\ U64.v c + 8 < heap_size)
          (ensures can_sweep g (state_at g c) /\
                   (let (g', fp', st') = sweep_step g fp (state_at g c) in
                    sweep_inv_stw g0 g' fp' st'.cursor))
  = step_st g fp c;
    let (g', fp', st') = sweep_step g fp (state_at g c) in
    let n = U64.v st'.cursor in
    front_unchanged_elim g0 g (U64.v c) c;
    W.reaches_snoc g0 zero_addr c;
    front_unchanged_intro g0 g' n (fun a -> front_unchanged_elim g0 g (U64.v c) a);
    marked_survive_intro g0 g' (fun p -> stw_marked g0 g fp c p);
    survivors_were_marked_intro g0 g' n (fun p -> stw_behind g0 g fp c p)

let sweep_inv_stw_step g0 g fp c =
  let c : hp_addr = (sweep_inv_incremental_elim g fp c; c) in
  stw_step g0 g fp c

let sweep_inv_incremental_ready g fp c =
  sweep_inv_incremental_elim g fp c;
  step_guards g fp (state_at g c)

/// ---------------------------------------------------------------------------
/// Up to `k` steps
/// ---------------------------------------------------------------------------

/// The sweep invariant at a state that is the derived one.
let inv_st (g: heap) (fp: U64.t) (st: sweep_state) : prop =
  sweep_inv_incremental g fp st.cursor /\ st == state_at g st.cursor

/// One step from such a state, when the sweep is not finished.
let step_inv (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires inv_st g fp st /\ not (sweep_done st.cursor))
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    inv_st g' fp' st' /\
                    (forall (x: obj_addr). in_use (free_incremental st'.cursor) g' x == in_use (free_incremental st.cursor) g x) /\
                    (forall (x: obj_addr). in_use (free_incremental st.cursor) g x ==> same_block g g' (hd_address x)) /\
                    (forall (x: obj_addr). pending_free st'.cursor g' x ==> pending_free st.cursor g x) /\
                    U64.v st'.cursor > U64.v st.cursor /\ U64.v st'.cursor <= heap_size))
  = sweep_inv_incremental_step g fp st.cursor

/// `same_block` composes.
let same_block_trans (g g' g'': heap) (q: hp_addr)
  : Lemma (requires same_block g g' q /\ same_block g' g'' q)
          (ensures same_block g g'' q)
  = W.bnext_facts g q; W.bnext_facts g' q

let rec steps_aux (g: heap) (fp: U64.t) (st: sweep_state) (k: nat)
  : Lemma (requires inv_st g fp st)
          (ensures (let (g', fp', st') = sweep_steps g fp st k in
                    inv_st g' fp' st' /\
                    (forall (x: obj_addr). in_use (free_incremental st'.cursor) g' x == in_use (free_incremental st.cursor) g x) /\
                    (forall (x: obj_addr). in_use (free_incremental st.cursor) g x ==> same_block g g' (hd_address x)) /\
                    (forall (x: obj_addr). pending_free st'.cursor g' x ==> pending_free st.cursor g x) /\
                    U64.v st'.cursor >= U64.v st.cursor /\
                    (st'.cursor == st.cursor ==> k = 0 \/ sweep_done st.cursor)))
          (decreases k)
  = sweep_steps_unfold g fp st k;
    if not (sweep_done st.cursor) then step_inv g fp st;
    if k = 0 || sweep_done st.cursor || not (can_sweep g st) then ()
    else begin
      let (g1, fp1, st1) = sweep_step g fp st in
      steps_aux g1 fp1 st1 (k - 1);
      let (g2, fp2, st2) = sweep_steps g1 fp1 st1 (k - 1) in
      let tr (x: obj_addr)
        : Lemma (in_use (free_incremental st.cursor) g x ==> same_block g g2 (hd_address x))
        = if in_use (free_incremental st.cursor) g x then same_block_trans g g1 g2 (hd_address x)
      in
      FStar.Classical.forall_intro tr;
      assert (U64.v st2.cursor > U64.v st.cursor)
    end

let sweep_inv_incremental_steps g fp c k = steps_aux g fp (state_at g c) k

let rec steps_stw_aux (g0 g: heap) (fp: U64.t) (st: sweep_state) (k: nat)
  : Lemma (requires sweep_inv_stw g0 g fp st.cursor /\ st == state_at g st.cursor)
          (ensures (let (g', fp', st') = sweep_steps g fp st k in
                    sweep_inv_stw g0 g' fp' st'.cursor))
          (decreases k)
  = sweep_steps_unfold g fp st k;
    if not (sweep_done st.cursor) then step_inv g fp st;
    if k = 0 || sweep_done st.cursor || not (can_sweep g st) then ()
    else begin
      sweep_inv_stw_step g0 g fp st.cursor;
      let (g1, fp1, st1) = sweep_step g fp st in
      steps_stw_aux g0 g1 fp1 st1 (k - 1)
    end

let sweep_inv_stw_steps g0 g fp c k = steps_stw_aux g0 g fp (state_at g c) k

let rec steps_done_aux (g: heap) (fp: U64.t) (st: sweep_state) (k: nat)
  : Lemma (requires inv_st g fp st /\ k * 8 >= heap_size - U64.v st.cursor)
          (ensures (let (g', fp', st') = sweep_steps g fp st k in sweep_done st'.cursor))
          (decreases k)
  = sweep_steps_unfold g fp st k;
    sweep_inv_incremental_elim g fp st.cursor;
    if sweep_done st.cursor then ()
    else begin
      step_inv g fp st;
      let (g1, fp1, st1) = sweep_step g fp st in
      sweep_inv_incremental_elim g1 fp1 st1.cursor;
      assert (U64.v st1.cursor >= U64.v st.cursor + 8);
      steps_done_aux g1 fp1 st1 (k - 1)
    end

let sweep_steps_done g fp c k = steps_done_aux g fp (state_at g c) k
