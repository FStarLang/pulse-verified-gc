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

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

let white_header_facts (h: U64.t) =
  makeHeader_getWosize (getWosize h) Header.White (getTag h);
  makeHeader_getColor (getWosize h) Header.White (getTag h);
  makeHeader_getTag (getWosize h) Header.White (getTag h)

let free_header_facts (wz: nat{wz < pow2 54}) =
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  makeHeader_getWosize (U64.uint_to_t wz) Header.Blue 0UL;
  makeHeader_getColor (U64.uint_to_t wz) Header.Blue 0UL;
  makeHeader_getTag (U64.uint_to_t wz) Header.Blue 0UL

/// ---------------------------------------------------------------------------
/// Dead runs
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1"
let rec dead_run_reaches (g0: heap) (a: hp_addr) (b: nat)
  : Lemma (requires dead_run g0 a b) (ensures W.reaches g0 a b)
          (decreases (heap_size - U64.v a))
  = if U64.v a = b then W.reaches_refl g0 a
    else begin
      let n = W.bnext g0 a in
      W.bnext_facts g0 a;
      if n = b then W.reaches_step g0 a
      else begin
        let na = mk_hp_addr n in
        dead_run_reaches g0 na b;
        W.reaches_step g0 a;
        W.reaches_trans g0 a na b
      end
    end
#pop-options

#push-options "--fuel 1 --ifuel 1"
let dead_run_one (g0: heap) (p: hp_addr) = ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let rec dead_run_snoc (g0: heap) (a p: hp_addr)
  : Lemma (requires dead_run g0 a (U64.v p) /\ W.can_step g0 p /\ not (black_at g0 p))
          (ensures dead_run g0 a (W.bnext g0 p))
          (decreases (heap_size - U64.v a))
  = W.bnext_facts g0 p;
    if U64.v a = U64.v p then ()
    else begin
      W.bnext_facts g0 a;
      let n = W.bnext g0 a in
      if n = U64.v p then begin
        dead_run_one g0 p;
        assert (mk_hp_addr n == p)
      end
      else dead_run_snoc g0 (mk_hp_addr n) p
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let rec dead_run_mem (g0: heap) (a: hp_addr) (b: nat) (q: hp_addr)
  : Lemma (requires dead_run g0 a b /\ W.reaches g0 a (U64.v q) /\ U64.v q < b)
          (ensures not (black_at g0 q))
          (decreases (heap_size - U64.v a))
  = if U64.v a = U64.v q then ()
    else begin
      // q lies beyond a, so the walk steps from a first
      W.reaches_bounds g0 a (U64.v q);
      W.reaches_unfold g0 a (U64.v q);
      W.bnext_facts g0 a;
      let n = W.bnext g0 a in
      if n = b then begin
        // the run is the single block at a, and q inside it would be a second position
        W.reaches_block_before g0 a a (U64.v q);
        assert False
      end
      else dead_run_mem g0 (mk_hp_addr n) b q
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Frames
/// ---------------------------------------------------------------------------

#push-options "--fuel 0 --ifuel 1 --z3rlimit 30"
let swept_block_frame (g0 g g': heap) (p: hp_addr) =
  W.bnext_facts g p;
  assert (read_word g' p == read_word g p);
  assert (W.bnext g' p == W.bnext g p);
  assert (W.can_step g' p == W.can_step g p)

let swept_block_frame_free (g0 g g': heap) (p: hp_addr) =
  white_header_facts (read_word g0 p);
  assert (W.bnext g' p == W.bnext g p);
  assert (W.can_step g' p == W.can_step g p)
#pop-options

/// ---------------------------------------------------------------------------
/// Opening and closing
/// ---------------------------------------------------------------------------

let sweep_inv_intro g0 g fp st = reveal_opaque (`%sweep_inv) (sweep_inv g0 g fp st)
let sweep_inv_elim g0 g fp st = reveal_opaque (`%sweep_inv) (sweep_inv g0 g fp st)

let front_same_elim g0 g c a = reveal_opaque (`%front_same) (front_same g0 g c)

let front_same_intro g0 g c pf =
  reveal_opaque (`%front_same) (front_same g0 g c);
  FStar.Classical.forall_intro (FStar.Classical.move_requires pf)

let behind_ok_elim g0 g c p = reveal_opaque (`%behind_ok) (behind_ok g0 g c)

let behind_ok_intro g0 g c pf =
  reveal_opaque (`%behind_ok) (behind_ok g0 g c);
  FStar.Classical.forall_intro (FStar.Classical.move_requires pf)

let no_adjacent_free_elim g c p q = reveal_opaque (`%no_adjacent_free) (no_adjacent_free g c)

let no_adjacent_free_intro g c pf =
  reveal_opaque (`%no_adjacent_free) (no_adjacent_free g c);
  FStar.Classical.forall_intro_2 (fun p -> FStar.Classical.move_requires (pf p))

let ends_free_elim g c b p = reveal_opaque (`%ends_free) (ends_free g c b)

let ends_free_intro g c b pf =
  reveal_opaque (`%ends_free) (ends_free g c b);
  FStar.Classical.forall_intro (FStar.Classical.move_requires pf)

let tail_ok_elim g c t = reveal_opaque (`%tail_ok) (tail_ok g c t)
let tail_ok_intro g c t = reveal_opaque (`%tail_ok) (tail_ok g c t)

/// ---------------------------------------------------------------------------
/// Cells
/// ---------------------------------------------------------------------------

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let fl_cell_iff (g: heap) (x: U64.t) =
  if is_obj x then begin
    let o : obj_addr = x in
    W.objects_mem_iff g zero_addr o;
    W.hd_address_pos o;
    color_of_object_spec o g;
    is_blue_iff o g;
    wosize_of_object_spec o g
  end
#pop-options

let wosize_at_hd (g: heap) (x: U64.t) =
  W.hd_address_pos (x <: obj_addr)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 30"
let cell_link_not_pos (g: heap) (x: U64.t) (q: nat) =
  fl_cell_iff g x;
  let p = mk_hp_addr (U64.v x - 8) in
  W.bnext_facts g p;
  if U64.v x = q then begin
    // p and q = p + 8 are both positions, but the cell at p is at least 16 bytes
    W.reaches_block_before g zero_addr p q;
    assert False
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Start
/// ---------------------------------------------------------------------------

#push-options "--fuel 0 --ifuel 1 --z3rlimit 30"
let sweep_start_inv (g0: heap) (fp: U64.t) =
  let c = U64.v zero_addr in
  W.reaches_refl g0 zero_addr;
  front_same_intro g0 g0 c (fun _ -> ());
  behind_ok_intro g0 g0 c (fun p -> W.reaches_bounds g0 zero_addr (U64.v p));
  no_adjacent_free_intro g0 c (fun p q ->
    W.reaches_bounds g0 zero_addr (U64.v p); W.bnext_facts g0 p);
  ends_free_intro g0 c false (fun p ->
    W.reaches_bounds g0 zero_addr (U64.v p); W.bnext_facts g0 p);
  let no_low (x: U64.t)
    : Lemma (requires FL.fl_cell g0 x /\ U64.v x < c) (ensures False)
    = FLA.fl_cell_facts g0 x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires no_low);
  tail_ok_intro g0 c 0UL;
  assert (prev_free g0 sweep_start == false);
  sweep_inv_intro g0 g0 fp sweep_start
#pop-options

/// ---------------------------------------------------------------------------
/// Facts at a step
/// ---------------------------------------------------------------------------

/// The cursor is a position of `g0`'s walk with room for a header, so the
/// block there fits.
#push-options "--fuel 0 --ifuel 1 --z3rlimit 30"
let g0_can_step (g0: heap) (c: hp_addr)
  : Lemma (requires sweep_g0 g0 /\ W.reaches g0 zero_addr (U64.v c) /\ U64.v c + 8 < heap_size)
          (ensures W.can_step g0 c)
  = W.reaches_end_of_dense g0;
    W.can_step_before_end g0 zero_addr c (W.walk_end g0 zero_addr)
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let sweep_inv_facts (g0 g: heap) (fp: U64.t) (st: sweep_state) =
  sweep_inv_elim g0 g fp st;
  let c : hp_addr = st.cursor in
  g0_can_step g0 c;
  front_same_elim g0 g (U64.v c) c;
  assert (W.can_step g c);
  assert (step_next g st == W.bnext g c);
  tail_ok_elim g (U64.v c) st.swept_tail;
  (if st.swept_tail <> 0UL then FLA.fl_cell_facts g st.swept_tail);
  W.bnext_facts g c;
  if prev_free g st then begin
    let p = if st.last_fragment <> 0UL then st.last_fragment else st.swept_tail in
    if st.last_fragment <> 0UL then begin
      let ph = mk_hp_addr (U64.v c - 8) in
      wosize_at_hd g st.last_fragment;
      assert (wosize_at g p == 0)
    end else begin
      FLA.fl_cell_facts g st.swept_tail;
      assert (U64.v p + wosize_at g p * 8 == U64.v c)
    end;
    // p - 8 + (wosize_at p + 1) * 8 = c, and the block at c ends by heap_size
    assert (U64.v p - 8 + (wosize_at g p + U64.v (getWosize (read_word g c)) + 2) * 8 <= heap_size);
    assert_norm (pow2 57 == pow2 54 * 8)
  end
#pop-options
