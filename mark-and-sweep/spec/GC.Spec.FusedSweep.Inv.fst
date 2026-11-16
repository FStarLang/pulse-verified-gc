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
/// Opening and closing
/// ---------------------------------------------------------------------------

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
/// Facts at a step
/// ---------------------------------------------------------------------------

#push-options "--fuel 0 --ifuel 1 --z3rlimit 30"
let dense_can_step (g: heap) (c: hp_addr) =
  W.reaches_end_of_dense g;
  W.can_step_before_end g zero_addr c (W.walk_end g zero_addr)
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let step_guards (g: heap) (fp: U64.t) (st: sweep_state) =
  W.reaches_bounds g zero_addr (U64.v st.cursor);
  let c : hp_addr = st.cursor in
  dense_can_step g c;
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
