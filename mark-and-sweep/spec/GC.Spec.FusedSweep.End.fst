module GC.Spec.FusedSweep.End

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.FusedSweep.Step

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module HeapGraph = GC.Spec.HeapGraph
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let sweep_post_elim g0 g fp = reveal_opaque (`%sweep_post) (sweep_post g0 g fp)

/// ---------------------------------------------------------------------------
/// Blocks and colours
/// ---------------------------------------------------------------------------

/// A block's colour, and the object it holds.
let obj_of (q: hp_addr{U64.v q + 8 < heap_size}) : obj_addr = f_address q

let obj_of_facts (q: hp_addr{U64.v q + 8 < heap_size})
  : Lemma (U64.v (obj_of q) == U64.v q + 8 /\ hd_address (obj_of q) == q)
  = f_address_spec q; hd_f_roundtrip q

/// The colour predicates of an object are those of its header.
let colour_of (g: heap) (x: obj_addr)
  : Lemma (let q = hd_address x in
           (is_black x g <==> black_at g q) /\ (is_blue x g <==> blue_at g q) /\
           (is_white x g <==> getColor (read_word g q) == Header.White) /\
           U64.v (wosize_of_object x g) == wz_at g q /\
           tag_of_object x g == getTag (read_word g q))
  = color_of_object_spec x g;
    is_black_iff x g; is_blue_iff x g; is_white_iff x g;
    wosize_of_object_spec x g; tag_of_object_spec x g

/// A dead run starts with a dead block.
#push-options "--fuel 1"
let dead_run_first (g0: heap) (a: hp_addr) (b: nat)
  : Lemma (requires dead_run g0 a b /\ U64.v a < b)
          (ensures W.can_step g0 a /\ not (black_at g0 a) /\ W.bnext g0 a <= b)
  = ()
#pop-options

/// The two kinds of swept block, told apart by `g0`'s colour.
let swept_cases (g0 g: heap) (p: hp_addr)
  : Lemma (requires swept_block g0 g p)
          (ensures W.can_step g p /\ W.can_step g0 p /\
                   (black_at g0 p ==> survivor g0 g p /\ W.bnext g0 p == W.bnext g p) /\
                   (not (black_at g0 p) ==> free_run g0 g p))
  = W.bnext_facts g p;
    white_header_facts (read_word g0 p);
    if black_at g0 p then begin
      if not (survivor g0 g p) then dead_run_first g0 p (W.bnext g p)
    end
    else dead_run_first g0 p (W.bnext g p)

/// ---------------------------------------------------------------------------
/// The end state
/// ---------------------------------------------------------------------------

let at_end (g0 g: heap) (fp: U64.t) (st: sweep_state) : prop =
  well_formed_heap g0 /\ sweep_g0 g0 /\ sweep_inv g0 g fp st /\ U64.v st.cursor + 8 >= heap_size

/// Every position of `g`'s walk up to the cursor is one of `g0`'s.
#push-options "--z3rlimit 40"
let rec g_pos_g0 (g0 g: heap) (c: nat) (p: nat)
  : Lemma (requires W.reaches g zero_addr c /\ behind_ok g0 g c /\
                    W.reaches g zero_addr p /\ p <= c)
          (ensures W.reaches g0 zero_addr p)
          (decreases p)
  = W.reaches_bounds g zero_addr p;
    if p = U64.v zero_addr then W.reaches_refl g0 zero_addr
    else begin
      let q = W.last_block g zero_addr p in
      behind_ok_elim g0 g c q;
      swept_cases g0 g q;
      g_pos_g0 g0 g c (U64.v q);
      if black_at g0 q then W.reaches_snoc g0 zero_addr q
      else begin
        dead_run_reaches g0 q p;
        W.reaches_trans g0 zero_addr q p
      end
    end
#pop-options

/// The objects of `g`: the blocks behind the cursor.
#push-options "--z3rlimit 40"
let obj_g (g0 g: heap) (fp: U64.t) (st: sweep_state) (x: obj_addr)
  : Lemma (requires at_end g0 g fp st)
          (ensures Seq.mem x (objects zero_addr g) <==>
                   (U64.v x >= U64.v zero_addr + 8 /\ W.reaches g zero_addr (U64.v x - 8) /\
                    U64.v x - 8 < U64.v st.cursor))
  = sweep_inv_elim g0 g fp st;
    W.objects_mem_iff g zero_addr x;
    W.hd_address_pos x;
    let c = U64.v st.cursor in
    if W.reaches g zero_addr (U64.v x - 8) then begin
      W.reaches_stuck g zero_addr c (U64.v x - 8);
      if U64.v x - 8 < c then behind_ok_elim g0 g c (hd_address x)
    end
#pop-options

/// A block of `g` is a block of `g0`, with the facts of its kind.
#push-options "--z3rlimit 40"
let block_g (g0 g: heap) (fp: U64.t) (st: sweep_state) (x: obj_addr)
  : Lemma (requires at_end g0 g fp st /\ Seq.mem x (objects zero_addr g))
          (ensures (let q = hd_address x in
                    Seq.mem x (objects zero_addr g0) /\ swept_block g0 g q /\
                    W.can_step g q /\ W.can_step g0 q /\
                    W.reaches g zero_addr (U64.v q) /\ W.reaches g0 zero_addr (U64.v q) /\
                    U64.v q < U64.v st.cursor))
  = obj_g g0 g fp st x;
    sweep_inv_elim g0 g fp st;
    W.hd_address_pos x;
    let q = hd_address x in
    behind_ok_elim g0 g (U64.v st.cursor) q;
    swept_cases g0 g q;
    g_pos_g0 g0 g (U64.v st.cursor) (U64.v q);
    W.objects_mem_iff g0 zero_addr x
#pop-options

/// A block of `g0` is behind the cursor.
#push-options "--z3rlimit 40"
let cover_q (g0 g: heap) (fp: U64.t) (st: sweep_state) (x: obj_addr)
  : Lemma (requires at_end g0 g fp st /\ Seq.mem x (objects zero_addr g0))
          (ensures (let q = hd_address x in
                    let c = U64.v st.cursor in
                    W.reaches g0 zero_addr (U64.v q) /\ W.can_step g0 q /\
                    U64.v zero_addr <= U64.v q /\ U64.v q < c /\
                    W.reaches g zero_addr c /\ behind_ok g0 g c))
  = sweep_inv_elim g0 g fp st;
    let c = U64.v st.cursor in
    W.objects_mem_iff g0 zero_addr x;
    W.hd_address_pos x;
    let q = hd_address x in
    W.reaches_stuck g0 zero_addr c (U64.v q)
#pop-options

/// ... inside a block of `g`, which is that block itself if it is a survivor,
/// and a free block covering it otherwise.
#push-options "--z3rlimit 40"
let cover_block (g0 g: heap) (fp: U64.t) (st: sweep_state) (x: obj_addr) (p: hp_addr)
  : Lemma (requires at_end g0 g fp st /\ Seq.mem x (objects zero_addr g0) /\
                    W.reaches g zero_addr (U64.v p) /\
                    U64.v p <= U64.v (hd_address x) /\ U64.v (hd_address x) < W.bnext g p /\
                    W.bnext g p <= U64.v st.cursor)
          (ensures (let q = hd_address x in
                    swept_block g0 g p /\ W.reaches g0 zero_addr (U64.v p) /\
                    (black_at g0 p ==> p == q) /\
                    (not (black_at g0 p) ==> not (black_at g0 q) /\
                                            W.bnext g0 q <= W.bnext g p)))
  = cover_q g0 g fp st x;
    let c = U64.v st.cursor in
    let q = hd_address x in
    behind_ok_elim g0 g c p;
    swept_cases g0 g p;
    g_pos_g0 g0 g c (U64.v p);
    W.reaches_det g0 zero_addr p (U64.v q);
    if black_at g0 p then begin
      if U64.v p < U64.v q then W.reaches_block_before g0 zero_addr p (U64.v q)
    end else begin
      dead_run_mem g0 p (W.bnext g p) q;
      dead_run_reaches g0 p (W.bnext g p);
      W.reaches_det g0 p q (W.bnext g p);
      W.reaches_refl g0 q;
      W.reaches_block_before g0 q q (W.bnext g p)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The clauses of `sweep_post`
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let survives_at (g0 g: heap) (fp: U64.t) (st: sweep_state) (x: obj_addr)
  : Lemma (requires at_end g0 g fp st /\ Seq.mem x (objects zero_addr g0) /\ is_black x g0)
          (ensures survives g0 g x)
  = cover_q g0 g fp st x;
    colour_of g0 x;
    let q = hd_address x in
    let p = W.block_at g zero_addr (U64.v st.cursor) (U64.v q) in
    cover_block g0 g fp st x p;
    assert (p == q);
    swept_cases g0 g q;
    W.hd_address_pos x;
    obj_g g0 g fp st x;
    colour_of g x;
    white_header_facts (read_word g0 q);
    is_no_scan_spec x g; is_no_scan_spec x g0;
    W.bnext_facts g q
#pop-options

#push-options "--z3rlimit 40"
let dead_is_free (g0 g: heap) (fp: U64.t) (st: sweep_state) (x: obj_addr)
  : Lemma (requires at_end g0 g fp st /\ Seq.mem x (objects zero_addr g) /\ ~(is_black x g0))
          (ensures is_blue x g)
  = block_g g0 g fp st x;
    colour_of g0 x;
    colour_of g x;
    swept_cases g0 g (hd_address x)
#pop-options

#push-options "--z3rlimit 40"
let not_infix_at (g0 g: heap) (fp: U64.t) (st: sweep_state) (x: obj_addr)
  : Lemma (requires at_end g0 g fp st /\ Seq.mem x (objects zero_addr g))
          (ensures ~(is_infix x g))
  = block_g g0 g fp st x;
    let q = hd_address x in
    swept_cases g0 g q;
    colour_of g0 x; colour_of g x;
    is_infix_spec x g; is_infix_spec x g0;
    white_header_facts (read_word g0 q);
    infix_tag_val ();
    wf_parts ();
    assert (~(is_infix x g0))
#pop-options

#push-options "--z3rlimit 40"
let no_adjacent_at (g0 g: heap) (fp: U64.t) (st: sweep_state) (x y: obj_addr)
  : Lemma (requires at_end g0 g fp st /\ Seq.mem x (objects zero_addr g) /\
                    Seq.mem y (objects zero_addr g) /\ is_blue x g /\ is_blue y g)
          (ensures ~(adjacent g x y))
  = block_g g0 g fp st x;
    block_g g0 g fp st y;
    colour_of g x; colour_of g y;
    W.hd_address_pos x; W.hd_address_pos y;
    sweep_inv_elim g0 g fp st;
    if U64.v x + U64.v (wosize_of_object x g) * 8 = U64.v y - 8 then
      no_adjacent_free_elim g (U64.v st.cursor) (hd_address x) (hd_address y)
#pop-options

#push-options "--z3rlimit 40"
let covered_at (g0 g: heap) (fp: U64.t) (st: sweep_state) (x: obj_addr)
  : Lemma (requires at_end g0 g fp st /\ Seq.mem x (objects zero_addr g0) /\ ~(is_black x g0))
          (ensures exists (y: obj_addr). Seq.mem y (objects zero_addr g) /\ is_blue y g /\
                                         inside g0 g x y)
  = cover_q g0 g fp st x;
    colour_of g0 x;
    let q = hd_address x in
    let c = U64.v st.cursor in
    let p = W.block_at g zero_addr c (U64.v q) in
    cover_block g0 g fp st x p;
    W.hd_address_pos x;
    if black_at g0 p then assert False
    else begin
      swept_cases g0 g p;
      assert (U64.v p + 8 < heap_size);
      let y = obj_of p in
      obj_of_facts p;
      W.reaches_bounds g zero_addr (U64.v p);
      assert (U64.v y - 8 == U64.v p);
      obj_g g0 g fp st y;
      colour_of g y;
      W.bnext_facts g p;
      W.bnext_facts g0 q;
      assert (Seq.mem y (objects zero_addr g) /\ is_blue y g /\ inside g0 g x y)
    end
#pop-options

/// A free block of the result holds only blocks that were dead.
#push-options "--z3rlimit 40"
let free_holds_dead (g0 g: heap) (fp: U64.t) (st: sweep_state) (x y: obj_addr)
  : Lemma (requires at_end g0 g fp st /\ Seq.mem y (objects zero_addr g) /\ is_blue y g /\
                    Seq.mem x (objects zero_addr g0) /\ inside g0 g x y)
          (ensures ~(is_black x g0))
  = block_g g0 g fp st y;
    colour_of g y;
    colour_of g0 x;
    let q = hd_address y in
    swept_cases g0 g q;
    white_header_facts (read_word g0 q);
    assert (free_run g0 g q);
    W.hd_address_pos x; W.hd_address_pos y;
    W.objects_mem_iff g0 zero_addr x;
    W.bnext_facts g q;
    W.reaches_det g0 zero_addr q (U64.v (hd_address x));
    dead_run_mem g0 q (W.bnext g q) (hd_address x)
#pop-options

#push-options "--z3rlimit 40"
let dense_at_end (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires at_end g0 g fp st)
          (ensures heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0)
  = sweep_inv_elim g0 g fp st;
    let c = U64.v st.cursor in
    W.reaches_end_of_dense g0;
    // the heap's first block is behind the cursor, so it can step in g
    W.reaches_refl g0 zero_addr;
    W.reaches_stuck g0 zero_addr c (U64.v zero_addr);
    W.reaches_refl g zero_addr;
    behind_ok_elim g0 g c zero_addr;
    W.dense_of_reaches_end g c
#pop-options

#push-options "--z3rlimit 60"
let sweep_done_post (g0 g: heap) (fp: U64.t) =
  eliminate exists (st: sweep_state). sweep_inv g0 g fp st /\ U64.v st.cursor + 8 >= heap_size
  with begin
    sweep_inv_elim g0 g fp st;
    dense_at_end g0 g fp st;
    let sub (x: obj_addr) : Lemma (requires Seq.mem x (objects zero_addr g))
                                  (ensures Seq.mem x (objects zero_addr g0))
      = block_g g0 g fp st x in
    FStar.Classical.forall_intro (FStar.Classical.move_requires sub);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (survives_at g0 g fp st));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (dead_is_free g0 g fp st));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (not_infix_at g0 g fp st));
    FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (no_adjacent_at g0 g fp st x));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (covered_at g0 g fp st));
    FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (free_holds_dead g0 g fp st x));
    reveal_opaque (`%sweep_post) (sweep_post g0 g fp)
  end
#pop-options

let fused_sweep_post (g0: heap) (fp: U64.t) =
  fused_sweep_done g0 fp;
  let r = fused_sweep_coalesce g0 fp in
  sweep_done_post g0 (fst r) (snd r)

/// ---------------------------------------------------------------------------
/// Consequences
/// ---------------------------------------------------------------------------

let sweep_post_white_or_blue (g0 g: heap) (fp: U64.t) (x: obj_addr) =
  sweep_post_elim g0 g fp

/// A survivor's word at `a`, inside its body.
let survivor_word (g0 g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr)
  : Lemma (requires sweep_post g0 g fp /\ Seq.mem x (objects zero_addr g0) /\ is_black x g0 /\
                    U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g0) * 8)
          (ensures read_word g a == read_word g0 a)
  = sweep_post_elim g0 g fp

#push-options "--z3rlimit 60"
let sweep_post_target (g0 g: heap) (fp: U64.t) (src dst: obj_addr) =
  sweep_post_elim g0 g fp;
  wf_parts ();
  let objs0 = objects zero_addr g0 in
  Mark.colors_exclusive src g0;
  assert (fields_constrained g0 src);
  wosize_of_object_bound src g0;
  wfh_part2_elim g0 src dst;
  wfh_part3_elim g0 src dst;
  let r = resolve_object dst g0 in
  // the target is black: not white (tri-colour), not grey, not blue
  assert (~(is_white r g0));
  assert (~(is_gray r g0));
  assert (~(is_blue r g0));
  Mark.color_exhaustive r g0;
  assert (is_black r g0);
  assert (survives g0 g r);
  if is_infix dst g0 then begin
    infix_addr_wf_elim g0 objs0 dst;
    parent_closure_addr_nat_spec dst g0;
    resolve_infix_spec dst g0;
    hd_address_spec dst;
    let a : hp_addr = hd_address dst in
    survivor_word g0 g fp r a;
    resolve_object_locality dst g g0
  end else begin
    resolve_non_infix dst g0;
    white_header_facts (read_word g0 (hd_address dst));
    tag_of_object_spec dst g; tag_of_object_spec dst g0;
    wosize_of_object_spec dst g; wosize_of_object_spec dst g0;
    is_infix_spec dst g; is_infix_spec dst g0;
    resolve_non_infix dst g
  end
#pop-options

/// `exists_field_pointing_to_unchecked` reads only the words it scans.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec efptu_congr (h1 h2: heap) (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54})
    (dst: obj_addr)
  : Lemma (requires forall (a: hp_addr).
                      U64.v a >= U64.v src /\ U64.v a + 8 <= U64.v src + U64.v wz * 8 ==>
                      read_word h1 a == read_word h2 a)
          (ensures exists_field_pointing_to_unchecked h1 src wz dst ==
                   exists_field_pointing_to_unchecked h2 src wz dst)
          (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      FStar.Math.Lemmas.pow2_plus 54 3;
      assert_norm (pow2 3 == 8);
      assert (U64.v idx * 8 < pow2 57);
      FStar.Math.Lemmas.pow2_lt_compat 64 57;
      FStar.Math.Lemmas.small_mod (U64.v idx * 8) (pow2 64);
      assert (U64.v (U64.mul_mod idx mword) == U64.v idx * 8);
      FStar.Math.Lemmas.pow2_double_sum 57;
      FStar.Math.Lemmas.pow2_lt_compat 64 58;
      FStar.Math.Lemmas.small_mod (U64.v src + U64.v idx * 8) (pow2 64);
      assert (U64.v (U64.add_mod src (U64.mul_mod idx mword)) == U64.v src + U64.v idx * 8);
      efptu_congr h1 h2 src idx dst
    end
#pop-options

/// A survivor points where it pointed.
#push-options "--z3rlimit 40"
let survivor_points_to (g0 g: heap) (fp: U64.t) (src dst: obj_addr)
  : Lemma (requires sweep_post g0 g fp /\ Seq.mem src (objects zero_addr g0) /\ is_black src g0)
          (ensures points_to g src dst == points_to g0 src dst)
  = sweep_post_elim g0 g fp;
    wosize_of_object_bound src g0;
    efptu_congr g g0 src (wosize_of_object src g0) dst
#pop-options

/// A live source of the result was a live (black) source of `g0`.
#push-options "--z3rlimit 40"
let live_source (g0 g: heap) (fp: U64.t) (src: obj_addr)
  : Lemma (requires sweep_post g0 g fp /\ Seq.mem src (objects zero_addr g) /\ ~(is_blue src g))
          (ensures Seq.mem src (objects zero_addr g0) /\ is_black src g0 /\ survives g0 g src /\
                   (fields_constrained g src == not (is_no_scan src g0)) /\
                   (fields_constrained g0 src == not (is_no_scan src g0)))
  = sweep_post_elim g0 g fp;
    Mark.colors_exclusive src g0;
    Mark.colors_exclusive src g
#pop-options

#push-options "--z3rlimit 60"
let sweep_post_wf (g0 g: heap) (fp: U64.t) =
  sweep_post_elim g0 g fp;
  wf_parts ();
  let objs = objects zero_addr g in
  let objs0 = objects zero_addr g0 in
  let p1 (h: obj_addr)
    : Lemma (Seq.mem h objs ==>
             (let wz = wosize_of_object h g in
              U64.v (hd_address h) + 8 + (U64.v wz * 8) <= Seq.length g))
    = if Seq.mem h objs then begin
        objects_member_size_bound zero_addr g h;
        wosize_of_object_spec h g
      end
  in
  FStar.Classical.forall_intro p1;
  assert (well_formed_heap_part1 g);
  assert (well_formed_heap_part4 g);
  let facts (src dst: obj_addr)
    : Lemma (requires Seq.mem src objs /\ fields_constrained g src /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
            (ensures Seq.mem (resolve_object dst g) objs /\
                     ~(is_blue (resolve_object dst g) g) /\
                     infix_addr_wf g objs dst)
    = live_source g0 g fp src;
      survivor_points_to g0 g fp src dst;
      sweep_post_target g0 g fp src dst;
      let r = resolve_object dst g0 in
      assert (survives g0 g r);
      Mark.colors_exclusive r g;
      wosize_of_object_bound src g0;
      wfh_part3_elim g0 src dst;
      if is_infix dst g0 then begin
        infix_addr_wf_elim g0 objs0 dst;
        parent_closure_addr_nat_spec dst g0;
        resolve_infix_spec dst g0;
        is_closure_spec r g; is_closure_spec r g0
      end;
      infix_addr_wf_transfer g0 g objs0 objs dst
  in
  well_formed_heap_part2_intro g (fun src dst -> facts src dst);
  well_formed_heap_part3_intro g (fun src dst -> facts src dst)
#pop-options

#push-options "--z3rlimit 40"
let sweep_post_get_field (g0 g: heap) (fp: U64.t) (x: obj_addr) (i: U64.t{U64.v i >= 1}) =
  sweep_post_elim g0 g fp;
  hd_address_spec x;
  wosize_of_object_bound x g0;
  if U64.v (hd_address x) + U64.v mword * U64.v i + U64.v mword <= heap_size then begin
    HeapGraph.get_field_addr_eq g x i;
    HeapGraph.get_field_addr_eq g0 x i
  end
#pop-options

/// A pointer field of a survivor resolves the same way in both heaps.
#push-options "--z3rlimit 60"
let survivor_field_resolve (g0 g: heap) (fp: U64.t) (b: obj_addr) (j: U64.t{U64.v j >= 1})
  : Lemma (requires sweep_post g0 g fp /\ marked g0 /\
                    Seq.mem b (objects zero_addr g0) /\ is_black b g0 /\ ~(is_no_scan b g0) /\
                    U64.v j <= U64.v (wosize_of_object b g0))
          (ensures (let v = HeapGraph.get_field g0 b j in
                    HeapGraph.get_field g b j == v /\
                    HeapGraph.resolve_field g v == HeapGraph.resolve_field g0 v))
  = sweep_post_get_field g0 g fp b j;
    let v = HeapGraph.get_field g0 b j in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let vo : obj_addr = v in
      wf_parts ();
      let wz = wosize_of_object b g0 in
      wosize_of_object_bound b g0;
      wf_object_size_bound g0 b;
      hd_address_spec b;
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      HeapGraph.get_field_addr_eq g0 b j;
      field_read_implies_exists_pointing g0 b wz (U64.sub j 1UL) vo;
      assert (points_to g0 b vo);
      sweep_post_target g0 g fp b vo
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let rec survivor_gpf_aux (g0 g: heap) (fp: U64.t) (b: obj_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma (requires sweep_post g0 g fp /\ marked g0 /\
                    Seq.mem b (objects zero_addr g0) /\ is_black b g0 /\ ~(is_no_scan b g0) /\
                    ws == wosize_of_object b g0)
          (ensures HeapGraph.get_pointer_fields_aux g b i ws ==
                   HeapGraph.get_pointer_fields_aux g0 b i ws)
          (decreases (U64.v ws - U64.v i + 1))
  = if U64.v i > U64.v ws then ()
    else begin
      survivor_field_resolve g0 g fp b i;
      if U64.v i < U64.v ws then survivor_gpf_aux g0 g fp b (U64.add i 1UL) ws
    end
#pop-options

#push-options "--z3rlimit 40"
let sweep_post_pointer_fields (g0 g: heap) (fp: U64.t) (x: obj_addr) =
  sweep_post_elim g0 g fp;
  Mark.colors_exclusive x g0;
  Mark.colors_exclusive x g;
  assert (survives g0 g x);
  if not (is_no_scan x g0) then survivor_gpf_aux g0 g fp x 1UL (wosize_of_object x g0)
#pop-options
