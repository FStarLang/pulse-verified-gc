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
module Header = GC.Lib.Header
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Heaps
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let splice_read g1 g lo hi a =
  let s = splice g1 g lo hi in
  read_word_spec s a; read_word_spec g a; read_word_spec g1 a;
  let k = U64.v a in
  let inside = lo <= k && k < hi in
  let byte (j: nat{j < 8})
    : Lemma (Seq.index s (k + j) == (if inside then Seq.index g (k + j) else Seq.index g1 (k + j)))
    = assert (k + j < heap_size);
      Seq.init_index heap_size (fun (i: nat{i < heap_size}) ->
        if lo <= i && i < hi then Seq.index g i else Seq.index g1 i)
    in
  byte 0; byte 1; byte 2; byte 3; byte 4; byte 5; byte 6; byte 7
#pop-options

#push-options "--z3rlimit 40"
let header_eta (h: U64.t)
  : Lemma (makeHeader (getWosize h) (getColor h) (getTag h) == h)
  = makeHeader_is_pack_header64 (getWosize h) (getColor h) (getTag h);
    all_headers_valid h;
    Header.unpack_pack_header (U64.v h);
    getWosize_spec h; getTag_spec h; getColor_spec h;
    Header.mask_tag_value ();
    Header.get_tag_bound (U64.v h);
    Header.get_wosize_bound (U64.v h);
    assert (U64.v (getWosize h) == Header.get_wosize (U64.v h));
    assert (U64.v (getTag h) == Header.get_tag (U64.v h))
#pop-options

let header_eq h h' = header_eta h; header_eta h'

let part1_holds g =
  let aux (h: obj_addr)
    : Lemma (requires Seq.mem h (objects zero_addr g))
            (ensures (let wz = wosize_of_object h g in
                      U64.v (hd_address h) + 8 + (U64.v wz * 8) <= Seq.length g))
    = W.objects_mem_iff g zero_addr h;
      W.hd_address_pos h;
      wosize_of_object_spec h g
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// The walk
/// ---------------------------------------------------------------------------

let no_pos_inside g p q = W.reaches_block_before g zero_addr p q

#push-options "--z3rlimit 40"
let seg_replace g g' a b =
  W.reaches_bounds g a b;
  let below (x: nat)
    : Lemma (requires x <= U64.v a)
            (ensures W.reaches g' zero_addr x <==> W.reaches g zero_addr x)
    = W.reaches_frame_below g g' zero_addr x
  in
  below (U64.v a);
  W.reaches_trans g' zero_addr a b;
  W.reaches_trans g zero_addr a b;
  let above (x: nat)
    : Lemma (requires x >= b)
            (ensures W.reaches g' zero_addr x <==> W.reaches g zero_addr x)
    = if b >= heap_size then begin
        (if W.reaches g zero_addr x then W.reaches_bounds g zero_addr x);
        (if W.reaches g' zero_addr x then W.reaches_bounds g' zero_addr x)
      end else begin
        let bb = mk_hp_addr b in
        W.walk_frame_from g g' bb;
        (if W.reaches g zero_addr x then begin
           W.reaches_det g zero_addr bb x;
           W.reaches_trans g' zero_addr bb x
         end);
        (if W.reaches g' zero_addr x then begin
           W.reaches_det g' zero_addr bb x;
           W.reaches_trans g zero_addr bb x
         end)
      end
  in
  let inside (x: nat)
    : Lemma (requires U64.v a <= x /\ x <= b)
            (ensures W.reaches g' zero_addr x <==> W.reaches g' a x)
    = (if W.reaches g' zero_addr x then W.reaches_det g' zero_addr a x);
      (if W.reaches g' a x then W.reaches_trans g' zero_addr a x)
  in
  let one (x: nat)
    : Lemma ((x <= U64.v a \/ x >= b) ==> (W.reaches g' zero_addr x <==> W.reaches g zero_addr x))
    = if x <= U64.v a then below x else if x >= b then above x
  in
  FStar.Classical.forall_intro one;
  FStar.Classical.forall_intro (FStar.Classical.move_requires inside)
#pop-options

#push-options "--z3rlimit 30"
let write_off_walk g a v
  = W.walk_write g zero_addr a v;
    let hd (q: hp_addr)
      : Lemma (requires W.reaches g zero_addr (U64.v q))
              (ensures read_word (write_word g a v) q == read_word g q)
      = read_write_different g a q v
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires hd)
#pop-options

#push-options "--z3rlimit 30"
let cells_transfer g g'
  = let aux (x: U64.t) : Lemma (FL.fl_cell g' x <==> FL.fl_cell g x)
      = fl_cell_iff g x; fl_cell_iff g' x;
        if is_obj x && U64.v x >= U64.v zero_addr + 8 then begin
          let q = mk_hp_addr (U64.v x - 8) in
          if W.reaches g zero_addr (U64.v q) then assert (read_word g' q == read_word g q)
        end
    in
    FStar.Classical.forall_intro aux
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let rec dead_run_frame_aux (g g': heap) (a: hp_addr) (b: nat)
  : Lemma (requires forall (w: hp_addr). U64.v a <= U64.v w /\ U64.v w < b ==>
                      read_word g' w == read_word g w)
          (ensures dead_run g' a b == dead_run g a b)
          (decreases (heap_size - U64.v a))
  = if U64.v a >= b then ()
    else begin
      assert (read_word g' a == read_word g a);
      if not (W.can_step g a) || black_at g a then ()
      else begin
        let n = W.bnext g a in
        if n = b || n > b || n >= heap_size then ()
        else begin
          aligned_plus_mul8 (U64.v a) (U64.v (getWosize (read_word g a)) + 1);
          W.bnext_facts g a;
          dead_run_frame_aux g g' (mk_hp_addr n) b
        end
      end
    end
#pop-options

let dead_run_frame g g' a b = dead_run_frame_aux g g' a b

/// ---------------------------------------------------------------------------
/// Swept blocks
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let dead_run_first (g1: heap) (a: hp_addr) (b: nat)
  : Lemma (requires dead_run g1 a b /\ U64.v a < b)
          (ensures W.can_step g1 a /\ not (black_at g1 a) /\ W.bnext g1 a <= b)
  = ()
#pop-options

let swept_block_kinds g1 g p =
  W.bnext_facts g p;
  white_header_facts (read_word g1 p);
  if black_at g1 p then begin
    if not (survivor g1 g p) then dead_run_first g1 p (W.bnext g p)
  end
  else dead_run_first g1 p (W.bnext g p)

#push-options "--z3rlimit 30"
let swept_block_ref_frame g1 g1' g q =
  W.bnext_facts g q;
  assert (read_word g1' q == read_word g1 q);
  if black_at g1 q && survivor g1 g q then ()
  else begin
    swept_block_kinds g1 g q;
    dead_run_frame g1 g1' q (W.bnext g q)
  end
#pop-options

#push-options "--z3rlimit 40"
let rec behind_pos_ref_aux (g1 g: heap) (c: nat) (p: nat)
  : Lemma (requires W.reaches g zero_addr c /\ behind_ok g1 g c /\
                    W.reaches g zero_addr p /\ p <= c)
          (ensures W.reaches g1 zero_addr p)
          (decreases p)
  = W.reaches_bounds g zero_addr p;
    if p = U64.v zero_addr then W.reaches_refl g1 zero_addr
    else begin
      let q = W.last_block g zero_addr p in
      behind_ok_elim g1 g c q;
      swept_block_kinds g1 g q;
      behind_pos_ref_aux g1 g c (U64.v q);
      if black_at g1 q then W.reaches_snoc g1 zero_addr q
      else begin
        dead_run_reaches g1 q p;
        W.reaches_trans g1 zero_addr q p
      end
    end
#pop-options

let behind_pos_ref g1 g c p = behind_pos_ref_aux g1 g c p

#push-options "--z3rlimit 40"
let sweeping_dense g0 g1 g fp st =
  sweep_inv_elim g1 g fp st;
  let c = U64.v st.cursor in
  W.reaches_end_of_dense g1;
  let e = W.walk_end g1 zero_addr in
  W.reaches_stuck g1 zero_addr e c;
  W.reaches_bounds g1 zero_addr c;
  W.reaches_bounds g1 zero_addr e;
  (if c < heap_size then begin
     let ca = mk_hp_addr c in
     let fr (w: hp_addr) : Lemma (requires U64.v w >= c) (ensures read_word g w == read_word g1 w)
       = front_same_elim g1 g c w in
     FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
     W.walk_frame_from g1 g ca;
     W.reaches_det g1 zero_addr ca e;
     W.reaches_trans g zero_addr ca e
   end);
  assert (W.reaches g zero_addr e);
  // the heap's first block
  (if U64.v zero_addr < c then begin
     W.reaches_refl g zero_addr;
     behind_ok_elim g1 g c zero_addr
   end else
     front_same_elim g1 g c zero_addr);
  W.dense_of_reaches_end g e
#pop-options

#push-options "--z3rlimit 40"
let live_block_ref g0 g1 g fp st p =
  sweep_inv_elim g1 g fp st;
  let c = U64.v st.cursor in
  if U64.v p >= c then front_pos g1 g c p
  else begin
    behind_ok_elim g1 g c p;
    swept_block_kinds g1 g p;
    behind_pos_ref g1 g c (U64.v p);
    white_header_facts (read_word g1 p)
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Field writes
/// ---------------------------------------------------------------------------

/// The reference heap's clauses only read its walk and the headers on it.
#push-options "--z3rlimit 40"
let ref_ok_transfer (g0 g1 g1': heap) (c: nat)
  : Lemma (requires ref_ok g0 g1 c /\
                    (forall (x: nat). W.reaches g1' zero_addr x == W.reaches g1 zero_addr x) /\
                    objects zero_addr g1' == objects zero_addr g1 /\
                    (forall (q: hp_addr). W.reaches g1 zero_addr (U64.v q) ==> read_word g1' q == read_word g1 q))
          (ensures ref_ok g0 g1' c)
  = W.reaches_end_of_dense g1;
    W.reaches_refl g1 zero_addr;
    W.dense_of_reaches_end g1' (W.walk_end g1 zero_addr);
    let p4 (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g1'))
              (ensures ~(is_infix x g1'))
      = W.objects_mem_iff g1 zero_addr x;
        W.hd_address_pos x;
        is_infix_spec x g1; is_infix_spec x g1';
        tag_of_object_spec x g1; tag_of_object_spec x g1'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires p4);
    keeps_live_intro g0 g1' (fun q -> keeps_live_elim g0 g1 q);
    no_new_garbage_intro g0 g1' (fun q -> no_new_garbage_elim g0 g1 q);
    front_carved_intro g0 g1' c (fun q -> front_carved_elim g0 g1 c q)
#pop-options

/// A cell's link word is not inside a block that is not free.
#push-options "--z3rlimit 30"
let link_not_in_live (g: heap) (x: U64.t) (p: hp_addr) (a: hp_addr)
  : Lemma (requires FL.fl_cell g x /\ pos g p /\ not (blue_at g p) /\
                    U64.v p < U64.v a /\ U64.v a < W.bnext g p)
          (ensures U64.v x <> U64.v a)
  = fl_cell_iff g x;
    let q = mk_hp_addr (U64.v x - 8) in
    W.bnext_facts g q; W.bnext_facts g p;
    if U64.v x = U64.v a then begin
      if U64.v q < U64.v p then W.reaches_block_before g zero_addr q (U64.v p)
      else W.reaches_block_before g zero_addr p (U64.v q)
    end
#pop-options

#push-options "--z3rlimit 40"
let write_at (g0 g1 g: heap) (fp: U64.t) (st: sweep_state) (a: hp_addr) (v: U64.t) (p: hp_addr)
  : Lemma (requires sweeping g0 g1 g fp st /\ pos g p /\ not (blue_at g p) /\
                    U64.v p < U64.v a /\ U64.v a < W.bnext g p)
          (ensures sweeping g0 (write_word g1 a v) (write_word g a v) fp st)
  = let g' = write_word g a v in
    let g1' = write_word g1 a v in
    let c = U64.v st.cursor in
    sweep_inv_elim g1 g fp st;
    live_block_ref g0 g1 g fp st p;
    let off (h: heap)
      : Lemma (requires pos h p /\ W.bnext h p == W.bnext g p)
              (ensures forall (x: nat). W.reaches h zero_addr x ==> x <> U64.v a)
      = let aux (x: nat) : Lemma (W.reaches h zero_addr x ==> x <> U64.v a)
          = if W.reaches h zero_addr x && x = U64.v a then no_pos_inside h p x in
        FStar.Classical.forall_intro aux
    in
    off g; off g1;
    write_off_walk g a v;
    write_off_walk g1 a v;
    read_write_same g a v; read_write_same g1 a v;
    let rd (w: hp_addr)
      : Lemma (w <> a ==> read_word g' w == read_word g w /\ read_word g1' w == read_word g1 w)
      = if w <> a then (read_write_different g a w v; read_write_different g1 a w v)
    in
    FStar.Classical.forall_intro rd;
    // the current heap's walk, cells and links
    cells_transfer g g';
    let link (x: U64.t)
      : Lemma (requires FL.fl_cell g x) (ensures FL.fl_next g' x == FL.fl_next g x)
      = FLA.fl_cell_facts g x; link_not_in_live g x p a
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires link);
    FLA.fl_ascending_transfer g g' fp;
    // in front
    front_same_intro g1' g' c (fun w -> front_same_elim g1 g c w);
    // behind
    let bh (q: hp_addr)
      : Lemma (requires W.reaches g' zero_addr (U64.v q) /\ U64.v q < c)
              (ensures swept_block g1' g' q)
      = behind_ok_elim g1 g c q;
        swept_block_kinds g1 g q;
        W.bnext_facts g q;
        if q = p then begin
          white_header_facts (read_word g1 p);
          assert (survivor g1' g' p)
        end else begin
          (if U64.v q < U64.v p then W.reaches_block_before g zero_addr q (U64.v p)
           else W.reaches_block_before g zero_addr p (U64.v q));
          swept_block_frame g1 g g' q;
          swept_block_ref_frame g1 g1' g' q
        end
    in
    behind_ok_intro g1' g' c bh;
    // no two free blocks adjacent; the block ending at the cursor
    let na (x y: hp_addr)
      : Lemma (requires W.reaches g' zero_addr (U64.v x) /\ W.can_step g' x /\
                        W.bnext g' x == U64.v y /\ U64.v y < c /\ blue_at g' x)
              (ensures not (blue_at g' y))
      = W.reaches_snoc g zero_addr x;
        no_adjacent_free_elim g c x y
    in
    no_adjacent_free_intro g' c na;
    tail_ok_elim g c st.swept_tail;
    (if st.swept_tail <> 0UL then begin
       fl_cell_iff g st.swept_tail;
       wosize_at_hd g st.swept_tail;
       wosize_at_hd g' st.swept_tail
     end);
    assert (prev_free g' st == prev_free g st);
    ends_free_intro g' c (prev_free g' st) (fun x -> ends_free_elim g c (prev_free g st) x);
    tail_ok_intro g' c st.swept_tail;
    assert (frag_ok g' c st.last_fragment);
    sweep_inv_intro g1' g' fp st;
    ref_ok_transfer g0 g1 g1' c
#pop-options

let write_sweeping g0 g1 g fp st a v =
  eliminate exists (p: hp_addr). pos g p /\ not (blue_at g p) /\ U64.v p < U64.v a /\ U64.v a < W.bnext g p
  with write_at g0 g1 g fp st a v p
