module GC.Gen.SweepPhase

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Spec.SweepPhase.Intrinsic
open GC.Gen.MinorHeap
open GC.Gen.AllocShape

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Promote = GC.Gen.Promote
module WB = GC.Gen.WriteBodyLemmas
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module Header = GC.Lib.Header
module CV = GC.Gen.CheneyView

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

let surviving_but_view_ok st obj =
  surviving_view_ok st;
  reveal_opaque (`%view_ok) view_ok

/// ---------------------------------------------------------------------------
/// The found case: the walk around the allocated block
/// ---------------------------------------------------------------------------

/// Everything the found case starts from.
let found (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) : prop =
  sweep_shape g fp st /\ FLA.fl_ascending g fp /\ FL.fl_cell g cur /\
  AC.fits_at g cur (AC.req_wz wz) /\ linked_to g fp p cur /\
  piece_ok g cur (AC.req_wz wz) pc /\
  SA.alloc_spec g fp wz tag == SA.alloc_search g fp p cur (AC.req_wz wz) SA.Idle tag 1 /\
  AC.alloc_choice g fp wz == (p, cur)

let gx_of (g: heap) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) : GTot heap =
  at_heap g p cur (AC.req_wz wz) tag pc st.cursor

/// Outside the cell's block, the walk and its headers are unchanged.
#push-options "--z3rlimit 30"
let outside_pos (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (q: hp_addr)
  : Lemma (requires found g fp st wz tag p cur pc /\ (U64.v q < U64.v pc.hd \/ U64.v q >= pc.e))
          (ensures (let gx = gx_of g st wz tag p cur pc in
                    (W.reaches gx zero_addr (U64.v q) <==> W.reaches g zero_addr (U64.v q)) /\
                    (W.reaches g zero_addr (U64.v q) ==>
                       read_word gx q == read_word g q /\ W.can_step gx q == W.can_step g q /\
                       W.bnext gx q == W.bnext g q)))
  = let w = AC.req_wz wz in
    cell_facts g fp p cur w pc;
    at_shape g fp p cur w tag pc st.cursor
#pop-options

/// Inside the cell's block, the walk has the remainder (when there is one) and
/// the new object; the old walk had only the cell.
#push-options "--z3rlimit 30"
let inside_pos (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (q: hp_addr)
  : Lemma (requires found g fp st wz tag p cur pc /\ U64.v pc.hd <= U64.v q /\ U64.v q < pc.e)
          (ensures (let gx = gx_of g st wz tag p cur pc in
                    (W.reaches gx zero_addr (U64.v q) <==>
                       ((U64.v q == U64.v pc.hd /\ pc.lo >= 1) \/ q == pc.ah)) /\
                    (W.reaches g zero_addr (U64.v q) <==> U64.v q == U64.v pc.hd)))
  = let w = AC.req_wz wz in
    cell_facts g fp p cur w pc;
    at_shape g fp p cur w tag pc st.cursor;
    if U64.v q > U64.v pc.hd && W.reaches g zero_addr (U64.v q) then no_pos_inside g pc.hd (U64.v q)
#pop-options

/// The cursor is a position of the new walk.
#push-options "--z3rlimit 30"
let found_cursor (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp st wz tag p cur pc)
          (ensures W.reaches (gx_of g st wz tag p cur pc) zero_addr (U64.v st.cursor) /\
                   (U64.v st.cursor <= U64.v pc.hd \/ U64.v st.cursor >= pc.e))
  = let w = AC.req_wz wz in
    sweep_shape_elim g fp st;
    cell_facts g fp p cur w pc;
    at_shape g fp p cur w tag pc st.cursor;
    let c = U64.v st.cursor in
    if U64.v pc.hd < c && c < pc.e then no_pos_inside g pc.hd c
#pop-options

/// The two blocks the allocation made, as walk facts of the new heap.
#push-options "--z3rlimit 30"
let found_blocks (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp st wz tag p cur pc)
          (ensures (let gx = gx_of g st wz tag p cur pc in
                    let front = U64.v pc.ah >= U64.v st.cursor in
                    pos gx pc.ah /\ W.bnext gx pc.ah == pc.e /\
                    not (blue_at gx pc.ah) /\ black_at gx pc.ah == front /\
                    white_at gx pc.ah == not front /\
                    wz_at gx pc.ah == AC.req_wz wz /\ getTag (read_word gx pc.ah) == tag /\
                    (pc.lo >= 1 ==> pos gx pc.hd /\ blue_at gx pc.hd /\ W.bnext gx pc.hd == U64.v pc.ah /\
                                   wz_at gx pc.hd == pc.lo - 1 /\ getTag (read_word gx pc.hd) == 0UL) /\
                    pos g pc.hd /\ blue_at g pc.hd /\ W.bnext g pc.hd == pc.e /\ wz_at g pc.hd >= 1))
  = let w = AC.req_wz wz in
    cell_facts g fp p cur w pc;
    at_new_blocks g fp p cur w tag pc st.cursor;
    let gx = gx_of g st wz tag p cur pc in
    header_facts w tag (if pc.lo >= 1 then pc.lo else 1);
    if U64.v pc.ah >= U64.v st.cursor then
      assert (read_word gx pc.ah == black_object_header w tag)
    else
      assert (read_word gx pc.ah == white_object_header w tag)
#pop-options

/// The new walk still covers the heap.
#push-options "--z3rlimit 20"
let found_end (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp st wz tag p cur pc)
          (ensures W.reaches (gx_of g st wz tag p cur pc) zero_addr (W.walk_end g zero_addr) /\
                   W.walk_end g zero_addr + 8 >= heap_size)
  = let w = AC.req_wz wz in
    sweep_shape_elim g fp st;
    cell_facts g fp p cur w pc;
    W.reaches_end_of_dense g;
    let e = W.walk_end g zero_addr in
    W.reaches_snoc g zero_addr pc.hd;
    W.reaches_stuck g zero_addr e pc.e;
    at_shape g fp p cur w tag pc st.cursor
#pop-options

#push-options "--z3rlimit 20"
let found_first (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp st wz tag p cur pc)
          (ensures W.can_step (gx_of g st wz tag p cur pc) zero_addr)
  = sweep_shape_elim g fp st;
    W.reaches_end_of_dense g;
    W.reaches_refl g zero_addr;
    found_blocks g fp st wz tag p cur pc;
    if U64.v zero_addr < U64.v pc.hd then outside_pos g fp st wz tag p cur pc zero_addr
    else W.reaches_bounds g zero_addr (U64.v pc.hd)
#pop-options

let found_dense (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp st wz tag p cur pc)
          (ensures (let gx = gx_of g st wz tag p cur pc in
                    heap_objects_dense gx /\ Seq.length (objects zero_addr gx) > 0))
  = found_end g fp st wz tag p cur pc;
    found_first g fp st wz tag p cur pc;
    W.dense_of_reaches_end (gx_of g st wz tag p cur pc) (W.walk_end g zero_addr)

/// Behind the cursor every block is white or free; in front none is grey.
#push-options "--z3rlimit 30"
let found_regions (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp st wz tag p cur pc)
          (ensures (let gx = gx_of g st wz tag p cur pc in
                    let c = U64.v st.cursor in
                    behind_swept gx c /\ front_unswept gx c))
  = let gx = gx_of g st wz tag p cur pc in
    let c = U64.v st.cursor in
    sweep_shape_elim g fp st;
    found_cursor g fp st wz tag p cur pc;
    found_blocks g fp st wz tag p cur pc;
    let behind (q: hp_addr)
      : Lemma (requires W.reaches gx zero_addr (U64.v q) /\ U64.v q < c)
              (ensures W.can_step gx q /\ (white_at gx q \/ blue_at gx q))
      = if U64.v q < U64.v pc.hd || U64.v q >= pc.e then begin
          outside_pos g fp st wz tag p cur pc q;
          behind_swept_elim g c q
        end else inside_pos g fp st wz tag p cur pc q
    in
    behind_swept_intro gx c behind;
    let front (q: hp_addr)
      : Lemma (requires pos gx q /\ U64.v q >= c)
              (ensures black_at gx q \/ white_at gx q \/ blue_at gx q)
      = if U64.v q < U64.v pc.hd || U64.v q >= pc.e then begin
          outside_pos g fp st wz tag p cur pc q;
          front_unswept_elim g c q
        end else inside_pos g fp st wz tag p cur pc q
    in
    front_unswept_intro gx c front
#pop-options

/// No two free blocks behind the cursor are adjacent.
#push-options "--z3rlimit 30"
let found_noadj (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp st wz tag p cur pc)
          (ensures no_adjacent_free (gx_of g st wz tag p cur pc) (U64.v st.cursor))
  = let gx = gx_of g st wz tag p cur pc in
    let c = U64.v st.cursor in
    sweep_shape_elim g fp st;
    found_blocks g fp st wz tag p cur pc;
    let na (x y: hp_addr)
      : Lemma (requires W.reaches gx zero_addr (U64.v x) /\ W.can_step gx x /\
                        W.bnext gx x == U64.v y /\ U64.v y < c /\ blue_at gx x)
              (ensures not (blue_at gx y))
      = if U64.v x < U64.v pc.hd || U64.v x >= pc.e then begin
          outside_pos g fp st wz tag p cur pc x;
          W.reaches_snoc g zero_addr x;
          W.bnext_facts g x;
          if U64.v y < U64.v pc.hd || U64.v y >= pc.e then begin
            outside_pos g fp st wz tag p cur pc y;
            no_adjacent_free_elim g c x y
          end else begin
            inside_pos g fp st wz tag p cur pc y;
            no_adjacent_free_elim g c x y
          end
        end else inside_pos g fp st wz tag p cur pc x
    in
    no_adjacent_free_intro gx c na
#pop-options

/// The new `swept_tail`.
let found_tail_eq (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp st wz tag p cur pc)
          (ensures (alloc_state g fp wz st).swept_tail ==
                   (if cur = st.swept_tail && pc.lo < 2 then p else st.swept_tail))
  = ()

/// The cells of the new heap, and the sizes of those other than the cell.
#push-options "--z3rlimit 30"
let found_cell (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (x: U64.t)
  : Lemma (requires found g fp st wz tag p cur pc)
          (ensures (let gx = gx_of g st wz tag p cur pc in
                    (FL.fl_cell gx x <==> (FL.fl_cell g x /\ (x <> cur \/ pc.lo >= 2))) /\
                    (FL.fl_cell g x /\ x <> cur ==> wosize_at gx x == wosize_at g x) /\
                    (pc.lo >= 2 ==> wosize_at gx cur == pc.lo - 1)))
  = let w = AC.req_wz wz in
    at_cells g fp p cur w tag pc st.cursor;
    if FStar.IndefiniteDescription.strong_excluded_middle (FL.fl_cell g x /\ x <> cur) then begin
      fl_cell_iff g x;
      wosize_at_hd g x;
      wosize_at_hd (gx_of g st wz tag p cur pc) x;
      let q = hd_pos x in
      if U64.v q >= U64.v pc.hd && U64.v q < pc.e then inside_pos g fp st wz tag p cur pc q
      else outside_pos g fp st wz tag p cur pc q
    end
#pop-options

/// Where the cell lies, against the sweep state.
#push-options "--z3rlimit 30"
let found_geom (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp st wz tag p cur pc)
          (ensures (let c = U64.v st.cursor in
                    let t = st.swept_tail in
                    U64.v cur == U64.v pc.hd + 8 /\ pc.e == U64.v cur + wosize_at g cur * 8 /\
                    wosize_at g cur == pc.bwz /\ pc.bwz >= 1 /\
                    U64.v pc.ah == U64.v pc.hd + pc.lo * 8 /\ U64.v pc.ah < pc.e /\
                    (p <> 0UL ==> FL.fl_cell g p /\ p <> cur /\ U64.v p + wosize_at g p * 8 <= U64.v pc.hd) /\
                    (forall (x: U64.t). FL.fl_cell g x /\ U64.v x < U64.v cur ==> p <> 0UL /\ U64.v x <= U64.v p) /\
                    (U64.v pc.hd >= c ==> cur <> t) /\
                    (pc.e <= c ==> t <> 0UL /\ U64.v cur <= U64.v t) /\
                    (pc.e == c ==> t == cur /\ st.last_fragment == 0UL) /\
                    (t <> 0UL ==> FL.fl_cell g t /\ U64.v t + wosize_at g t * 8 <= c) /\
                    (forall (x: U64.t). FL.fl_cell g x /\ U64.v x < c ==> t <> 0UL /\ U64.v x <= U64.v t)))
  = let w = AC.req_wz wz in
    let c = U64.v st.cursor in
    let t = st.swept_tail in
    sweep_shape_elim g fp st;
    cell_facts g fp p cur w pc;
    tail_ok_elim g c t;
    found_cursor g fp st wz tag p cur pc;
    (if p <> 0UL then FLA.fl_cell_facts g p);
    (if t <> 0UL then begin
       FLA.fl_cell_facts g t;
       fl_cell_iff g t;
       wosize_at_hd g t
     end);
    if pc.e = c then begin
      if U64.v t > U64.v cur then begin
        let q = hd_pos t in
        no_pos_inside g pc.hd (U64.v q)
      end;
      let f = st.last_fragment in
      if f <> 0UL then begin
        let q = prev_pos c in
        if U64.v q > U64.v pc.hd then no_pos_inside g pc.hd (U64.v q)
      end
    end
#pop-options

/// The clauses about the sweep state after allocating.
#push-options "--z3rlimit 40"
let found_state (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp st wz tag p cur pc)
          (ensures (let gx = gx_of g st wz tag p cur pc in
                    let st' = alloc_state g fp wz st in
                    let c = U64.v st.cursor in
                    ends_free gx c (prev_free gx st') /\
                    tail_ok gx c st'.swept_tail /\ frag_ok gx c st'.last_fragment))
  = let gx = gx_of g st wz tag p cur pc in
    let st' = alloc_state g fp wz st in
    let c = U64.v st.cursor in
    let t = st.swept_tail in
    let t' = st'.swept_tail in
    sweep_shape_elim g fp st;
    found_tail_eq g fp st wz tag p cur pc;
    found_geom g fp st wz tag p cur pc;
    found_cursor g fp st wz tag p cur pc;
    found_blocks g fp st wz tag p cur pc;
    found_cell g fp st wz tag p cur pc t;
    found_cell g fp st wz tag p cur pc p;
    found_cell g fp st wz tag p cur pc cur;
    // prev_free
    assert (prev_free gx st' ==
            (if pc.e = c || (cur = t && pc.e < c) then st.last_fragment <> 0UL else prev_free g st));
    // the block ending at the cursor
    let ef (x: hp_addr)
      : Lemma (requires W.reaches gx zero_addr (U64.v x) /\ W.can_step gx x /\ W.bnext gx x == c)
              (ensures blue_at gx x == prev_free gx st')
      = if U64.v x < U64.v pc.hd then begin
          outside_pos g fp st wz tag p cur pc x;
          W.reaches_snoc g zero_addr pc.hd;
          (if pc.e <= c then W.reaches_block_before g zero_addr x (U64.v pc.hd)
           else ends_free_elim g c (prev_free g st) x)
        end else if U64.v x >= pc.e then begin
          outside_pos g fp st wz tag p cur pc x;
          ends_free_elim g c (prev_free g st) x
        end else inside_pos g fp st wz tag p cur pc x
    in
    ends_free_intro gx c (prev_free gx st') ef;
    // swept_tail
    let tc (x: U64.t)
      : Lemma (requires FL.fl_cell gx x /\ U64.v x < c) (ensures t' <> 0UL /\ U64.v x <= U64.v t')
      = found_cell g fp st wz tag p cur pc x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires tc);
    tail_ok_intro gx c t';
    // last_fragment
    let f = st.last_fragment in
    if f <> 0UL then begin
      let q = prev_pos c in
      if U64.v q < U64.v pc.hd || U64.v q >= pc.e then outside_pos g fp st wz tag p cur pc q
      else inside_pos g fp st wz tag p cur pc q
    end
#pop-options

/// Object by object: outside the cell's block nothing changed; inside it, the
/// cell (free) became the remainder (free) and the new object.
#push-options "--z3rlimit 30"
let found_obj (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (x: obj_addr)
  : Lemma (requires found g fp st wz tag p cur pc)
          (ensures (let gx = gx_of g st wz tag p cur pc in
                    let q = hd_address x in
                    (q <> pc.ah ==>
                       (Seq.mem x (objects zero_addr gx) <==> Seq.mem x (objects zero_addr g))) /\
                    (q <> pc.ah /\ Seq.mem x (objects zero_addr g) ==>
                       (is_blue x gx <==> is_blue x g) /\ (is_white x gx <==> is_white x g)) /\
                    (q <> pc.ah /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) ==>
                       read_word gx q == read_word g q /\
                       (U64.v q + 8 + U64.v (wosize_of_object x g) * 8 <= U64.v pc.hd \/ U64.v q >= pc.e)) /\
                    (q == pc.ah ==> ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)))))
  = let gx = gx_of g st wz tag p cur pc in
    let q = hd_address x in
    obj_pos g x; obj_pos gx x;
    colour_of g x; colour_of gx x;
    found_blocks g fp st wz tag p cur pc;
    if U64.v q < U64.v pc.hd || U64.v q >= pc.e then begin
      outside_pos g fp st wz tag p cur pc q;
      if U64.v q < U64.v pc.hd && W.reaches g zero_addr (U64.v q) then begin
        W.reaches_snoc g zero_addr pc.hd;
        W.reaches_block_before g zero_addr q (U64.v pc.hd);
        W.bnext_facts g q
      end
    end else begin
      inside_pos g fp st wz tag p cur pc q
    end
#pop-options

/// The found case, assembled.
#push-options "--z3rlimit 30"
let found_shape (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp st wz tag p cur pc)
          (ensures (let gx = gx_of g st wz tag p cur pc in
                    let st' = alloc_state g fp wz st in
                    let obj = U64.uint_to_t (U64.v pc.ah + 8) in
                    sweep_shape gx (spec_fp g fp p cur pc) st' /\
                    (forall (x: obj_addr). condemned st' gx x == condemned st g x) /\
                    new_block g gx st obj wz tag))
  = let w = AC.req_wz wz in
    let gx = gx_of g st wz tag p cur pc in
    let st' = alloc_state g fp wz st in
    let c = U64.v st.cursor in
    sweep_shape_elim g fp st;
    found_cursor g fp st wz tag p cur pc;
    found_dense g fp st wz tag p cur pc;
    found_regions g fp st wz tag p cur pc;
    found_noadj g fp st wz tag p cur pc;
    found_state g fp st wz tag p cur pc;
    found_blocks g fp st wz tag p cur pc;
    at_list g fp wz tag st.cursor p cur pc;
    sweep_shape_intro gx (spec_fp g fp p cur pc) st';
    // the new object
    let obj = U64.uint_to_t (U64.v pc.ah + 8) in
    assert (is_obj obj /\ U64.v obj >= U64.v zero_addr + 8);
    let o : obj_addr = obj in
    hd_address_spec o;
    assert (hd_address o == pc.ah);
    obj_pos gx o; colour_of gx o;
    found_obj g fp st wz tag p cur pc o;
    // condemned
    let pd (x: obj_addr) : Lemma (condemned st' gx x == condemned st g x)
      = found_obj g fp st wz tag p cur pc x;
        if hd_address x = pc.ah then begin
          hd_address_spec x;
          assert (x == o);
          obj_pos g x; colour_of g x
        end else begin
          obj_pos g x; colour_of g x; obj_pos gx x; colour_of gx x
        end
    in
    FStar.Classical.forall_intro pd
#pop-options

/// When nothing fits, nothing changes.
#push-options "--z3rlimit 30"
let alloc_none (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t)
  : Lemma (requires FLA.fl_ascending g fp /\
                    (fst (AC.alloc_phase g fp (SA.Sweeping st) wz tag)).SA.obj_out == 0UL)
          (ensures (let r = fst (AC.alloc_phase g fp (SA.Sweeping st) wz tag) in
                    r.SA.heap_out == g /\ r.SA.fp_out == fp /\
                    snd (AC.alloc_choice g fp wz) == 0UL /\
                    (forall (t: U64.t). AC.alloc_tail g fp wz t == t)))
  = choice_facts g fp wz (SA.Sweeping st) tag;
    AC.alloc_phase_fields g fp (SA.Sweeping st) wz tag;
    let (p, cur) = AC.alloc_choice g fp wz in
    if cur <> 0UL then begin
      let w = AC.req_wz wz in
      let pc = mk_piece g cur w in
      at_explicit g fp wz tag st p cur pc
    end
#pop-options

/// The allocation at the sweep's phase, in the found case: the found context
/// and the result.
#push-options "--z3rlimit 30"
let alloc_found (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t)
  : Ghost (U64.t & U64.t & piece)
      (requires sweep_shape g fp st /\
                (fst (AC.alloc_phase g fp (SA.Sweeping st) wz tag)).SA.obj_out <> 0UL)
      (ensures fun (p, cur, pc) ->
         (let r = fst (AC.alloc_phase g fp (SA.Sweeping st) wz tag) in
          found g fp st wz tag p cur pc /\
          r.SA.heap_out == gx_of g st wz tag p cur pc /\
          r.SA.fp_out == spec_fp g fp p cur pc /\
          r.SA.obj_out == U64.uint_to_t (U64.v pc.ah + 8)))
  = sweep_shape_elim g fp st;
    let ph = SA.Sweeping st in
    choice_facts g fp wz ph tag;
    choice_facts g fp wz SA.Idle tag;
    AC.alloc_phase_idle g fp wz tag;
    AC.alloc_phase_fields g fp ph wz tag;
    let (p, cur) = AC.alloc_choice g fp wz in
    let w = AC.req_wz wz in
    let pc = mk_piece g cur w in
    at_explicit g fp wz tag st p cur pc;
    (p, cur, pc)
#pop-options

#push-options "--z3rlimit 30"
let alloc_sweep_shape g fp st wz tag =
  sweep_shape_elim g fp st;
  let r = fst (AC.alloc_phase g fp (SA.Sweeping st) wz tag) in
  if r.SA.obj_out = 0UL then alloc_none g fp st wz tag
  else begin
    let (p, cur, pc) = alloc_found g fp st wz tag in
    found_shape g fp st wz tag p cur pc
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Well-formedness across the allocation
/// ---------------------------------------------------------------------------

/// No object of the new heap is infix.
#push-options "--z3rlimit 30"
let found_part4 (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp st wz tag p cur pc /\ no_infix_block g /\ tag <> infix_tag)
          (ensures no_infix_block (gx_of g st wz tag p cur pc))
  = let gx = gx_of g st wz tag p cur pc in
    found_blocks g fp st wz tag p cur pc;
    let one (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr gx)) (ensures ~(is_infix x gx))
      = let q = hd_address x in
        obj_pos gx x; obj_pos g x;
        colour_of gx x; colour_of g x;
        is_infix_spec x gx; is_infix_spec x g;
        infix_tag_val ();
        if U64.v q < U64.v pc.hd || U64.v q >= pc.e then outside_pos g fp st wz tag p cur pc q
        else inside_pos g fp st wz tag p cur pc q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

/// A block that is not free keeps its whole block.
#push-options "--z3rlimit 30"
let found_same_block (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (x: obj_addr)
  : Lemma (requires found g fp st wz tag p cur pc /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
          (ensures same_block g (gx_of g st wz tag p cur pc) (hd_address x))
  = let w = AC.req_wz wz in
    let gx = gx_of g st wz tag p cur pc in
    let q = hd_address x in
    obj_pos g x; colour_of g x;
    found_blocks g fp st wz tag p cur pc;
    found_obj g fp st wz tag p cur pc x;
    (if q = pc.ah then begin
       // the new object's header was inside the cell's block, or was the cell
       inside_pos g fp st wz tag p cur pc q
     end);
    cell_facts g fp p cur w pc;
    at_shape g fp p cur w tag pc st.cursor;
    W.bnext_facts g q;
    let body (a: hp_addr)
      : Lemma (requires U64.v q < U64.v a /\ U64.v a < W.bnext g q)
              (ensures read_word gx a == read_word g a)
      = (if p <> 0UL then begin
           body_word g q a;
           assert (U64.v a <> U64.v p)
         end)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires body)
#pop-options

/// The surviving objects, but the new one, are those of the heap before.
#push-options "--z3rlimit 30"
let found_surviving (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (x: obj_addr)
  : Lemma (requires found g fp st wz tag p cur pc)
          (ensures (let gx = gx_of g st wz tag p cur pc in
                    let st' = alloc_state g fp wz st in
                    let obj = U64.uint_to_t (U64.v pc.ah + 8) in
                    surviving_but st' obj gx x == surviving st g x))
  = let gx = gx_of g st wz tag p cur pc in
    let st' = alloc_state g fp wz st in
    found_shape g fp st wz tag p cur pc;
    found_obj g fp st wz tag p cur pc x;
    let obj = U64.uint_to_t (U64.v pc.ah + 8) in
    let o : obj_addr = obj in
    hd_address_spec o; hd_address_spec x;
    if hd_address x = pc.ah then assert (x == o)
#pop-options

#push-options "--z3rlimit 30"
let alloc_sweep_phase g fp st wz tag =
  sweep_phase_inv_iff g fp st;
  alloc_sweep_shape g fp st wz tag;
  let r = fst (AC.alloc_phase g fp (SA.Sweeping st) wz tag) in
  if r.SA.obj_out <> 0UL then begin
    let (p, cur, pc) = alloc_found g fp st wz tag in
    let gx = gx_of g st wz tag p cur pc in
    let st' = alloc_state g fp wz st in
    let obj : obj_addr = r.SA.obj_out in
    wf_view_parts ();
    found_part4 g fp st wz tag p cur pc;
    FStar.Classical.forall_intro (found_surviving g fp st wz tag p cur pc);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (found_same_block g fp st wz tag p cur pc));
    surviving_but_view_ok st' obj;
    wf_transport g gx (surviving st) (surviving_but st' obj)
  end
#pop-options

#push-options "--z3rlimit 30"
let alloc_carved g fp st wz tag =
  let r = fst (AC.alloc_phase g fp (SA.Sweeping st) wz tag) in
  let (p, cur, pc) = alloc_found g fp st wz tag in
  let w = AC.req_wz wz in
  found_shape g fp st wz tag p cur pc;
  found_blocks g fp st wz tag p cur pc;
  cell_facts g fp p cur w pc;
  at_shape g fp p cur w tag pc st.cursor;
  let o : obj_addr = r.SA.obj_out in
  hd_address_spec o;
  assert (hd_address o == pc.ah);
  let rd (a: hp_addr)
    : Lemma (requires W.reaches g zero_addr (U64.v a) /\ (U64.v a < U64.v pc.hd \/ U64.v a >= pc.e))
            (ensures read_word r.SA.heap_out a == read_word g a)
    = outside_pos g fp st wz tag p cur pc a
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires rd);
  assert (carved_from g r.SA.heap_out pc.hd pc.ah)
#pop-options


/// ---------------------------------------------------------------------------
/// Writes into a body
/// ---------------------------------------------------------------------------

let same_heads_trans (g g' g'': heap)
  : Lemma (requires same_heads g g' /\ same_heads g' g'') (ensures same_heads g g'')
  = ()

let same_heads_refl (g: heap) : Lemma (same_heads g g) = ()

/// A word of an object's body is inside its block.
let in_body_block (g: heap) (x: obj_addr) (a: hp_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ in_body g x a)
          (ensures pos g (hd_address x) /\ U64.v (hd_address x) < U64.v a /\
                   U64.v a < W.bnext g (hd_address x))
  = obj_pos g x; colour_of g x; hd_address_spec x

/// Blocks of two different objects are disjoint.
#push-options "--z3rlimit 20"
let other_body (g: heap) (x y: obj_addr) (a: hp_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\ x <> y /\
                    in_body g x a)
          (ensures ~(U64.v (hd_address y) < U64.v a /\ U64.v a < W.bnext g (hd_address y)))
  = in_body_block g x a;
    obj_pos g y;
    hd_address_injective x y;
    let p = hd_address x in
    let q = hd_address y in
    if U64.v q < U64.v a && U64.v a < W.bnext g q then begin
      if U64.v q < U64.v p then W.reaches_block_before g zero_addr q (U64.v p)
      else W.reaches_block_before g zero_addr p (U64.v q)
    end
#pop-options

let same_heads_part4 (g g': heap)
  : Lemma (requires same_heads g g' /\ no_infix_block g)
          (ensures no_infix_block g')
  = same_heads_facts g g';
    let one (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g')) (ensures ~(is_infix x g'))
      = is_infix_spec x g; is_infix_spec x g'; colour_of g x; colour_of g' x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

#push-options "--z3rlimit 20"
let body_write_shape g fp st x a v =
  in_body_block g x a;
  colour_of g x;
  body_write g fp (hd_address x) a v;
  sweep_shape_elim g fp st;
  shape_transport g (write_word g a v) fp st;
  same_heads_facts g (write_word g a v)
#pop-options

#push-options "--z3rlimit 20"
let fresh_write g fp st obj a v =
  let g' = write_word g a v in
  body_write_shape g fp st obj a v;
  same_heads_facts g g';
  let kept (y: obj_addr)
    : Lemma (requires surviving_but st obj g y)
            (ensures same_block g g' (hd_address y))
    = other_body g obj y a;
      obj_pos g y;
      let body (b: hp_addr)
        : Lemma (requires U64.v (hd_address y) < U64.v b /\ U64.v b < W.bnext g (hd_address y))
                (ensures read_word g' b == read_word g b)
        = read_write_different g a b v
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires body)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires kept);
  wf_view_parts ();
  same_heads_part4 g g';
  surviving_but_view_ok st obj;
  wf_transport g g' (surviving_but st obj) (surviving_but st obj)
#pop-options

/// ---------------------------------------------------------------------------
/// Closing a fresh object
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let fresh_close g fp st obj =
  let v = surviving st in
  let vo = surviving_but st obj in
  wf_view_parts ();
  surviving_view_ok st;
  surviving_but_view_ok st obj;
  view_ok_elim v;
  let closure (src: obj_addr) (j: nat)
    : Lemma (requires v g src /\ ~(is_no_scan src g) /\
                      j < U64.v (wosize_of_object src g) /\ U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer w ==>
                      v g (resolve_object (w <: obj_addr) g) /\
                      infix_addr_wf g (objects zero_addr g) (w <: obj_addr)))
    = let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
      if src = obj then assert (storable v g (field_val g obj j))
      else if is_pointer w then CV.wf_view_field vo g src j
  in
  pointer_clauses_from_field_closure v g closure;
  sweep_phase_inv_iff g fp st
#pop-options

/// ---------------------------------------------------------------------------
/// Field writes
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30"
let write_sweep_phase g fp st x a v =
  let g' = write_word g a v in
  let sv = surviving st in
  sweep_phase_inv_iff g fp st;
  sweep_phase_inv_iff g' fp st;
  body_write_shape g fp st x a v;
  same_heads_facts g g';
  surviving_view_ok st;
  view_ok_elim sv;
  wf_view_parts ();
  same_heads_part4 g g';
  part1_holds g';
  // the surviving objects keep their headers, and closures their blocks
  let kept (y: obj_addr)
    : Lemma (requires sv g y)
            (ensures read_word g' (hd_address y) == read_word g (hd_address y) /\
                     (is_closure y g ==> same_block g g' (hd_address y)))
    = if is_closure y g then begin
        other_body g x y a;
        obj_pos g y;
        let body (b: hp_addr)
          : Lemma (requires U64.v (hd_address y) < U64.v b /\ U64.v b < W.bnext g (hd_address y))
                  (ensures read_word g' b == read_word g b)
          = read_write_different g a b v
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires body)
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires kept);
  assert (heads_kept sv g g');
  let closure (src: obj_addr) (j: nat)
    : Lemma (requires sv g' src /\ ~(is_no_scan src g') /\
                      j < U64.v (wosize_of_object src g') /\ U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let w = read_word g' (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer w ==>
                      sv g' (resolve_object (w <: obj_addr) g') /\
                      infix_addr_wf g' (objects zero_addr g') (w <: obj_addr)))
    = let b : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
      let w = read_word g' b in
      colour_of g src; colour_of g' src;
      is_no_scan_spec src g; is_no_scan_spec src g';
      if b = a then begin
        read_write_same g a v;
        (if src <> x then begin
           assert (in_body g' src b);
           in_body_block g' src b;
           other_body g x src a
         end);
        storable_transfer g g' sv sv v
      end else begin
        read_write_different g a b v;
        if is_pointer w then begin
          CV.wf_view_field sv g src j;
          storable_transfer g g' sv sv w
        end
      end
  in
  pointer_clauses_from_field_closure sv g' closure
#pop-options

/// ---------------------------------------------------------------------------
/// Promotion
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let minor_fields_ok_of v minor obj g =
  let one (j: nat)
    : Lemma (requires j < minor_scan_wosize minor obj)
            (ensures storable v g (minor_read_field minor obj j))
    = let w = minor_read_field minor obj j in
      if is_pointer w then begin
        GC.Gen.HeapInvariant.minor_major_fields_in_view_elim v minor g obj j;
        let t : obj_addr = w in
        view_ok_within_allocated v g t;
        assert (~(is_infix t g));
        resolve_non_infix t g;
        infix_addr_wf_non_infix g (objects zero_addr g) t
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

/// The allocation keeps every surviving object, with its block.
#push-options "--z3rlimit 30"
let alloc_keeps (g: heap) (fp: U64.t) (st: sweep_state) (wz: nat) (tag: tag_t) (y: obj_addr)
  : Lemma (requires sweep_shape g fp st /\ surviving st g y /\
                    (fst (AC.alloc_phase g fp (SA.Sweeping st) wz tag)).SA.obj_out <> 0UL)
          (ensures (let r = fst (AC.alloc_phase g fp (SA.Sweeping st) wz tag) in
                    let st' = alloc_state g fp wz st in
                    same_block g r.SA.heap_out (hd_address y) /\
                    read_word r.SA.heap_out (hd_address y) == read_word g (hd_address y) /\
                    surviving st' r.SA.heap_out y /\
                    y <> r.SA.obj_out))
  = let (p, cur, pc) = alloc_found g fp st wz tag in
    found_same_block g fp st wz tag p cur pc y;
    found_obj g fp st wz tag p cur pc y;
    (if hd_address y = pc.ah then inside_pos g fp st wz tag p cur pc pc.ah);
    found_surviving g fp st wz tag p cur pc y;
    found_shape g fp st wz tag p cur pc
#pop-options

/// The copy into a not-free object keeps the shape, the walk and the
/// headers, and keeps a fresh object fresh.
#push-options "--z3rlimit 20"
let rec copy_shape (g: heap) (fp: U64.t) (st: sweep_state) (minor: minor_state)
                   (src: U64.t) (dst: obj_addr) (i n: nat)
  : Lemma (requires sweep_shape g fp st /\ Seq.mem dst (objects zero_addr g) /\ ~(is_blue dst g) /\
                    n <= U64.v (wosize_of_object dst g))
          (ensures (let g' = WB.copy_fields minor g src dst i n in
                    sweep_shape g' fp st /\ same_heads g g' /\
                    (forall (y: obj_addr). condemned st g' y == condemned st g y) /\
                    (fresh_ok g fp st dst ==> fresh_ok g' fp st dst)))
          (decreases (n - i))
  = if i >= n then begin
      WB.copy_fields_base minor g src dst i n;
      same_heads_refl g
    end else begin
      part1_holds g;
      wfh_part1_obj_bound g dst;
      hd_address_spec dst;
      let an = U64.v dst + i * 8 in
      let a : hp_addr = U64.uint_to_t an in
      let v = minor_read_field minor src i in
      WB.copy_fields_step minor g src dst i n;
      let g1 = write_word g a v in
      body_write_shape g fp st dst a v;
      same_heads_facts g g1;
      colour_of g dst; colour_of g1 dst;
      (if FStar.IndefiniteDescription.strong_excluded_middle (fresh_ok g fp st dst)
       then fresh_write g fp st dst a v);
      copy_shape g1 fp st minor src dst (i + 1) n;
      same_heads_trans g g1 (WB.copy_fields minor g1 src dst (i + 1) n)
    end
#pop-options

#push-options "--z3rlimit 30"
let promote_sweep_shape g fp st minor obj wosize =
  let tag = Promote.promoted_tag minor obj in
  alloc_sweep_shape g fp st wosize tag;
  let r = fst (AC.alloc_phase g fp (SA.Sweeping st) wosize tag) in
  if r.SA.obj_out <> 0UL then begin
    let st' = alloc_state g fp wosize st in
    let dst : obj_addr = r.SA.obj_out in
    obj_pos r.SA.heap_out dst; colour_of r.SA.heap_out dst;
    hd_address_spec dst;
    copy_shape r.SA.heap_out r.SA.fp_out st' minor obj dst 0 wosize
  end
#pop-options

/// `same_block` composes.
let same_block_trans (g g' g'': heap) (q: hp_addr)
  : Lemma (requires same_block g g' q /\ same_block g' g'' q)
          (ensures same_block g g'' q)
  = W.bnext_facts g q; W.bnext_facts g' q

/// The copy into `dst` keeps every other object's block.
#push-options "--z3rlimit 20"
let copy_keeps (g1: heap) (minor: minor_state) (src: U64.t) (dst: obj_addr) (n: nat) (y: obj_addr)
  : Lemma (requires Seq.mem dst (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\ y <> dst /\
                    n <= U64.v (wosize_of_object dst g1))
          (ensures same_block g1 (WB.copy_fields minor g1 src dst 0 n) (hd_address y))
  = let g2 = WB.copy_fields minor g1 src dst 0 n in
    part1_holds g1;
    wfh_part1_obj_bound g1 dst;
    hd_address_spec dst;
    obj_pos g1 y;
    Promote.dst_fields_valid_from_bounds dst (if n = 0 then 1 else n);
    let body (b: hp_addr)
      : Lemma (requires U64.v (hd_address y) <= U64.v b /\ U64.v b < W.bnext g1 (hd_address y))
              (ensures read_word g2 b == read_word g1 b)
      = if n = 0 then WB.copy_fields_base minor g1 src dst 0 n
        else if U64.v b >= U64.v dst && U64.v b < U64.v dst + n * 8 then begin
          assert (in_body g1 dst b);
          (if U64.v b = U64.v (hd_address y) then begin
             in_body_block g1 dst b;
             no_pos_inside g1 (hd_address dst) (U64.v b)
           end else other_body g1 dst y b)
        end else Promote.copy_fields_frame minor g1 src dst 0 n b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires body);
    W.bnext_facts g1 (hd_address y)
#pop-options

/// The copied fields are storable.
#push-options "--z3rlimit 20"
let copy_storable_one (g g2: heap) (v v2: view) (minor: minor_state) (obj: U64.t) (dst: obj_addr)
                      (i: nat{U64.v dst + i * 8 + 8 <= heap_size})
  : Lemma (requires minor_fields_ok v minor obj g /\
                    no_infix_block g /\ no_infix_block g2 /\ view_ok v2 /\
                    heads_kept v g g2 /\ (forall (y: obj_addr). v g y ==> v2 g2 y) /\
                    i < minor_scan_wosize minor obj /\
                    field_val g2 dst i == minor_read_field minor obj i)
          (ensures storable v2 g2 (field_val g2 dst i))
  = storable_transfer g g2 v v2 (minor_read_field minor obj i)
#pop-options

#push-options "--z3rlimit 20"
let copy_storable (g g2: heap) (v v2: view) (minor: minor_state) (obj: U64.t) (dst: obj_addr)
                  (wosize: nat{wosize > 0})
  : Lemma (requires minor_fields_ok v minor obj g /\ wosize == minor_wosize minor obj /\
                    no_infix_block g /\ no_infix_block g2 /\ view_ok v2 /\
                    heads_kept v g g2 /\ (forall (y: obj_addr). v g y ==> v2 g2 y) /\
                    U64.v (wosize_of_object dst g2) == wosize /\
                    tag_of_object dst g2 == Promote.promoted_tag minor obj /\
                    (forall (j: nat). j < wosize /\ U64.v dst + j * 8 + 8 <= heap_size ==>
                       field_val g2 dst j == minor_read_field minor obj j))
          (ensures fields_storable v2 g2 dst)
  = is_no_scan_spec dst g2;
    no_scan_tag_val ();
    minor_scan_wosize_cases minor obj;
    minor_tag_bound minor obj;
    if not (is_no_scan dst g2) then begin
      assert (minor_scan_wosize minor obj == wosize);
      let sto (i: nat)
        : Lemma (i < U64.v (wosize_of_object dst g2) /\ U64.v dst + i * 8 + 8 <= heap_size ==>
                 storable v2 g2 (field_val g2 dst i))
        = if i < U64.v (wosize_of_object dst g2) && U64.v dst + i * 8 + 8 <= heap_size
          then copy_storable_one g g2 v v2 minor obj dst i
      in
      FStar.Classical.forall_intro sto
    end
#pop-options

#push-options "--z3rlimit 20"
let promote_sweep_phase g fp st minor obj wosize =
  let tag = Promote.promoted_tag minor obj in
  let sv = surviving st in
  sweep_phase_inv_iff g fp st;
  alloc_sweep_phase g fp st wosize tag;
  let r = fst (AC.alloc_phase g fp (SA.Sweeping st) wosize tag) in
  if r.SA.obj_out <> 0UL then begin
    let st' = alloc_state g fp wosize st in
    let g1 = r.SA.heap_out in
    let dst : obj_addr = r.SA.obj_out in
    obj_pos g1 dst; colour_of g1 dst;
    hd_address_spec dst;
    copy_shape g1 r.SA.fp_out st' minor obj dst 0 wosize;
    let g2 = WB.copy_fields minor g1 obj dst 0 wosize in
    same_heads_facts g1 g2;
    colour_of g2 dst;
    part1_holds g1;
    wfh_part1_obj_bound g1 dst;
    Promote.dst_fields_valid_from_obj g1 dst wosize;
    Promote.copy_fields_all_correct minor g1 obj dst wosize;
    assert (forall (j: nat). j < wosize /\ U64.v dst + j * 8 + 8 <= heap_size ==>
              field_val g2 dst j == minor_read_field minor obj j);
    let kept (y: obj_addr)
      : Lemma (requires sv g y)
              (ensures read_word g2 (hd_address y) == read_word g (hd_address y) /\
                       (is_closure y g ==> same_block g g2 (hd_address y)) /\
                       surviving st' g2 y)
      = alloc_keeps g fp st wosize tag y;
        obj_pos g1 y;
        assert (read_word g2 (hd_address y) == read_word g1 (hd_address y));
        if is_closure y g then begin
          copy_keeps g1 minor obj dst wosize y;
          same_block_trans g g1 g2 (hd_address y)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires kept);
    wf_view_parts ();
    same_heads_part4 g1 g2;
    surviving_view_ok st';
    copy_storable g g2 sv (surviving st') minor obj dst wosize;
    fresh_close g2 r.SA.fp_out st' dst
  end
#pop-options
