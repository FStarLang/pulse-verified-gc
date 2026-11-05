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
module CV = GC.Gen.CheneyGeneric

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The allocator's new block
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30"
let alloc_phase_new_block g fp c0 wz tag =
  let ph = SA.Sweeping c0 in
  let r = GC.Gen.AllocPhase.alloc_at ph g fp wz tag in
  FLA.fl_ascending_valid g fp;
  part1_holds g;
  GC.Gen.AllocPhase.alloc_at_recoloured ph g fp wz tag;
  GC.Gen.AllocPhase.alloc_at_obj_wosize ph g fp wz tag;
  if r.SA.obj_out <> 0UL then begin
    let x : obj_addr = r.SA.obj_out in
    let g' = r.SA.heap_out in
    let q = hd_address x in
    hd_address_spec x;
    obj_pos g' x; colour_of g' x;
    W.bnext_facts g' q;
    objects_addresses_gt_start zero_addr g' x;
    // the object was not a non-free block: the list holds only cells
    (if FStar.IndefiniteDescription.strong_excluded_middle
          (Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) then begin
       fl_cell_iff g x; obj_pos g x; colour_of g x;
       FLA.fl_ascending_avoids g fp x heap_words;
       GC.Gen.AllocPhase.alloc_at_obj_ne_excl ph g fp wz x tag
     end);
    assert (is_white x g' ==> U64.v q < U64.v c0)
  end
#pop-options

let free_or_uninitialised_ok c0 obj =
  free_incremental_ok c0;
  reveal_opaque (`%free_def_ok) free_def_ok

/// ---------------------------------------------------------------------------
/// The found case: the walk around the allocated block
/// ---------------------------------------------------------------------------

/// Everything the found case starts from.
let found (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) : prop =
  sweep_shape g fp c0 /\ FLA.fl_ascending g fp /\ FL.fl_cell g cur /\
  AC.fits_at g cur (AC.req_wz wz) /\ linked_to g fp p cur /\
  piece_ok g cur (AC.req_wz wz) pc /\
  SA.alloc_spec g fp wz tag == SA.alloc_search g fp p cur (AC.req_wz wz) SA.Idle tag 1 /\
  AC.alloc_choice g fp wz == (p, cur)

let gx_of (g: heap) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) : GTot heap =
  at_heap g p cur (AC.req_wz wz) tag pc c0

/// Outside the cell's block, the walk and its headers are unchanged.
#push-options "--z3rlimit 30"
let outside_pos (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (q: hp_addr)
  : Lemma (requires found g fp c0 wz tag p cur pc /\ (U64.v q < U64.v pc.hd \/ U64.v q >= pc.e))
          (ensures (let gx = gx_of g c0 wz tag p cur pc in
                    (W.reaches gx zero_addr (U64.v q) <==> W.reaches g zero_addr (U64.v q)) /\
                    (W.reaches g zero_addr (U64.v q) ==>
                       read_word gx q == read_word g q /\ W.can_step gx q == W.can_step g q /\
                       W.bnext gx q == W.bnext g q)))
  = let w = AC.req_wz wz in
    cell_facts g fp p cur w pc;
    at_shape g fp p cur w tag pc c0
#pop-options

/// Inside the cell's block, the walk has the remainder (when there is one) and
/// the new object; the old walk had only the cell.
#push-options "--z3rlimit 30"
let inside_pos (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (q: hp_addr)
  : Lemma (requires found g fp c0 wz tag p cur pc /\ U64.v pc.hd <= U64.v q /\ U64.v q < pc.e)
          (ensures (let gx = gx_of g c0 wz tag p cur pc in
                    (W.reaches gx zero_addr (U64.v q) <==>
                       ((U64.v q == U64.v pc.hd /\ pc.lo >= 1) \/ q == pc.ah)) /\
                    (W.reaches g zero_addr (U64.v q) <==> U64.v q == U64.v pc.hd)))
  = let w = AC.req_wz wz in
    cell_facts g fp p cur w pc;
    at_shape g fp p cur w tag pc c0;
    if U64.v q > U64.v pc.hd && W.reaches g zero_addr (U64.v q) then no_pos_inside g pc.hd (U64.v q)
#pop-options

/// The cursor is a position of the new walk.
#push-options "--z3rlimit 30"
let found_cursor (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp c0 wz tag p cur pc)
          (ensures W.reaches (gx_of g c0 wz tag p cur pc) zero_addr (U64.v c0) /\
                   (U64.v c0 <= U64.v pc.hd \/ U64.v c0 >= pc.e))
  = let w = AC.req_wz wz in
    sweep_shape_elim g fp c0;
    cell_facts g fp p cur w pc;
    at_shape g fp p cur w tag pc c0;
    let c = U64.v c0 in
    if U64.v pc.hd < c && c < pc.e then no_pos_inside g pc.hd c
#pop-options

/// The two blocks the allocation made, as walk facts of the new heap.
#push-options "--z3rlimit 30"
let found_blocks (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp c0 wz tag p cur pc)
          (ensures (let gx = gx_of g c0 wz tag p cur pc in
                    let front = U64.v pc.ah >= U64.v c0 in
                    pos gx pc.ah /\ W.bnext gx pc.ah == pc.e /\
                    not (blue_at gx pc.ah) /\ black_at gx pc.ah == front /\
                    white_at gx pc.ah == not front /\
                    wz_at gx pc.ah == AC.req_wz wz /\ getTag (read_word gx pc.ah) == tag /\
                    (pc.lo >= 1 ==> pos gx pc.hd /\ blue_at gx pc.hd /\ W.bnext gx pc.hd == U64.v pc.ah /\
                                   wz_at gx pc.hd == pc.lo - 1 /\ getTag (read_word gx pc.hd) == 0UL) /\
                    pos g pc.hd /\ blue_at g pc.hd /\ W.bnext g pc.hd == pc.e /\ wz_at g pc.hd >= 1))
  = let w = AC.req_wz wz in
    cell_facts g fp p cur w pc;
    at_new_blocks g fp p cur w tag pc c0;
    let gx = gx_of g c0 wz tag p cur pc in
    header_facts w tag (if pc.lo >= 1 then pc.lo else 1);
    if U64.v pc.ah >= U64.v c0 then
      assert (read_word gx pc.ah == black_object_header w tag)
    else
      assert (read_word gx pc.ah == white_object_header w tag)
#pop-options

/// The new walk still covers the heap.
#push-options "--z3rlimit 20"
let found_end (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp c0 wz tag p cur pc)
          (ensures W.reaches (gx_of g c0 wz tag p cur pc) zero_addr (W.walk_end g zero_addr) /\
                   W.walk_end g zero_addr + 8 >= heap_size)
  = let w = AC.req_wz wz in
    sweep_shape_elim g fp c0;
    cell_facts g fp p cur w pc;
    W.reaches_end_of_dense g;
    let e = W.walk_end g zero_addr in
    W.reaches_snoc g zero_addr pc.hd;
    W.reaches_stuck g zero_addr e pc.e;
    at_shape g fp p cur w tag pc c0
#pop-options

#push-options "--z3rlimit 20"
let found_first (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp c0 wz tag p cur pc)
          (ensures W.can_step (gx_of g c0 wz tag p cur pc) zero_addr)
  = sweep_shape_elim g fp c0;
    W.reaches_end_of_dense g;
    W.reaches_refl g zero_addr;
    found_blocks g fp c0 wz tag p cur pc;
    if U64.v zero_addr < U64.v pc.hd then outside_pos g fp c0 wz tag p cur pc zero_addr
    else W.reaches_bounds g zero_addr (U64.v pc.hd)
#pop-options

let found_dense (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp c0 wz tag p cur pc)
          (ensures (let gx = gx_of g c0 wz tag p cur pc in
                    heap_objects_dense gx /\ Seq.length (objects zero_addr gx) > 0))
  = found_end g fp c0 wz tag p cur pc;
    found_first g fp c0 wz tag p cur pc;
    W.dense_of_reaches_end (gx_of g c0 wz tag p cur pc) (W.walk_end g zero_addr)

/// Behind the cursor every block is white or free; in front none is grey.
#push-options "--z3rlimit 30"
let found_regions (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp c0 wz tag p cur pc)
          (ensures (let gx = gx_of g c0 wz tag p cur pc in
                    let c = U64.v c0 in
                    behind_swept gx c /\ front_unswept gx c))
  = let gx = gx_of g c0 wz tag p cur pc in
    let c = U64.v c0 in
    sweep_shape_elim g fp c0;
    found_cursor g fp c0 wz tag p cur pc;
    found_blocks g fp c0 wz tag p cur pc;
    let behind (q: hp_addr)
      : Lemma (requires W.reaches gx zero_addr (U64.v q) /\ U64.v q < c)
              (ensures W.can_step gx q /\ (white_at gx q \/ blue_at gx q))
      = if U64.v q < U64.v pc.hd || U64.v q >= pc.e then begin
          outside_pos g fp c0 wz tag p cur pc q;
          behind_swept_elim g c q
        end else inside_pos g fp c0 wz tag p cur pc q
    in
    behind_swept_intro gx c behind;
    let front (q: hp_addr)
      : Lemma (requires pos gx q /\ U64.v q >= c)
              (ensures black_at gx q \/ white_at gx q \/ blue_at gx q)
      = if U64.v q < U64.v pc.hd || U64.v q >= pc.e then begin
          outside_pos g fp c0 wz tag p cur pc q;
          front_unswept_elim g c q
        end else inside_pos g fp c0 wz tag p cur pc q
    in
    front_unswept_intro gx c front
#pop-options

/// No two free blocks behind the cursor are adjacent.
#push-options "--z3rlimit 30"
let found_noadj (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp c0 wz tag p cur pc)
          (ensures no_adjacent_free (gx_of g c0 wz tag p cur pc) (U64.v c0))
  = let gx = gx_of g c0 wz tag p cur pc in
    let c = U64.v c0 in
    sweep_shape_elim g fp c0;
    found_blocks g fp c0 wz tag p cur pc;
    let na (x y: hp_addr)
      : Lemma (requires W.reaches gx zero_addr (U64.v x) /\ W.can_step gx x /\
                        W.bnext gx x == U64.v y /\ U64.v y < c /\ blue_at gx x)
              (ensures not (blue_at gx y))
      = if U64.v x < U64.v pc.hd || U64.v x >= pc.e then begin
          outside_pos g fp c0 wz tag p cur pc x;
          W.reaches_snoc g zero_addr x;
          W.bnext_facts g x;
          if U64.v y < U64.v pc.hd || U64.v y >= pc.e then begin
            outside_pos g fp c0 wz tag p cur pc y;
            no_adjacent_free_elim g c x y
          end else begin
            inside_pos g fp c0 wz tag p cur pc y;
            no_adjacent_free_elim g c x y
          end
        end else inside_pos g fp c0 wz tag p cur pc x
    in
    no_adjacent_free_intro gx c na
#pop-options

/// Object by object: outside the cell's block nothing changed; inside it, the
/// cell (free) became the remainder (free) and the new object.
#push-options "--z3rlimit 30"
let found_obj (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (x: obj_addr)
  : Lemma (requires found g fp c0 wz tag p cur pc)
          (ensures (let gx = gx_of g c0 wz tag p cur pc in
                    let q = hd_address x in
                    (q <> pc.ah ==>
                       (Seq.mem x (objects zero_addr gx) <==> Seq.mem x (objects zero_addr g))) /\
                    (q <> pc.ah /\ Seq.mem x (objects zero_addr g) ==>
                       (is_blue x gx <==> is_blue x g) /\ (is_white x gx <==> is_white x g)) /\
                    (q <> pc.ah /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) ==>
                       read_word gx q == read_word g q /\
                       (U64.v q + 8 + U64.v (wosize_of_object x g) * 8 <= U64.v pc.hd \/ U64.v q >= pc.e)) /\
                    (q == pc.ah ==> ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)))))
  = let gx = gx_of g c0 wz tag p cur pc in
    let q = hd_address x in
    obj_pos g x; obj_pos gx x;
    colour_of g x; colour_of gx x;
    found_blocks g fp c0 wz tag p cur pc;
    if U64.v q < U64.v pc.hd || U64.v q >= pc.e then begin
      outside_pos g fp c0 wz tag p cur pc q;
      if U64.v q < U64.v pc.hd && W.reaches g zero_addr (U64.v q) then begin
        W.reaches_snoc g zero_addr pc.hd;
        W.reaches_block_before g zero_addr q (U64.v pc.hd);
        W.bnext_facts g q
      end
    end else begin
      inside_pos g fp c0 wz tag p cur pc q
    end
#pop-options

/// The found case, assembled.
#push-options "--z3rlimit 30"
let found_shape (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp c0 wz tag p cur pc)
          (ensures (let gx = gx_of g c0 wz tag p cur pc in
                    let obj = U64.uint_to_t (U64.v pc.ah + 8) in
                    sweep_shape gx (spec_fp g fp p cur pc) c0 /\
                    (forall (x: obj_addr). pending_free c0 gx x == pending_free c0 g x) /\
                    new_block g gx c0 obj wz tag))
  = let w = AC.req_wz wz in
    let gx = gx_of g c0 wz tag p cur pc in
    let c = U64.v c0 in
    sweep_shape_elim g fp c0;
    found_cursor g fp c0 wz tag p cur pc;
    found_dense g fp c0 wz tag p cur pc;
    found_regions g fp c0 wz tag p cur pc;
    found_noadj g fp c0 wz tag p cur pc;
    found_blocks g fp c0 wz tag p cur pc;
    at_list g fp wz tag c0 p cur pc;
    sweep_shape_intro gx (spec_fp g fp p cur pc) c0;
    // the new object
    let obj = U64.uint_to_t (U64.v pc.ah + 8) in
    assert (is_obj obj /\ U64.v obj >= U64.v zero_addr + 8);
    let o : obj_addr = obj in
    hd_address_spec o;
    assert (hd_address o == pc.ah);
    obj_pos gx o; colour_of gx o;
    found_obj g fp c0 wz tag p cur pc o;
    // pending free
    let pd (x: obj_addr) : Lemma (pending_free c0 gx x == pending_free c0 g x)
      = found_obj g fp c0 wz tag p cur pc x;
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
let alloc_none (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t)
  : Lemma (requires FLA.fl_ascending g fp /\
                    (AC.alloc_phase g fp (SA.Sweeping c0) wz tag).SA.obj_out == 0UL)
          (ensures (let r = AC.alloc_phase g fp (SA.Sweeping c0) wz tag in
                    r.SA.heap_out == g /\ r.SA.fp_out == fp /\
                    snd (AC.alloc_choice g fp wz) == 0UL))
  = choice_facts g fp wz (SA.Sweeping c0) tag;
    AC.alloc_phase_fields g fp (SA.Sweeping c0) wz tag;
    let (p, cur) = AC.alloc_choice g fp wz in
    if cur <> 0UL then begin
      let w = AC.req_wz wz in
      let pc = mk_piece g cur w in
      at_explicit g fp wz tag c0 p cur pc
    end
#pop-options

/// The allocation at the sweep's phase, in the found case: the found context
/// and the result.
#push-options "--z3rlimit 30"
let alloc_found (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t)
  : Ghost (U64.t & U64.t & piece)
      (requires sweep_shape g fp c0 /\
                (AC.alloc_phase g fp (SA.Sweeping c0) wz tag).SA.obj_out <> 0UL)
      (ensures fun (p, cur, pc) ->
         (let r = AC.alloc_phase g fp (SA.Sweeping c0) wz tag in
          found g fp c0 wz tag p cur pc /\
          r.SA.heap_out == gx_of g c0 wz tag p cur pc /\
          r.SA.fp_out == spec_fp g fp p cur pc /\
          r.SA.obj_out == U64.uint_to_t (U64.v pc.ah + 8)))
  = sweep_shape_elim g fp c0;
    let ph = SA.Sweeping c0 in
    choice_facts g fp wz ph tag;
    choice_facts g fp wz SA.Idle tag;
    AC.alloc_phase_idle g fp wz tag;
    AC.alloc_phase_fields g fp ph wz tag;
    let (p, cur) = AC.alloc_choice g fp wz in
    let w = AC.req_wz wz in
    let pc = mk_piece g cur w in
    at_explicit g fp wz tag c0 p cur pc;
    (p, cur, pc)
#pop-options

#push-options "--z3rlimit 30"
let alloc_sweep_shape g fp c0 wz tag =
  sweep_shape_elim g fp c0;
  let r = AC.alloc_phase g fp (SA.Sweeping c0) wz tag in
  if r.SA.obj_out = 0UL then alloc_none g fp c0 wz tag
  else begin
    let (p, cur, pc) = alloc_found g fp c0 wz tag in
    found_shape g fp c0 wz tag p cur pc
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Well-formedness across the allocation
/// ---------------------------------------------------------------------------

/// No object of the new heap is infix.
#push-options "--z3rlimit 30"
let found_part4 (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece)
  : Lemma (requires found g fp c0 wz tag p cur pc /\ no_infix_block g /\ tag <> infix_tag)
          (ensures no_infix_block (gx_of g c0 wz tag p cur pc))
  = let gx = gx_of g c0 wz tag p cur pc in
    found_blocks g fp c0 wz tag p cur pc;
    let one (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr gx)) (ensures ~(is_infix x gx))
      = let q = hd_address x in
        obj_pos gx x; obj_pos g x;
        colour_of gx x; colour_of g x;
        is_infix_spec x gx; is_infix_spec x g;
        infix_tag_val ();
        if U64.v q < U64.v pc.hd || U64.v q >= pc.e then outside_pos g fp c0 wz tag p cur pc q
        else inside_pos g fp c0 wz tag p cur pc q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

/// A block that is not free keeps its whole block.
#push-options "--z3rlimit 30"
let found_same_block (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (x: obj_addr)
  : Lemma (requires found g fp c0 wz tag p cur pc /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
          (ensures same_block g (gx_of g c0 wz tag p cur pc) (hd_address x))
  = let w = AC.req_wz wz in
    let gx = gx_of g c0 wz tag p cur pc in
    let q = hd_address x in
    obj_pos g x; colour_of g x;
    found_blocks g fp c0 wz tag p cur pc;
    found_obj g fp c0 wz tag p cur pc x;
    (if q = pc.ah then begin
       // the new object's header was inside the cell's block, or was the cell
       inside_pos g fp c0 wz tag p cur pc q
     end);
    cell_facts g fp p cur w pc;
    at_shape g fp p cur w tag pc c0;
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

/// The non-free objects, but the new one, are those of the heap before.
#push-options "--z3rlimit 30"
let found_in_use (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (p cur: U64.t) (pc: piece) (x: obj_addr)
  : Lemma (requires found g fp c0 wz tag p cur pc)
          (ensures (let gx = gx_of g c0 wz tag p cur pc in
                    let obj = U64.uint_to_t (U64.v pc.ah + 8) in
                    in_use (free_or_uninitialised c0 obj) gx x == in_use (free_incremental c0) g x))
  = let gx = gx_of g c0 wz tag p cur pc in
    found_shape g fp c0 wz tag p cur pc;
    found_obj g fp c0 wz tag p cur pc x;
    let obj = U64.uint_to_t (U64.v pc.ah + 8) in
    let o : obj_addr = obj in
    hd_address_spec o; hd_address_spec x;
    if hd_address x = pc.ah then assert (x == o)
#pop-options

#push-options "--z3rlimit 30"
let alloc_sweep_phase g fp c0 wz tag =
  sweep_inv_incremental_iff g fp c0;
  alloc_sweep_shape g fp c0 wz tag;
  let r = AC.alloc_phase g fp (SA.Sweeping c0) wz tag in
  if r.SA.obj_out <> 0UL then begin
    let (p, cur, pc) = alloc_found g fp c0 wz tag in
    let gx = gx_of g c0 wz tag p cur pc in
    let obj : obj_addr = r.SA.obj_out in
    wf_with_parts ();
    found_part4 g fp c0 wz tag p cur pc;
    FStar.Classical.forall_intro (found_in_use g fp c0 wz tag p cur pc);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (found_same_block g fp c0 wz tag p cur pc));
    free_or_uninitialised_ok c0 obj;
    wf_transport g gx (free_incremental c0) (free_or_uninitialised c0 obj)
  end
#pop-options

#push-options "--z3rlimit 30"
let alloc_carved g fp c0 wz tag =
  let r = AC.alloc_phase g fp (SA.Sweeping c0) wz tag in
  let (p, cur, pc) = alloc_found g fp c0 wz tag in
  let w = AC.req_wz wz in
  found_shape g fp c0 wz tag p cur pc;
  found_blocks g fp c0 wz tag p cur pc;
  cell_facts g fp p cur w pc;
  at_shape g fp p cur w tag pc c0;
  let o : obj_addr = r.SA.obj_out in
  hd_address_spec o;
  assert (hd_address o == pc.ah);
  let rd (a: hp_addr)
    : Lemma (requires W.reaches g zero_addr (U64.v a) /\ (U64.v a < U64.v pc.hd \/ U64.v a >= pc.e))
            (ensures read_word r.SA.heap_out a == read_word g a)
    = outside_pos g fp c0 wz tag p cur pc a
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
let body_write_shape g fp c0 x a v =
  in_body_block g x a;
  colour_of g x;
  body_write g fp (hd_address x) a v;
  sweep_shape_elim g fp c0;
  shape_transport g (write_word g a v) fp c0;
  same_heads_facts g (write_word g a v)
#pop-options

#push-options "--z3rlimit 20"
let fresh_write g fp c0 obj a v =
  let g' = write_word g a v in
  body_write_shape g fp c0 obj a v;
  same_heads_facts g g';
  let kept (y: obj_addr)
    : Lemma (requires in_use (free_or_uninitialised c0 obj) g y)
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
  wf_with_parts ();
  same_heads_part4 g g';
  free_or_uninitialised_ok c0 obj;
  wf_transport g g' (free_or_uninitialised c0 obj) (free_or_uninitialised c0 obj)
#pop-options

/// ---------------------------------------------------------------------------
/// Closing a fresh object
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let fresh_close g fp c0 obj =
  let free = free_incremental c0 in
  let fresh_free = free_or_uninitialised c0 obj in
  wf_with_parts ();
  free_incremental_ok c0;
  free_or_uninitialised_ok c0 obj;
  free_def_ok_elim free;
  let closure (src: obj_addr) (j: nat)
    : Lemma (requires in_use free g src /\ ~(is_no_scan src g) /\
                      j < U64.v (wosize_of_object src g) /\ U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer w ==>
                      in_use free g (resolve_object (w <: obj_addr) g) /\
                      infix_addr_wf g (objects zero_addr g) (w <: obj_addr)))
    = let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
      if src = obj then assert (storable free g (field_val g obj j))
      else if is_pointer w then CV.wf_with_field fresh_free g src j
  in
  pointer_clauses_from_field_closure free g closure;
  sweep_inv_incremental_iff g fp c0
#pop-options

/// ---------------------------------------------------------------------------
/// Field writes
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30"
let write_sweep_phase g fp c0 x a v =
  let g' = write_word g a v in
  let free = free_incremental c0 in
  sweep_inv_incremental_iff g fp c0;
  sweep_inv_incremental_iff g' fp c0;
  body_write_shape g fp c0 x a v;
  same_heads_facts g g';
  free_incremental_ok c0;
  free_def_ok_elim free;
  wf_with_parts ();
  same_heads_part4 g g';
  part1_holds g';
  // the non-free objects keep their headers, and closures their blocks
  let kept (y: obj_addr)
    : Lemma (requires in_use free g y)
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
  assert (heads_kept free g g');
  let closure (src: obj_addr) (j: nat)
    : Lemma (requires in_use free g' src /\ ~(is_no_scan src g') /\
                      j < U64.v (wosize_of_object src g') /\ U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let w = read_word g' (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer w ==>
                      in_use free g' (resolve_object (w <: obj_addr) g') /\
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
        storable_transfer g g' free free v
      end else begin
        read_write_different g a b v;
        if is_pointer w then begin
          CV.wf_with_field free g src j;
          storable_transfer g g' free free w
        end
      end
  in
  pointer_clauses_from_field_closure free g' closure
#pop-options

/// ---------------------------------------------------------------------------
/// Promotion
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let minor_fields_ok_of free minor obj g =
  let one (j: nat)
    : Lemma (requires j < minor_scan_wosize minor obj)
            (ensures storable free g (minor_read_field minor obj j))
    = let w = minor_read_field minor obj j in
      if is_pointer w then begin
        GC.Gen.HeapInvariant.minor_major_fields_not_free_elim free minor g obj j;
        let t : obj_addr = w in
        in_use_not_blue free g t;
        assert (~(is_infix t g));
        resolve_non_infix t g;
        infix_addr_wf_non_infix g (objects zero_addr g) t
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

/// The allocation keeps every non-free object, with its block.
#push-options "--z3rlimit 30"
let alloc_keeps (g: heap) (fp: U64.t) (c0: U64.t) (wz: nat) (tag: tag_t) (y: obj_addr)
  : Lemma (requires sweep_shape g fp c0 /\ in_use (free_incremental c0) g y /\
                    (AC.alloc_phase g fp (SA.Sweeping c0) wz tag).SA.obj_out <> 0UL)
          (ensures (let r = AC.alloc_phase g fp (SA.Sweeping c0) wz tag in
                    same_block g r.SA.heap_out (hd_address y) /\
                    read_word r.SA.heap_out (hd_address y) == read_word g (hd_address y) /\
                    in_use (free_incremental c0) r.SA.heap_out y /\
                    y <> r.SA.obj_out))
  = let (p, cur, pc) = alloc_found g fp c0 wz tag in
    found_same_block g fp c0 wz tag p cur pc y;
    found_obj g fp c0 wz tag p cur pc y;
    (if hd_address y = pc.ah then inside_pos g fp c0 wz tag p cur pc pc.ah);
    found_in_use g fp c0 wz tag p cur pc y;
    found_shape g fp c0 wz tag p cur pc
#pop-options

/// The copy into a non-blue object keeps the shape, the walk and the
/// headers, and keeps a fresh object fresh.
#push-options "--z3rlimit 20"
let rec copy_shape (g: heap) (fp: U64.t) (c0: U64.t) (minor: minor_state)
                   (src: U64.t) (dst: obj_addr) (i n: nat)
  : Lemma (requires sweep_shape g fp c0 /\ Seq.mem dst (objects zero_addr g) /\ ~(is_blue dst g) /\
                    n <= U64.v (wosize_of_object dst g))
          (ensures (let g' = WB.copy_fields minor g src dst i n in
                    sweep_shape g' fp c0 /\ same_heads g g' /\
                    (forall (y: obj_addr). pending_free c0 g' y == pending_free c0 g y) /\
                    (fresh_ok g fp c0 dst ==> fresh_ok g' fp c0 dst)))
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
      body_write_shape g fp c0 dst a v;
      same_heads_facts g g1;
      colour_of g dst; colour_of g1 dst;
      (if FStar.IndefiniteDescription.strong_excluded_middle (fresh_ok g fp c0 dst)
       then fresh_write g fp c0 dst a v);
      copy_shape g1 fp c0 minor src dst (i + 1) n;
      same_heads_trans g g1 (WB.copy_fields minor g1 src dst (i + 1) n)
    end
#pop-options

#push-options "--z3rlimit 30"
let promote_sweep_shape g fp c0 minor obj wosize =
  let tag = Promote.promoted_tag minor obj in
  alloc_sweep_shape g fp c0 wosize tag;
  let r = AC.alloc_phase g fp (SA.Sweeping c0) wosize tag in
  if r.SA.obj_out <> 0UL then begin
    let dst : obj_addr = r.SA.obj_out in
    obj_pos r.SA.heap_out dst; colour_of r.SA.heap_out dst;
    hd_address_spec dst;
    copy_shape r.SA.heap_out r.SA.fp_out c0 minor obj dst 0 wosize
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
let copy_storable_one (g g2: heap) (free free2: free_def) (minor: minor_state) (obj: U64.t) (dst: obj_addr)
                      (i: nat{U64.v dst + i * 8 + 8 <= heap_size})
  : Lemma (requires minor_fields_ok free minor obj g /\
                    no_infix_block g /\ no_infix_block g2 /\ free_def_ok free2 /\
                    heads_kept free g g2 /\ (forall (y: obj_addr). in_use free g y ==> in_use free2 g2 y) /\
                    i < minor_scan_wosize minor obj /\
                    field_val g2 dst i == minor_read_field minor obj i)
          (ensures storable free2 g2 (field_val g2 dst i))
  = storable_transfer g g2 free free2 (minor_read_field minor obj i)
#pop-options

#push-options "--z3rlimit 20"
let copy_storable (g g2: heap) (free free2: free_def) (minor: minor_state) (obj: U64.t) (dst: obj_addr)
                  (wosize: nat{wosize > 0})
  : Lemma (requires minor_fields_ok free minor obj g /\ wosize == minor_wosize minor obj /\
                    no_infix_block g /\ no_infix_block g2 /\ free_def_ok free2 /\
                    heads_kept free g g2 /\ (forall (y: obj_addr). in_use free g y ==> in_use free2 g2 y) /\
                    U64.v (wosize_of_object dst g2) == wosize /\
                    tag_of_object dst g2 == Promote.promoted_tag minor obj /\
                    (forall (j: nat). j < wosize /\ U64.v dst + j * 8 + 8 <= heap_size ==>
                       field_val g2 dst j == minor_read_field minor obj j))
          (ensures fields_storable free2 g2 dst)
  = is_no_scan_spec dst g2;
    no_scan_tag_val ();
    minor_scan_wosize_cases minor obj;
    minor_tag_bound minor obj;
    if not (is_no_scan dst g2) then begin
      assert (minor_scan_wosize minor obj == wosize);
      let sto (i: nat)
        : Lemma (i < U64.v (wosize_of_object dst g2) /\ U64.v dst + i * 8 + 8 <= heap_size ==>
                 storable free2 g2 (field_val g2 dst i))
        = if i < U64.v (wosize_of_object dst g2) && U64.v dst + i * 8 + 8 <= heap_size
          then copy_storable_one g g2 free free2 minor obj dst i
      in
      FStar.Classical.forall_intro sto
    end
#pop-options

#push-options "--z3rlimit 20"
let promote_sweep_phase g fp c0 minor obj wosize =
  let tag = Promote.promoted_tag minor obj in
  let free = free_incremental c0 in
  sweep_inv_incremental_iff g fp c0;
  alloc_sweep_phase g fp c0 wosize tag;
  let r = AC.alloc_phase g fp (SA.Sweeping c0) wosize tag in
  if r.SA.obj_out <> 0UL then begin
    let g1 = r.SA.heap_out in
    let dst : obj_addr = r.SA.obj_out in
    obj_pos g1 dst; colour_of g1 dst;
    hd_address_spec dst;
    copy_shape g1 r.SA.fp_out c0 minor obj dst 0 wosize;
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
      : Lemma (requires in_use free g y)
              (ensures read_word g2 (hd_address y) == read_word g (hd_address y) /\
                       (is_closure y g ==> same_block g g2 (hd_address y)) /\
                       in_use (free_incremental c0) g2 y)
      = alloc_keeps g fp c0 wosize tag y;
        obj_pos g1 y;
        assert (read_word g2 (hd_address y) == read_word g1 (hd_address y));
        if is_closure y g then begin
          copy_keeps g1 minor obj dst wosize y;
          same_block_trans g g1 g2 (hd_address y)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires kept);
    wf_with_parts ();
    same_heads_part4 g1 g2;
    free_incremental_ok c0;
    copy_storable g g2 free (free_incremental c0) minor obj dst wosize;
    fresh_close g2 r.SA.fp_out c0 dst
  end
#pop-options
