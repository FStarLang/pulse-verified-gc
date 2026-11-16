module GC.Spec.SweepPhase.Intrinsic.End

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Spec.SweepPhase.Intrinsic

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FLA = GC.Spec.FreeList.Ascending
module FSE = GC.Spec.FusedSweep.End
module Edit = GC.Spec.SweepPhase.Util
module Step = GC.Spec.FusedSweep.Step

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// At the end, every block is behind the cursor.
let at_end (g: heap) (fp: U64.t) (c0: U64.t) : prop =
  sweep_inv_incremental g fp c0 /\ U64.v c0 + 8 >= heap_size

let pos_behind (g: heap) (fp: U64.t) (c0: U64.t) (p: hp_addr)
  : Lemma (requires at_end g fp c0 /\ pos g p) (ensures U64.v p < U64.v c0)
  = sweep_inv_incremental_elim g fp c0;
    W.reaches_stuck g zero_addr (U64.v c0) (U64.v p)

/// ---------------------------------------------------------------------------
/// Incremental
/// ---------------------------------------------------------------------------

let end_obj (g: heap) (fp: U64.t) (c0: U64.t) (x: obj_addr)
  : Lemma (requires at_end g fp c0 /\ Seq.mem x (objects zero_addr g))
          (ensures (is_white x g \/ is_blue x g) /\ not (pending_free c0 g x))
  = sweep_inv_incremental_elim g fp c0;
    obj_pos g x; colour_of g x;
    pos_behind g fp c0 (hd_address x);
    behind_swept_elim g (U64.v c0) (hd_address x)

let sweep_inv_incremental_end g fp c0 =
  sweep_inv_incremental_elim g fp c0;
  let objs (x: obj_addr) : Lemma (Seq.mem x (objects zero_addr g) ==> (is_white x g \/ is_blue x g))
    = if Seq.mem x (objects zero_addr g) then end_obj g fp c0 x in
  FStar.Classical.forall_intro objs;
  let none (x: obj_addr) : Lemma (not (pending_free c0 g x) /\ in_use (free_incremental c0) g x == in_use free_stw g x)
    = if Seq.mem x (objects zero_addr g) then end_obj g fp c0 x in
  FStar.Classical.forall_intro none;
  wf_with_parts ();
  well_formed_heap_with_congr (free_incremental c0) free_stw g

/// ---------------------------------------------------------------------------
/// Stop-the-world
/// ---------------------------------------------------------------------------

let at_end_stw (g0 g: heap) (fp: U64.t) (c0: U64.t) : prop =
  sweep_inv_stw g0 g fp c0 /\ U64.v c0 + 8 >= heap_size

let pos0_behind (g0 g: heap) (fp: U64.t) (c0: U64.t) (p: hp_addr)
  : Lemma (requires at_end_stw g0 g fp c0 /\ pos g0 p) (ensures U64.v p < U64.v c0)
  = W.reaches_stuck g0 zero_addr (U64.v c0) (U64.v p)

/// The blocks of the result are blocks of the marked heap.
let sub_at (g0 g: heap) (fp: U64.t) (c0: U64.t) (x: obj_addr)
  : Lemma (requires at_end_stw g0 g fp c0 /\ Seq.mem x (objects zero_addr g))
          (ensures Seq.mem x (objects zero_addr g0))
  = sweep_inv_incremental_elim g fp c0;
    let c = U64.v c0 in
    obj_pos g x; obj_pos g0 x;
    let q = hd_address x in
    pos_behind g fp c0 q;
    if not (blue_at g q) then survivors_were_marked_elim g0 g c q
    else begin
      W.reaches_bounds g zero_addr (U64.v q);
      let q0 = W.block_at g0 zero_addr c (U64.v q) in
      if U64.v q0 <> U64.v q then begin
        W.reaches_bounds g0 zero_addr (U64.v q0);
        if black_at g0 q0 then begin
          marked_survive_elim g0 g q0;
          Edit.no_pos_inside g q0 (U64.v q)
        end else begin
          let s = W.last_block g zero_addr (U64.v q) in
          if blue_at g s then no_adjacent_free_elim g c s q
          else begin
            survivors_were_marked_elim g0 g c s;
            marked_survive_elim g0 g s;
            if U64.v s < U64.v q0 then Edit.no_pos_inside g0 s (U64.v q0)
            else if U64.v s > U64.v q0 then Edit.no_pos_inside g0 q0 (U64.v s)
          end
        end
      end
    end

/// A block live after marking survives, white, with its size, tag and fields.
let survives_at (g0 g: heap) (fp: U64.t) (c0: U64.t) (x: obj_addr)
  : Lemma (requires at_end_stw g0 g fp c0 /\ Seq.mem x (objects zero_addr g0) /\ is_black x g0)
          (ensures FSE.survives g0 g x)
  = sweep_inv_incremental_elim g fp c0;
    obj_pos g0 x; colour_of g0 x;
    let q = hd_address x in
    marked_survive_elim g0 g q;
    obj_pos g x; colour_of g x;
    pos_behind g fp c0 q;
    behind_swept_elim g (U64.v c0) q;
    is_no_scan_spec x g; is_no_scan_spec x g0;
    U64.v_inj (wosize_of_object x g) (wosize_of_object x g0);
    white_header_facts (read_word g0 q);
    Edit.header_eq (read_word g q) (white_header (read_word g0 q))

let dead_is_free (g0 g: heap) (fp: U64.t) (c0: U64.t) (x: obj_addr)
  : Lemma (requires at_end_stw g0 g fp c0 /\ Seq.mem x (objects zero_addr g) /\ ~(is_black x g0))
          (ensures is_blue x g)
  = obj_pos g x; colour_of g x; colour_of g0 x;
    pos_behind g fp c0 (hd_address x);
    if not (blue_at g (hd_address x)) then
      survivors_were_marked_elim g0 g (U64.v c0) (hd_address x)

let not_infix_at (g0 g: heap) (fp: U64.t) (c0: U64.t) (x: obj_addr)
  : Lemma (requires at_end_stw g0 g fp c0 /\ Seq.mem x (objects zero_addr g))
          (ensures ~(is_infix x g))
  = sweep_inv_incremental_elim g fp c0;
    wf_with_parts ()

let no_adjacent_at (g0 g: heap) (fp: U64.t) (c0: U64.t) (x y: obj_addr)
  : Lemma (requires at_end_stw g0 g fp c0 /\ Seq.mem x (objects zero_addr g) /\
                    Seq.mem y (objects zero_addr g) /\ is_blue x g /\ is_blue y g)
          (ensures ~(FSE.adjacent g x y))
  = sweep_inv_incremental_elim g fp c0;
    obj_pos g x; obj_pos g y;
    colour_of g x; colour_of g y;
    pos_behind g fp c0 (hd_address y);
    if U64.v x + U64.v (wosize_of_object x g) * 8 = U64.v y - 8 then
      no_adjacent_free_elim g (U64.v c0) (hd_address x) (hd_address y)

/// Every dead block of the marked heap lies inside a free block of the result.
let covered_at (g0 g: heap) (fp: U64.t) (c0: U64.t) (x: obj_addr)
  : Lemma (requires at_end_stw g0 g fp c0 /\ Seq.mem x (objects zero_addr g0) /\ ~(is_black x g0))
          (ensures exists (y: obj_addr). Seq.mem y (objects zero_addr g) /\ is_blue y g /\
                                         FSE.inside g0 g x y)
  = sweep_inv_incremental_elim g fp c0;
    let c = U64.v c0 in
    obj_pos g0 x; colour_of g0 x;
    let q = hd_address x in
    pos0_behind g0 g fp c0 q;
    W.reaches_bounds g0 zero_addr (U64.v q);
    let p = W.block_at g zero_addr c (U64.v q) in
    if not (blue_at g p) then begin
      survivors_were_marked_elim g0 g c p;
      marked_survive_elim g0 g p;
      if U64.v p < U64.v q then Edit.no_pos_inside g0 p (U64.v q);
      assert False
    end else begin
      let n = W.bnext g p in
      W.bnext_facts g p;
      if n = c then W.reaches_block_before g0 zero_addr q c
      else begin
        W.reaches_snoc g zero_addr p;
        let nn = mk_hp_addr n in
        W.reaches_block_before g zero_addr nn c;
        no_adjacent_free_elim g c p nn;
        survivors_were_marked_elim g0 g c nn;
        W.reaches_block_before g0 zero_addr q n
      end;
      let y = obj_of p in
      obj_of_facts p;
      obj_pos g y; colour_of g y;
      W.bnext_facts g0 q;
      assert (Seq.mem y (objects zero_addr g) /\ is_blue y g /\ FSE.inside g0 g x y)
    end

/// A free block of the result holds only blocks that were dead.
let free_holds_dead (g0 g: heap) (fp: U64.t) (c0: U64.t) (x y: obj_addr)
  : Lemma (requires at_end_stw g0 g fp c0 /\ Seq.mem y (objects zero_addr g) /\ is_blue y g /\
                    Seq.mem x (objects zero_addr g0) /\ FSE.inside g0 g x y)
          (ensures ~(is_black x g0))
  = obj_pos g y; colour_of g y;
    obj_pos g0 x; colour_of g0 x;
    if is_black x g0 then begin
      marked_survive_elim g0 g (hd_address x);
      if U64.v (hd_address x) <> U64.v (hd_address y) then
        Edit.no_pos_inside g (hd_address y) (U64.v (hd_address x))
    end

let sweep_inv_stw_end g0 g fp c0 =
  sweep_inv_incremental_elim g fp c0;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (sub_at g0 g fp c0));
  FStar.Classical.forall_intro (FStar.Classical.move_requires (survives_at g0 g fp c0));
  FStar.Classical.forall_intro (FStar.Classical.move_requires (dead_is_free g0 g fp c0));
  FStar.Classical.forall_intro (FStar.Classical.move_requires (not_infix_at g0 g fp c0));
  FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (no_adjacent_at g0 g fp c0 x));
  FStar.Classical.forall_intro (FStar.Classical.move_requires (covered_at g0 g fp c0));
  FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (free_holds_dead g0 g fp c0 x));
  reveal_opaque (`%FSE.sweep_post) (FSE.sweep_post g0 g fp)

/// ---------------------------------------------------------------------------
/// The whole pass
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec from_post_st (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_inv_stw g0 g fp st.cursor /\ st == state_at g st.cursor)
          (ensures (let r = sweep_from g fp st in FSE.sweep_post g0 (fst r) (snd r)))
          (decreases (heap_size - U64.v st.cursor))
  = if U64.v st.cursor + 8 < heap_size then begin
      Step.sweep_inv_incremental_step g fp st.cursor;
      Step.sweep_inv_stw_step g0 g fp st.cursor;
      let (g', fp', st') = sweep_step g fp st in
      sweep_from_step g fp st;
      from_post_st g0 g' fp' st'
    end else begin
      sweep_from_stop g fp st;
      sweep_inv_stw_end g0 g fp st.cursor
    end
#pop-options

let sweep_from_post g0 g fp c = from_post_st g0 g fp (state_at g c)

let fused_sweep_post g0 fp =
  sweep_inv_stw_start g0 fp;
  state_at_start g0;
  sweep_from_post g0 g0 fp sweep_start.cursor;
  let r = fused_sweep_coalesce g0 fp in
  FSE.sweep_post_wf g0 (fst r) (snd r)

/// ---------------------------------------------------------------------------
/// Nothing live
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let nothing_live_one_block g0 g fp c0 =
  sweep_inv_incremental_elim g fp c0;
  let c = U64.v c0 in
  W.reaches_refl g zero_addr;
  behind_swept_elim g c zero_addr;
  (if not (blue_at g zero_addr) then survivors_were_marked_elim g0 g c zero_addr);
  W.reaches_unfold g zero_addr c;
  let n = W.bnext g zero_addr in
  W.bnext_facts g zero_addr;
  (if n < c then begin
     let nn = mk_hp_addr n in
     W.reaches_snoc g zero_addr zero_addr;
     behind_swept_elim g c nn;
     (if not (blue_at g nn) then survivors_were_marked_elim g0 g c nn);
     no_adjacent_free_elim g c zero_addr nn
   end);
  let only (x: nat)
    : Lemma (requires W.reaches g zero_addr x /\ x < c) (ensures x == U64.v zero_addr)
    = W.reaches_bounds g zero_addr x;
      if x > U64.v zero_addr then Edit.no_pos_inside g zero_addr x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires only)
#pop-options
