module GC.Spec.SweepPhase.Intrinsic

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module Mark = GC.Spec.Mark
module Step = GC.Spec.FusedSweep.Step
module Edit = GC.Spec.FusedSweep.Edit
module Phase = GC.Spec.FusedSweep.Phase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// Opening and closing the clauses
/// ---------------------------------------------------------------------------

let sweep_phase_inv_elim g fp st = reveal_opaque (`%sweep_phase_inv) (sweep_phase_inv g fp st)

let sweep_phase_inv_intro (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires (let c = U64.v st.cursor in
                     c % 8 == 0 /\ c <= heap_size /\ W.reaches g zero_addr c /\
                     heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                     well_formed_heap_except g (pending g st) /\
                     behind_swept g c /\ front_unswept g c /\
                     no_adjacent_free g c /\ ends_free g c (prev_free g st) /\
                     tail_ok g c st.swept_tail /\ frag_ok g c st.last_fragment /\
                     FLA.fl_ascending g fp))
          (ensures sweep_phase_inv g fp st)
  = reveal_opaque (`%sweep_phase_inv) (sweep_phase_inv g fp st)

let behind_swept_elim g c p
  = reveal_opaque (`%behind_swept) (behind_swept g c)

let behind_swept_intro (g: heap) (c: nat)
  (pf: (p: hp_addr -> Lemma (requires W.reaches g zero_addr (U64.v p) /\ U64.v p < c)
                           (ensures W.can_step g p /\ (white_at g p \/ blue_at g p))))
  : Lemma (behind_swept g c)
  = reveal_opaque (`%behind_swept) (behind_swept g c);
    FStar.Classical.forall_intro (FStar.Classical.move_requires pf)

let front_unswept_elim (g: heap) (c: nat) (p: hp_addr)
  : Lemma (requires front_unswept g c /\ pos g p /\ U64.v p >= c)
          (ensures black_at g p \/ white_at g p \/ blue_at g p)
  = reveal_opaque (`%front_unswept) (front_unswept g c)

let front_unswept_intro (g: heap) (c: nat)
  (pf: (p: hp_addr -> Lemma (requires pos g p /\ U64.v p >= c)
                           (ensures black_at g p \/ white_at g p \/ blue_at g p)))
  : Lemma (front_unswept g c)
  = reveal_opaque (`%front_unswept) (front_unswept g c);
    FStar.Classical.forall_intro (FStar.Classical.move_requires pf)

let pending_ok_lemma g st =
  let aux (x: obj_addr)
    : Lemma (pending g st x ==> Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
    = Mark.colors_exclusive x g
  in
  FStar.Classical.forall_intro aux

let survivors_unchanged_elim g0 g p = reveal_opaque (`%survivors_unchanged) (survivors_unchanged g0 g)

let survivors_unchanged_intro (g0 g: heap)
  (pf: (p: hp_addr -> Lemma (requires pos g0 p /\ black_at g0 p)
         (ensures pos g p /\ not (blue_at g p) /\ wz_at g p == wz_at g0 p /\
                  getTag (read_word g p) == getTag (read_word g0 p) /\
                  (forall (a: hp_addr). U64.v p < U64.v a /\ U64.v a < W.bnext g0 p ==>
                     read_word g a == read_word g0 a))))
  : Lemma (survivors_unchanged g0 g)
  = reveal_opaque (`%survivors_unchanged) (survivors_unchanged g0 g);
    FStar.Classical.forall_intro (FStar.Classical.move_requires pf)

let behind_survivors_elim g0 g c p = reveal_opaque (`%behind_survivors) (behind_survivors g0 g c)

let behind_survivors_intro (g0 g: heap) (c: nat)
  (pf: (p: hp_addr -> Lemma (requires pos g p /\ U64.v p < c /\ not (blue_at g p))
                           (ensures pos g0 p /\ black_at g0 p)))
  : Lemma (behind_survivors g0 g c)
  = reveal_opaque (`%behind_survivors) (behind_survivors g0 g c);
    FStar.Classical.forall_intro (FStar.Classical.move_requires pf)

/// ---------------------------------------------------------------------------
/// Objects and positions
/// ---------------------------------------------------------------------------

/// The colour predicates of an object are those of its header.
let colour_of g x
  = color_of_object_spec x g;
    is_black_iff x g; is_blue_iff x g; is_white_iff x g;
    wosize_of_object_spec x g; tag_of_object_spec x g

/// An object of the walk is a block at its header.
let obj_pos g x
  = W.objects_mem_iff g zero_addr x;
    W.hd_address_pos x;
    if W.reaches g zero_addr (U64.v x - 8) then W.reaches_bounds g zero_addr (U64.v x - 8)

let obj_of_facts q
  = f_address_spec q; hd_f_roundtrip q

/// A block not free and not pending free, at its header.
let live_pos (g: heap) (c: nat) (q: hp_addr) : bool =
  pos g q && not (blue_at g q) && not (white_at g q && U64.v q >= c)

let live_obj (g: heap) (st: sweep_state) (x: obj_addr)
  : Lemma (requires U64.v st.cursor % 8 == 0)
          (ensures not_freed g (pending g st) x <==> live_pos g (U64.v st.cursor) (hd_address x))
  = obj_pos g x; colour_of g x

/// ---------------------------------------------------------------------------
/// Headers
/// ---------------------------------------------------------------------------

let black_header (h: U64.t) : U64.t = makeHeader (getWosize h) Header.Black (getTag h)

let black_header_facts (h: U64.t)
  : Lemma (getWosize (black_header h) == getWosize h /\
           getColor (black_header h) == Header.Black /\
           getTag (black_header h) == getTag h)
  = makeHeader_getWosize (getWosize h) Header.Black (getTag h);
    makeHeader_getColor (getWosize h) Header.Black (getTag h);
    makeHeader_getTag (getWosize h) Header.Black (getTag h)

let white_black (h: U64.t)
  : Lemma (requires getColor h == Header.White)
          (ensures white_header (black_header h) == h)
  = black_header_facts h;
    white_header_facts (black_header h);
    Edit.header_eq (white_header (black_header h)) h

/// ---------------------------------------------------------------------------
/// The reference heap, rebuilt from the current one
/// ---------------------------------------------------------------------------
///
/// The stop-the-world step lemmas (`GC.Spec.FusedSweep.Step`) are stated
/// against a heap marking left.  Any heap satisfying the sweep phase *has*
/// one: blacken every white block behind the cursor.  It is built only inside
/// the step's proof, from the current heap and cursor; nothing carries it.

let rec blacken (g: heap) (p: hp_addr) (c: nat) : GTot heap (decreases (heap_size - U64.v p)) =
  if U64.v p >= c || not (W.can_step g p) then g
  else begin
    let g1 = if white_at g p then write_word g p (black_header (read_word g p)) else g in
    let n = W.bnext g p in
    if n >= heap_size then g1
    else begin
      W.bnext_facts g p;
      blacken g1 (mk_hp_addr n) c
    end
  end

let blackened (g: heap) (p: hp_addr) (c: nat) (a: hp_addr) : bool =
  W.reaches g p (U64.v a) && U64.v a < c && W.can_step g a && white_at g a

#push-options "--fuel 1"
let rec blacken_read (g: heap) (p: hp_addr) (c: nat) (a: hp_addr)
  : Lemma (ensures read_word (blacken g p c) a ==
                   (if blackened g p c a then black_header (read_word g a) else read_word g a))
          (decreases (heap_size - U64.v p))
  = if U64.v p >= c || not (W.can_step g p) then begin
      if W.reaches g p (U64.v a) then begin
        W.reaches_bounds g p (U64.v a);
        if U64.v p < U64.v a then W.reaches_unfold g p (U64.v a)
      end
    end else begin
      let hb = black_header (read_word g p) in
      let g1 = if white_at g p then write_word g p hb else g in
      let n = W.bnext g p in
      W.bnext_facts g p;
      let same (w: hp_addr) : Lemma (requires w <> p) (ensures read_word g1 w == read_word g w)
        = if white_at g p then read_write_different g p w hb
      in
      (if white_at g p then read_write_same g p hb);
      if U64.v a < U64.v p then begin
        if W.reaches g p (U64.v a) then W.reaches_bounds g p (U64.v a)
      end;
      if U64.v a > U64.v p && W.reaches g p (U64.v a) then W.reaches_unfold g p (U64.v a);
      if n >= heap_size then begin
        if U64.v a <> U64.v p then same a
      end else begin
        let nn = mk_hp_addr n in
        blacken_read g1 nn c a;
        let fr (w: hp_addr) : Lemma (requires U64.v w >= U64.v nn) (ensures read_word g1 w == read_word g w)
          = same w in
        FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
        W.walk_frame_from g g1 nn;
        if U64.v a < n && W.reaches g1 nn (U64.v a) then W.reaches_bounds g1 nn (U64.v a);
        if U64.v a <> U64.v p then begin
          same a;
          if U64.v a > U64.v p then begin
            W.reaches_refl g nn;
            if W.reaches g nn (U64.v a) then begin
              W.reaches_step g p;
              W.reaches_trans g p nn (U64.v a)
            end
          end
        end
      end
    end
#pop-options

/// The reference heap of the sweep phase at cursor `c`.
let ref_of (g: heap) (c: nat) : GTot heap = blacken g zero_addr c

let ref_read (g: heap) (c: nat) (a: hp_addr)
  : Lemma (read_word (ref_of g c) a ==
           (if pos g a && U64.v a < c && white_at g a then black_header (read_word g a)
            else read_word g a))
  = blacken_read g zero_addr c a

/// The reference heap has the same walk, and the same sizes everywhere.
let ref_walk (g: heap) (c: nat)
  : Lemma (objects zero_addr (ref_of g c) == objects zero_addr g /\
           (forall (b: nat). W.reaches (ref_of g c) zero_addr b == W.reaches g zero_addr b) /\
           (forall (q: hp_addr). W.can_step (ref_of g c) q == W.can_step g q /\
                            W.bnext (ref_of g c) q == W.bnext g q /\
                            wz_at (ref_of g c) q == wz_at g q))
  = let r = ref_of g c in
    let sz (q: hp_addr)
      : Lemma (getWosize (read_word r q) == getWosize (read_word g q))
      = ref_read g c q; black_header_facts (read_word g q)
    in
    FStar.Classical.forall_intro sz;
    W.walk_congr g r zero_addr

/// A block that is not free and not pending is black in the reference heap,
/// and the reference heap has the same block there.
let ref_block (g: heap) (fp: U64.t) (st: sweep_state) (q: hp_addr)
  : Lemma (requires sweep_phase_inv g fp st)
          (ensures (let c = U64.v st.cursor in
                    let r = ref_of g c in
                    (live_pos g c q <==> pos r q /\ black_at r q) /\
                    (pos r q ==> same_block g r q) /\
                    (U64.v q >= c ==> read_word r q == read_word g q)))
  = sweep_phase_inv_elim g fp st;
    let c = U64.v st.cursor in
    let r = ref_of g c in
    ref_read g c q; ref_walk g c;
    black_header_facts (read_word g q);
    if pos g q then begin
      if U64.v q < c then behind_swept_elim g c q else front_unswept_elim g c q;
      let body (a: hp_addr)
        : Lemma (requires U64.v q < U64.v a /\ U64.v a < W.bnext g q)
                (ensures read_word r a == read_word g a)
        = ref_read g c a;
          if W.reaches g zero_addr (U64.v a) then Edit.no_pos_inside g q (U64.v a)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires body)
    end

/// The sweep phase is the stop-the-world invariant against its reference heap.
let swept_of (g: heap) (fp: U64.t) (st: sweep_state) (p: hp_addr)
  : Lemma (requires sweep_phase_inv g fp st /\ W.reaches g zero_addr (U64.v p) /\
                    U64.v p < U64.v st.cursor)
          (ensures swept_block (ref_of g (U64.v st.cursor)) g p)
  = sweep_phase_inv_elim g fp st;
    let c = U64.v st.cursor in
    let r = ref_of g c in
    behind_swept_elim g c p;
    ref_read g c p; ref_walk g c;
    if white_at g p then begin
      black_header_facts (read_word g p);
      white_black (read_word g p);
      let body (a: hp_addr)
        : Lemma (requires U64.v p < U64.v a /\ U64.v a < W.bnext g p)
                (ensures read_word g a == read_word r a)
        = ref_read g c a;
          if W.reaches g zero_addr (U64.v a) then Edit.no_pos_inside g p (U64.v a)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires body);
      assert (survivor r g p)
    end else begin
      dead_run_one r p;
      assert (free_run r g p)
    end

let to_ref (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st)
          (ensures (let r = ref_of g (U64.v st.cursor) in sweep_inv r g fp st /\ sweep_g0 r))
  = sweep_phase_inv_elim g fp st;
    let c = U64.v st.cursor in
    let r = ref_of g c in
    ref_walk g c;
    front_same_intro r g c (fun a -> ref_read g c a);
    behind_ok_intro r g c (fun p -> swept_of g fp st p);
    W.reaches_end_of_dense g;
    W.dense_of_reaches_end r (W.walk_end g zero_addr);
    sweep_inv_intro r g fp st

/// ---------------------------------------------------------------------------
/// After a step, against the reference heap
/// ---------------------------------------------------------------------------

/// Against a reference heap `r`, a heap `g'` that satisfies the
/// stop-the-world invariant at `c'` keeps exactly the blocks black in `r`
/// (and no others) as not-freed blocks, with their contents.
let after_live (r g': heap) (c': nat) (q: hp_addr)
  : Lemma (requires W.reaches r zero_addr c' /\ W.reaches g' zero_addr c' /\
                    front_same r g' c' /\ behind_ok r g' c' /\ front_unswept r c')
          (ensures (live_pos g' c' q <==> pos r q /\ black_at r q) /\
                   (pos r q /\ black_at r q ==> same_block r g' q /\ W.bnext g' q == W.bnext r q))
  = if U64.v q >= c' then begin
      Phase.front_pos r g' c' q;
      if pos r q then front_unswept_elim r c' q;
      let body (a: hp_addr)
        : Lemma (requires U64.v q < U64.v a) (ensures read_word g' a == read_word r a)
        = front_same_elim r g' c' a
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires body)
    end else begin
      if live_pos g' c' q then begin
        behind_ok_elim r g' c' q;
        Edit.swept_block_kinds r g' q;
        Edit.behind_pos_ref r g' c' (U64.v q)
      end;
      if pos r q && black_at r q then begin
        W.reaches_bounds r zero_addr (U64.v q);
        let p = W.block_at g' zero_addr c' (U64.v q) in
        behind_ok_elim r g' c' p;
        Edit.swept_block_kinds r g' p;
        Edit.behind_pos_ref r g' c' (U64.v p);
        W.reaches_det r zero_addr p (U64.v q);
        if black_at r p then begin
          if U64.v p < U64.v q then Edit.no_pos_inside r p (U64.v q);
          assert (p == q);
          white_header_facts (read_word r q)
        end else begin
          dead_run_mem r p (W.bnext g' p) q;
          assert False
        end
      end
    end

/// ---------------------------------------------------------------------------
/// Well-formedness, carried across a heap change that keeps the live blocks
/// ---------------------------------------------------------------------------

/// `exists_field_pointing_to_unchecked` reads only the words it scans.
#push-options "--fuel 1 --ifuel 0"
let rec efptu_congr (h1 h2: heap) (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (dst: obj_addr)
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

/// The fields of the source, as `exists_field_pointing_to_unchecked` reads
/// them, are words of its block.
let src_fields (g g': heap) (src dst: obj_addr)
  : Lemma (requires same_block g g' (hd_address src))
          (ensures U64.v (wosize_of_object src g) < pow2 54 /\
                   wosize_of_object src g' == wosize_of_object src g /\
                   is_no_scan src g' == is_no_scan src g /\
                   exists_field_pointing_to_unchecked g' src (wosize_of_object src g) dst ==
                   exists_field_pointing_to_unchecked g src (wosize_of_object src g) dst)
  = colour_of g src; colour_of g' src;
    is_no_scan_spec src g; is_no_scan_spec src g';
    hd_address_spec src;
    wosize_of_object_bound src g;
    efptu_congr g' g src (wosize_of_object src g) dst

/// The target of a field of a source that stayed, resolved, stays too.
let target_moves (g g': heap) (pf pf': obj_addr -> prop) (src dst: obj_addr)
  : Lemma (requires well_formed_heap_except g pf /\
                    (forall (x: obj_addr). not_freed g' pf' x <==> not_freed g pf x) /\
                    (forall (x: obj_addr). not_freed g pf x ==> same_block g g' (hd_address x)) /\
                    not_freed g' pf' src /\ fields_constrained g' src /\
                    (let wz = wosize_of_object src g' in
                     U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g' src wz dst))
          (ensures not_freed g' pf' (resolve_object dst g') /\
                   infix_addr_wf g' (objects zero_addr g') dst)
  = assert (not_freed g pf src);
    src_fields g g' src dst;
    colour_of g src; colour_of g' src;
    wf_except_parts ();
    wfh_part2_except_elim g pf src dst;
    wfh_part3_except_elim g pf src dst;
    let t = resolve_object dst g in
    if is_infix dst g then begin
      infix_addr_wf_elim g (objects zero_addr g) dst;
      parent_closure_addr_nat_spec dst g;
      resolve_infix_spec dst g;
      hd_address_spec dst; hd_address_spec t;
      colour_of g t;
      assert (same_block g g' (hd_address t));
      assert (read_word g' (hd_address dst) == read_word g (hd_address dst));
      resolve_object_locality dst g g';
      colour_of g' t;
      is_closure_spec t g; is_closure_spec t g';
      infix_addr_wf_transfer g g' (objects zero_addr g) (objects zero_addr g') dst
    end else begin
      resolve_non_infix dst g;
      colour_of g dst; colour_of g' dst;
      is_infix_spec dst g; is_infix_spec dst g';
      resolve_non_infix dst g';
      infix_addr_wf_non_infix g' (objects zero_addr g') dst
    end

/// **Well-formedness except the pending objects, transported**: a change
/// that keeps the same not-freed objects, with the same size, tag and
/// fields, keeps the field closure.
let wf_transport g g' pf pf'
  = wf_except_parts ();
    Edit.part1_holds g';
    well_formed_heap_part2_except_intro g' pf' (fun src dst -> target_moves g g' pf pf' src dst);
    well_formed_heap_part3_except_intro g' pf' (fun src dst -> target_moves g g' pf pf' src dst)

/// ---------------------------------------------------------------------------
/// Start
/// ---------------------------------------------------------------------------

let start_target (g0: heap) (src dst: obj_addr)
  : Lemma (requires well_formed_heap g0 /\ Mark.noGreyObjects g0 /\ Mark.tri_color_invariant g0 /\
                    not_freed g0 (pending g0 sweep_start) src /\ fields_constrained g0 src /\
                    (let wz = wosize_of_object src g0 in
                     U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g0 src wz dst))
          (ensures not_freed g0 (pending g0 sweep_start) (resolve_object dst g0) /\
                   infix_addr_wf g0 (objects zero_addr g0) dst)
  = wf_parts ();
    W.objects_mem_iff g0 zero_addr src;
    Mark.color_exhaustive src g0; Mark.colors_exclusive src g0;
    assert (is_black src g0);
    wfh_part2_elim g0 src dst;
    wfh_part3_elim g0 src dst;
    let t = resolve_object dst g0 in
    assert (points_to g0 src dst);
    assert (~(is_white t g0));
    Mark.color_exhaustive t g0; Mark.colors_exclusive t g0

let sweep_phase_start g0 fp =
  sweep_start_inv g0 fp;
  sweep_inv_elim g0 g0 fp sweep_start;
  let c = U64.v zero_addr in
  behind_swept_intro g0 c (fun p -> W.reaches_bounds g0 zero_addr (U64.v p));
  let front (p: hp_addr)
    : Lemma (requires pos g0 p /\ U64.v p >= c)
            (ensures black_at g0 p \/ white_at g0 p \/ blue_at g0 p)
    = let x = obj_of p in
      obj_of_facts p;
      obj_pos g0 x;
      colour_of g0 x;
      Mark.color_exhaustive x g0
  in
  front_unswept_intro g0 c front;
  wf_parts ();
  wf_except_parts ();
  well_formed_heap_part2_except_intro g0 (pending g0 sweep_start) (fun src dst -> start_target g0 src dst);
  well_formed_heap_part3_except_intro g0 (pending g0 sweep_start) (fun src dst -> start_target g0 src dst);
  sweep_phase_inv_intro g0 fp sweep_start;
  W.reaches_refl g0 zero_addr;
  front_same_intro g0 g0 c (fun _ -> ());
  survivors_unchanged_intro g0 g0 (fun _ -> ());
  behind_survivors_intro g0 g0 c (fun p -> W.reaches_bounds g0 zero_addr (U64.v p))

/// ---------------------------------------------------------------------------
/// Step
/// ---------------------------------------------------------------------------

/// The step, run against the reference heap.
let step_ref (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let c = U64.v st.cursor in
                    let r = ref_of g c in
                    let (g', fp', st') = sweep_step g fp st in
                    sweep_inv r g' fp' st' /\ sweep_g0 r /\
                    pos g st.cursor /\ U64.v st'.cursor == W.bnext g st.cursor /\
                    W.reaches r zero_addr (U64.v st'.cursor) /\
                    front_unswept r (U64.v st'.cursor)))
  = to_ref g fp st;
    let c = U64.v st.cursor in
    let r = ref_of g c in
    Step.sweep_step_inv r g fp st;
    sweep_phase_inv_elim g fp st;
    let (g', fp', st') = sweep_step g fp st in
    sweep_inv_elim r g' fp' st';
    ref_walk g c;
    let c' = U64.v st'.cursor in
    let front (p: hp_addr)
      : Lemma (requires pos r p /\ U64.v p >= c')
              (ensures black_at r p \/ white_at r p \/ blue_at r p)
      = ref_read g c p;
        front_unswept_elim g c p
    in
    front_unswept_intro r c' front

/// One step's effect on the blocks: not-freed before iff after, same contents.
let step_live (g: heap) (fp: U64.t) (st: sweep_state) (q: hp_addr)
  : Lemma (requires sweep_phase_inv g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    (live_pos g' (U64.v st'.cursor) q <==> live_pos g (U64.v st.cursor) q) /\
                    (live_pos g (U64.v st.cursor) q ==>
                       same_block g g' q /\ W.bnext g' q == W.bnext g q)))
  = step_ref g fp st;
    let c = U64.v st.cursor in
    let r = ref_of g c in
    let (g', fp', st') = sweep_step g fp st in
    sweep_inv_elim r g' fp' st';
    ref_block g fp st q;
    ref_walk g c;
    after_live r g' (U64.v st'.cursor) q

/// Every object of the heap after a step is not infix.
let step_part4 (g: heap) (fp: U64.t) (st: sweep_state) (x: obj_addr)
  : Lemma (requires sweep_phase_inv g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    Seq.mem x (objects zero_addr g') ==> ~(is_infix x g')))
  = step_ref g fp st;
    sweep_phase_inv_elim g fp st;
    let c = U64.v st.cursor in
    let r = ref_of g c in
    let (g', fp', st') = sweep_step g fp st in
    let c' = U64.v st'.cursor in
    sweep_inv_elim r g' fp' st';
    ref_walk g c;
    wf_except_parts ();
    obj_pos g' x; obj_pos g x;
    colour_of g' x; colour_of g x;
    is_infix_spec x g'; is_infix_spec x g;
    let q = hd_address x in
    if pos g' q then begin
      ref_read g c q;
      black_header_facts (read_word g q);
      if U64.v q >= c' then Phase.front_pos r g' c' q
      else begin
        behind_ok_elim r g' c' q;
        Edit.swept_block_kinds r g' q;
        Edit.behind_pos_ref r g' c' (U64.v q);
        white_header_facts (read_word r q);
        infix_tag_val ()
      end
    end

/// The pending set after a step is part of the one before.
let step_pending (g: heap) (fp: U64.t) (st: sweep_state) (x: obj_addr)
  : Lemma (requires sweep_phase_inv g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    pending g' st' x ==> pending g st x))
  = step_ref g fp st;
    let c = U64.v st.cursor in
    let r = ref_of g c in
    let (g', fp', st') = sweep_step g fp st in
    let c' = U64.v st'.cursor in
    sweep_inv_elim r g' fp' st';
    ref_walk g c;
    obj_pos g' x; obj_pos g x;
    colour_of g' x; colour_of g x;
    let q = hd_address x in
    if U64.v q >= c' then begin
      Phase.front_pos r g' c' q;
      ref_read g c q
    end

/// The walk of the heap after a step still covers the heap.
let step_dense (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    heap_objects_dense g' /\ Seq.length (objects zero_addr g') > 0))
  = step_ref g fp st;
    sweep_phase_inv_elim g fp st;
    let c = U64.v st.cursor in
    let r = ref_of g c in
    let (g', fp', st') = sweep_step g fp st in
    let c' = U64.v st'.cursor in
    sweep_inv_elim r g' fp' st';
    W.reaches_bounds g zero_addr c;
    W.reaches_unfold g' zero_addr c';
    W.reaches_end_of_dense r;
    let e = W.walk_end r zero_addr in
    W.reaches_stuck r zero_addr e c';
    W.reaches_bounds r zero_addr e;
    if c' < e then begin
      let ca = mk_hp_addr c' in
      W.reaches_det r zero_addr ca e;
      let fr (w: hp_addr) : Lemma (requires U64.v w >= c') (ensures read_word g' w == read_word r w)
        = front_same_elim r g' c' w in
      FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
      W.walk_frame_from r g' ca;
      W.reaches_trans g' zero_addr ca e
    end;
    W.dense_of_reaches_end g' e

/// Behind and in front of the cursor, after a step.
let step_regions (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    behind_swept g' (U64.v st'.cursor) /\ front_unswept g' (U64.v st'.cursor)))
  = step_ref g fp st;
    sweep_phase_inv_elim g fp st;
    let c = U64.v st.cursor in
    let r = ref_of g c in
    let (g', fp', st') = sweep_step g fp st in
    let c' = U64.v st'.cursor in
    sweep_inv_elim r g' fp' st';
    ref_walk g c;
    let behind (p: hp_addr)
      : Lemma (requires W.reaches g' zero_addr (U64.v p) /\ U64.v p < c')
              (ensures W.can_step g' p /\ (white_at g' p \/ blue_at g' p))
      = behind_ok_elim r g' c' p;
        Edit.swept_block_kinds r g' p;
        white_header_facts (read_word r p)
    in
    behind_swept_intro g' c' behind;
    let front (p: hp_addr)
      : Lemma (requires pos g' p /\ U64.v p >= c')
              (ensures black_at g' p \/ white_at g' p \/ blue_at g' p)
      = Phase.front_pos r g' c' p;
        front_unswept_elim r c' p
    in
    front_unswept_intro g' c' front

let sweep_phase_step g fp st pf0 =
  step_ref g fp st;
  step_dense g fp st;
  step_regions g fp st;
  sweep_phase_inv_elim g fp st;
  let c = U64.v st.cursor in
  let r = ref_of g c in
  let (g', fp', st') = sweep_step g fp st in
  let c' = U64.v st'.cursor in
  sweep_inv_elim r g' fp' st';
  W.bnext_facts g st.cursor;
  // well formed except the (smaller) pending set
  let keep (x: obj_addr)
    : Lemma ((not_freed g' (pending g' st') x <==> not_freed g (pending g st) x) /\
             (not_freed g (pending g st) x ==> same_block g g' (hd_address x)))
    = live_obj g st x; live_obj g' st' x;
      step_live g fp st (hd_address x)
  in
  FStar.Classical.forall_intro keep;
  wf_except_parts ();
  FStar.Classical.forall_intro (step_part4 g fp st);
  wf_transport g g' (pending g st) (pending g' st');
  sweep_phase_inv_intro g' fp' st';
  FStar.Classical.forall_intro (step_pending g fp st)

/// ---------------------------------------------------------------------------
/// Step, stop-the-world
/// ---------------------------------------------------------------------------

let stw_survivor (g0 g: heap) (fp: U64.t) (st: sweep_state) (p: hp_addr)
  : Lemma (requires sweep_phase_inv g fp st /\ stw_rel g0 g (U64.v st.cursor) /\
                    U64.v st.cursor + 8 < heap_size /\ pos g0 p /\ black_at g0 p)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    pos g' p /\ not (blue_at g' p) /\ wz_at g' p == wz_at g0 p /\
                    getTag (read_word g' p) == getTag (read_word g0 p) /\
                    (forall (a: hp_addr). U64.v p < U64.v a /\ U64.v a < W.bnext g0 p ==>
                       read_word g' a == read_word g0 a)))
  = let c = U64.v st.cursor in
    survivors_unchanged_elim g0 g p;
    if U64.v p >= c then front_same_elim g0 g c p;
    step_live g fp st p

let stw_behind (g0 g: heap) (fp: U64.t) (st: sweep_state) (p: hp_addr)
  : Lemma (requires sweep_phase_inv g fp st /\ stw_rel g0 g (U64.v st.cursor) /\
                    U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    pos g' p /\ U64.v p < U64.v st'.cursor /\ not (blue_at g' p) ==>
                      pos g0 p /\ black_at g0 p))
  = step_ref g fp st;
    sweep_phase_inv_elim g fp st;
    let c = U64.v st.cursor in
    let (g', fp', st') = sweep_step g fp st in
    let c' = U64.v st'.cursor in
    step_live g fp st p;
    if pos g' p && U64.v p < c' && not (blue_at g' p) then begin
      if U64.v p < c then behind_survivors_elim g0 g c p
      else begin
        if U64.v p > c then Edit.no_pos_inside g st.cursor (U64.v p);
        front_unswept_elim g c p;
        front_same_elim g0 g c p
      end
    end

let sweep_phase_step_stw g0 g fp st =
  step_ref g fp st;
  sweep_phase_inv_elim g fp st;
  let c = U64.v st.cursor in
  let r = ref_of g c in
  let (g', fp', st') = sweep_step g fp st in
  let c' = U64.v st'.cursor in
  sweep_inv_elim r g' fp' st';
  front_same_elim g0 g c st.cursor;
  W.reaches_snoc g0 zero_addr st.cursor;
  let fs (a: hp_addr) : Lemma (requires U64.v a >= c') (ensures read_word g' a == read_word g0 a)
    = front_same_elim r g' c' a;
      ref_read g c a;
      front_same_elim g0 g c a
  in
  front_same_intro g0 g' c' fs;
  survivors_unchanged_intro g0 g' (fun p -> stw_survivor g0 g fp st p);
  behind_survivors_intro g0 g' c' (fun p -> stw_behind g0 g fp st p)
