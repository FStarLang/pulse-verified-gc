module GC.Spec.SweepPhase.Intrinsic

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module FreeList = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module Mark = GC.Spec.Mark
module Step = GC.Spec.FusedSweep.Step
module Edit = GC.Spec.SweepPhase.Util
module Phase = GC.Spec.SweepPhase.Util

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The sweep's caches, derived
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let rec max_cell_below_spec g x =
  if x = 0 then begin
    let aux (y: U64.t) : Lemma (~(FL.fl_cell g y /\ U64.v y <= 0)) = () in
    FStar.Classical.forall_intro aux
  end else begin
    max_cell_below_spec g (x - 1);
    if x < heap_size && FStar.IndefiniteDescription.strong_excluded_middle (FL.fl_cell g (U64.uint_to_t x))
    then ()
    else begin
      let aux (y: U64.t) : Lemma (FL.fl_cell g y /\ U64.v y <= x ==> U64.v y <= x - 1)
        = if U64.v y = x && x >= heap_size then () in
      FStar.Classical.forall_intro aux
    end
  end
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec max_cell_below_congr g g' x =
  if x = 0 then () else max_cell_below_congr g g' (x - 1)
#pop-options

/// The spec pins `max_cell_below` down.
private let max_cell_unique (g: heap) (x: nat) (m: U64.t)
  : Lemma (requires (m == 0UL \/ (FL.fl_cell g m /\ U64.v m <= x)) /\
                    (forall (y: U64.t). FL.fl_cell g y /\ U64.v y <= x ==> m <> 0UL /\ U64.v y <= U64.v m))
          (ensures max_cell_below g x == m)
  = max_cell_below_spec g x

/// A cell's block ends at or before any walk position above the cell.
#push-options "--z3rlimit 20"
private let cell_end_before (g: heap) (x: U64.t) (c: nat)
  : Lemma (requires FL.fl_cell g x /\ W.reaches g zero_addr c /\ U64.v x < c)
          (ensures U64.v x + wosize_at g x * 8 <= c /\ wosize_at g x >= 1)
  = fl_cell_iff g x;
    wosize_at_hd g x;
    let q = mk_hp_addr (U64.v x - 8) in
    W.bnext_facts g q;
    if c < W.bnext g q then no_pos_inside g q c
#pop-options

#push-options "--z3rlimit 20"
let tail_ok_iff g c t =
  let m = last_cell_behind g c in
  (if c > 0 then max_cell_below_spec g (c - 1));
  let fwd () : Lemma (requires tail_ok g c t) (ensures t == m)
    = tail_ok_elim g c t;
      (if t <> 0UL then begin fl_cell_iff g t; wosize_at_hd g t end);
      if c > 0 then begin
        let aux (y: U64.t) : Lemma (FL.fl_cell g y /\ U64.v y <= c - 1 ==> t <> 0UL /\ U64.v y <= U64.v t)
          = () in
        FStar.Classical.forall_intro aux;
        max_cell_unique g (c - 1) t
      end
  in
  let bwd () : Lemma (requires t == m) (ensures tail_ok g c t)
    = (if t <> 0UL then cell_end_before g t c);
      tail_ok_intro g c t
  in
  FStar.Classical.move_requires fwd ();
  FStar.Classical.move_requires bwd ()
#pop-options

/// A fragment ending at `c` is no cell's block: two blocks of the walk do not
/// end at the same position.
#push-options "--z3rlimit 30"
let frag_ok_derived g st =
  let c = U64.v st.cursor in
  let f = st.last_fragment in
  if f <> 0UL then ()
  else if c >= U64.v zero_addr + 8 && c < heap_size && c % 8 = 0 &&
          W.reaches g zero_addr (c - 8) && W.can_step g (mk_hp_addr (c - 8)) &&
          blue_at g (mk_hp_addr (c - 8)) && wz_at g (mk_hp_addr (c - 8)) = 0
  then begin
    // the fragment's block is free, so the block before the cursor is, so
    // `swept_tail`'s block ends at the cursor -- around the fragment
    let p = mk_hp_addr (c - 8) in
    ends_free_elim g c (prev_free g st) p;
    let t = st.swept_tail in
    tail_ok_elim g c t;
    assert (t <> 0UL);
    fl_cell_iff g t;
    wosize_at_hd g t;
    let q = mk_hp_addr (U64.v t - 8) in
    W.bnext_facts g q;
    no_pos_inside g q (c - 8)
  end
#pop-options

let frag_at_ok g c = ()

let ends_free_derived g c =
  let n = U64.v c in
  let st = state_at g c in
  let ef (p: hp_addr)
    : Lemma (requires W.reaches g zero_addr (U64.v p) /\ W.can_step g p /\ W.bnext g p == n)
            (ensures blue_at g p == prev_free g st)
    = W.bnext_facts g p;
      W.reaches_bounds g zero_addr (U64.v p);
      // `p` is the only block of the walk that ends at `n`
      let uniq (q: hp_addr)
        : Lemma (requires W.reaches g zero_addr (U64.v q) /\ W.can_step g q /\ W.bnext g q == n)
                (ensures q == p)
        = W.bnext_facts g q;
          if U64.v q < U64.v p then no_pos_inside g q (U64.v p)
          else if U64.v p < U64.v q then no_pos_inside g p (U64.v q)
      in
      max_cell_below_spec g (n - 1);
      let m = last_cell_behind g n in
      // the cell `swept_tail` names, when its block ends at `n`, is `p`'s
      (if m <> 0UL then begin
         fl_cell_iff g m; wosize_at_hd g m;
         let q = mk_hp_addr (U64.v m - 8) in
         W.bnext_facts g q;
         if U64.v m + wosize_at g m * 8 = n then uniq q
       end);
      // so is the fragment
      (if frag_at g n <> 0UL then uniq (mk_hp_addr (n - 8)));
      if blue_at g p && wz_at g p >= 1 then begin
        // a cell: the last one behind `n`
        let x : U64.t = U64.uint_to_t (U64.v p + 8) in
        fl_cell_iff g x;
        assert (mk_hp_addr (U64.v x - 8) == p);
        assert (FL.fl_cell g x);
        assert (m <> 0UL /\ U64.v x <= U64.v m);
        fl_cell_iff g m;
        if U64.v m > U64.v x then no_pos_inside g p (U64.v m - 8);
        wosize_at_hd g x
      end
  in
  ends_free_intro g n (prev_free g st) ef

let state_at_start g =
  zero_addr_above_2048 ();
  max_cell_below_spec g (U64.v zero_addr - 1);
  let none (y: U64.t) : Lemma (requires FL.fl_cell g y) (ensures U64.v y > U64.v zero_addr - 1)
    = fl_cell_iff g y;
      W.reaches_bounds g zero_addr (U64.v y - 8)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires none)

/// ---------------------------------------------------------------------------
/// What counts as free during the sweep
/// ---------------------------------------------------------------------------

let free_incremental_ok c =
  reveal_opaque (`%free_def_ok) free_def_ok;
  let aux (g g': heap) (x: obj_addr) : Lemma
    ((is_block g x <==> is_block g' x) /\
     read_word g (hd_address x) == read_word g' (hd_address x) ==>
     free_incremental c g x == free_incremental c g' x)
    = FStar.Classical.move_requires (color_of_header_eq x g) g'
  in
  FStar.Classical.forall_intro_3 aux

let well_formed_heap_with_congr free free' g =
  wf_with_parts ();
  let one (free free': free_def)
    : Lemma (requires (forall (x: obj_addr). in_use free' g x == in_use free g x) /\ well_formed_heap_with free g)
            (ensures well_formed_heap_with free' g)
    = pointers_lead_to_non_free_intro free' g (fun src dst -> pointers_lead_to_non_free_elim free g src dst);
      interior_pointers_valid_intro free' g (fun src dst -> interior_pointers_valid_elim free g src dst)
  in
  FStar.Classical.move_requires (one free) free';
  FStar.Classical.move_requires (one free') free

/// ---------------------------------------------------------------------------
/// Opening and closing the clauses
/// ---------------------------------------------------------------------------

/// The caches are derived exactly when `tail_ok` and `frag_ok` hold.
private let caches_derived (g: heap) (st: sweep_state)
  : Lemma (requires W.reaches g zero_addr (U64.v st.cursor) /\
                    ends_free g (U64.v st.cursor) (prev_free g st))
          (ensures (st == state_at g st.cursor <==>
                    tail_ok g (U64.v st.cursor) st.swept_tail /\ frag_ok g (U64.v st.cursor) st.last_fragment))
  = let c = U64.v st.cursor in
    tail_ok_iff g c st.swept_tail;
    frag_at_ok g c;
    FStar.Classical.move_requires (frag_ok_derived g) st

/// The clauses of the derived state at a position of the walk.
private let derived_clauses (g: heap) (c: U64.t)
  : Lemma (requires W.reaches g zero_addr (U64.v c))
          (ensures (let st = state_at g c in
                    ends_free g (U64.v c) (prev_free g st) /\
                    tail_ok g (U64.v c) st.swept_tail /\ frag_ok g (U64.v c) st.last_fragment))
  = ends_free_derived g c;
    tail_ok_iff g (U64.v c) (last_cell_behind g (U64.v c));
    frag_at_ok g (U64.v c)

let sweep_inv_incremental_elim g fp c =
  reveal_opaque (`%sweep_inv_incremental) (sweep_inv_incremental g fp c);
  derived_clauses g c

/// The sweep phase at a state that is the derived one: the form the
/// stop-the-world step lemmas take.
let inv_st (g: heap) (fp: U64.t) (st: sweep_state) : prop =
  sweep_inv_incremental g fp st.cursor /\ st == state_at g st.cursor

let inv_st_elim (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires inv_st g fp st)
          (ensures (let c = U64.v st.cursor in
                    c % 8 == 0 /\ c <= heap_size /\ W.reaches g zero_addr c /\
                    heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                    well_formed_heap_with (free_incremental st.cursor) g /\
                    behind_swept g c /\ front_unswept g c /\
                    no_adjacent_free g c /\ ends_free g c (prev_free g st) /\
                    tail_ok g c st.swept_tail /\ frag_ok g c st.last_fragment /\
                    FLA.fl_ascending g fp))
  = sweep_inv_incremental_elim g fp st.cursor

let inv_st_intro (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires (let c = U64.v st.cursor in
                     c % 8 == 0 /\ c <= heap_size /\ W.reaches g zero_addr c /\
                     heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                     well_formed_heap_with (free_incremental st.cursor) g /\
                     behind_swept g c /\ front_unswept g c /\
                     no_adjacent_free g c /\ ends_free g c (prev_free g st) /\
                     tail_ok g c st.swept_tail /\ frag_ok g c st.last_fragment /\
                     FLA.fl_ascending g fp))
          (ensures inv_st g fp st)
  = caches_derived g st;
    reveal_opaque (`%sweep_inv_incremental) (sweep_inv_incremental g fp st.cursor)

/// ---------------------------------------------------------------------------
/// The shape
/// ---------------------------------------------------------------------------

let sweep_inv_incremental_iff g fp c =
  reveal_opaque (`%sweep_inv_incremental) (sweep_inv_incremental g fp c);
  reveal_opaque (`%sweep_shape) (sweep_shape g fp c)

let sweep_shape_elim g fp c =
  reveal_opaque (`%sweep_shape) (sweep_shape g fp c);
  derived_clauses g c

let sweep_shape_intro g fp c =
  reveal_opaque (`%sweep_shape) (sweep_shape g fp c)

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

let behind_swept_elim g c p
  = reveal_opaque (`%behind_swept) (behind_swept g c)

let marked_survive_elim g0 g p = reveal_opaque (`%marked_survive) (marked_survive g0 g)

let marked_survive_intro (g0 g: heap)
  (pf: (p: hp_addr -> Lemma (requires pos g0 p /\ black_at g0 p)
         (ensures pos g p /\ not (blue_at g p) /\ wz_at g p == wz_at g0 p /\
                  getTag (read_word g p) == getTag (read_word g0 p) /\
                  (forall (a: hp_addr). U64.v p < U64.v a /\ U64.v a < W.bnext g0 p ==>
                     read_word g a == read_word g0 a))))
  : Lemma (marked_survive g0 g)
  = reveal_opaque (`%marked_survive) (marked_survive g0 g);
    FStar.Classical.forall_intro (FStar.Classical.move_requires pf)

let survivors_were_marked_elim g0 g c p = reveal_opaque (`%survivors_were_marked) (survivors_were_marked g0 g c)

let survivors_were_marked_intro (g0 g: heap) (c: nat)
  (pf: (p: hp_addr -> Lemma (requires pos g p /\ U64.v p < c /\ not (blue_at g p))
                           (ensures pos g0 p /\ black_at g0 p)))
  : Lemma (survivors_were_marked g0 g c)
  = reveal_opaque (`%survivors_were_marked) (survivors_were_marked g0 g c);
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

/// A non-free block, at its header.
let live_pos (g: heap) (c: nat) (q: hp_addr) : bool =
  pos g q && not (blue_at g q) && not (white_at g q && U64.v q >= c)

let live_obj (g: heap) (st: sweep_state) (x: obj_addr)
  : Lemma (requires U64.v st.cursor % 8 == 0)
          (ensures in_use (free_incremental st.cursor) g x == live_pos g (U64.v st.cursor) (hd_address x))
  = obj_pos g x; colour_of g x

/// ---------------------------------------------------------------------------
/// Headers
/// ---------------------------------------------------------------------------

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

/// The reference heap of the sweep phase at cursor `c`.
let ref_of (g: heap) (c: nat) : GTot heap =
  recolour (fun (a: hp_addr) -> U64.v a < c && white_at g a) g zero_addr

let ref_read (g: heap) (c: nat) (a: hp_addr)
  : Lemma (read_word (ref_of g c) a ==
           (if pos g a && U64.v a < c && white_at g a then black_header (read_word g a)
            else read_word g a))
  = recolour_read (fun (a: hp_addr) -> U64.v a < c && white_at g a) g zero_addr a

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

/// A non-free block is black in the reference heap,
/// and the reference heap has the same block there.
let ref_block (g: heap) (fp: U64.t) (st: sweep_state) (q: hp_addr)
  : Lemma (requires inv_st g fp st)
          (ensures (let c = U64.v st.cursor in
                    let r = ref_of g c in
                    (live_pos g c q <==> pos r q /\ black_at r q) /\
                    (pos r q ==> same_block g r q) /\
                    (U64.v q >= c ==> read_word r q == read_word g q)))
  = inv_st_elim g fp st;
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
  : Lemma (requires inv_st g fp st /\ W.reaches g zero_addr (U64.v p) /\
                    U64.v p < U64.v st.cursor)
          (ensures swept_block (ref_of g (U64.v st.cursor)) g p)
  = inv_st_elim g fp st;
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
      assert (marked_block r g p)
    end else begin
      dead_run_one r p;
      assert (free_run r g p)
    end

let to_ref (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires inv_st g fp st)
          (ensures (let r = ref_of g (U64.v st.cursor) in sweep_inv r g fp st /\ sweep_g0 r))
  = inv_st_elim g fp st;
    let c = U64.v st.cursor in
    let r = ref_of g c in
    ref_walk g c;
    front_unchanged_intro r g c (fun a -> ref_read g c a);
    behind_ok_intro r g c (fun p -> swept_of g fp st p);
    W.reaches_end_of_dense g;
    W.dense_of_reaches_end r (W.walk_end g zero_addr);
    sweep_inv_intro r g fp st

/// ---------------------------------------------------------------------------
/// After a step, against the reference heap
/// ---------------------------------------------------------------------------

/// Against a reference heap `r`, a heap `g'` that satisfies the
/// stop-the-world invariant at `c'` keeps exactly the blocks black in `r`
/// (and no others) as non-free blocks, with their contents.
let after_live (r g': heap) (c': nat) (q: hp_addr)
  : Lemma (requires W.reaches r zero_addr c' /\ W.reaches g' zero_addr c' /\
                    front_unchanged r g' c' /\ behind_ok r g' c' /\ front_unswept r c')
          (ensures (live_pos g' c' q <==> pos r q /\ black_at r q) /\
                   (pos r q /\ black_at r q ==> same_block r g' q /\ W.bnext g' q == W.bnext r q))
  = if U64.v q >= c' then begin
      Phase.front_pos r g' c' q;
      if pos r q then front_unswept_elim r c' q;
      let body (a: hp_addr)
        : Lemma (requires U64.v q < U64.v a) (ensures read_word g' a == read_word r a)
        = front_unchanged_elim r g' c' a
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
let target_moves (g g': heap) (free free': free_def) (src dst: obj_addr)
  : Lemma (requires well_formed_heap_with free g /\ free_def_ok free' /\
                    (forall (x: obj_addr). in_use free' g' x == in_use free g x) /\
                    (forall (x: obj_addr). in_use free g x ==> same_block g g' (hd_address x)) /\
                    in_use free' g' src /\ scannable g' src /\ points_to g' src dst)
          (ensures in_use free' g' (resolve_object dst g') /\
                   infix_addr_wf g' (objects zero_addr g') dst)
  = assert (in_use free g src);
    src_fields g g' src dst;
    colour_of g src; colour_of g' src;
    wosize_of_object_bound src g';
    assert (scannable g src /\ points_to g src dst);
    points_to_target_not_free free g src dst;
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
      in_use_not_blue free' g' t;
      infix_addr_wf_transfer g g' (objects zero_addr g) (objects zero_addr g') dst
    end else begin
      resolve_non_infix dst g;
      colour_of g dst; colour_of g' dst;
      is_infix_spec dst g; is_infix_spec dst g';
      resolve_non_infix dst g';
      infix_addr_wf_non_infix g' (objects zero_addr g') dst
    end

/// **Well-formedness, transported**: a change after which the non-free blocks
/// under `free'` are those non-free under `free` before, with the same size,
/// tag and fields, keeps the pointer clauses.
let wf_transport g g' free free'
  = wf_with_parts ();
    Edit.part1_holds g';
    pointers_lead_to_non_free_intro free' g' (fun src dst -> target_moves g g' free free' src dst);
    interior_pointers_valid_intro free' g' (fun src dst -> target_moves g g' free free' src dst)

/// ---------------------------------------------------------------------------
/// Changes that keep the walk and the headers
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let same_heads_facts g g' =
  W.walk_congr g g' zero_addr;
  let hd (x: obj_addr)
    : Lemma (Seq.mem x (objects zero_addr g) ==> read_word g' (hd_address x) == read_word g (hd_address x))
    = obj_pos g x
  in
  FStar.Classical.forall_intro hd;
  let col (x: obj_addr)
    : Lemma ((is_white x g' <==> is_white x g) \/ ~(Seq.mem x (objects zero_addr g)))
    = obj_pos g x; colour_of g x; colour_of g' x
  in
  FStar.Classical.forall_intro col;
  let blu (x: obj_addr)
    : Lemma ((is_blue x g' <==> is_blue x g) \/ ~(Seq.mem x (objects zero_addr g)))
    = obj_pos g x; colour_of g x; colour_of g' x
  in
  FStar.Classical.forall_intro blu;
  let vw (x: obj_addr) (free: free_def)
    : Lemma (free_def_ok free ==> in_use free g' x == in_use free g x)
    = if FStar.IndefiniteDescription.strong_excluded_middle (free_def_ok free) then begin
        free_def_ok_elim free;
        if Seq.mem x (objects zero_addr g) then in_use_is_determined_from_header free g g' x
      end
  in
  FStar.Classical.forall_intro_2 vw;
  Edit.cells_transfer g g'
#pop-options

#push-options "--z3rlimit 20"
let shape_transport g g' fp c0 =
  sweep_shape_elim g fp c0;
  same_heads_facts g g';
  let c = U64.v c0 in
  W.reaches_end_of_dense g;
  W.reaches_refl g zero_addr;
  W.dense_of_reaches_end g' (W.walk_end g zero_addr);
  behind_swept_intro g' c (fun p -> behind_swept_elim g c p);
  front_unswept_intro g' c (fun p -> front_unswept_elim g c p);
  let na (p q: hp_addr)
    : Lemma (requires W.reaches g' zero_addr (U64.v p) /\ W.can_step g' p /\
                      W.bnext g' p == U64.v q /\ U64.v q < c /\ blue_at g' p)
            (ensures not (blue_at g' q))
    = W.reaches_snoc g zero_addr p;
      no_adjacent_free_elim g c p q
  in
  no_adjacent_free_intro g' c na;
  sweep_shape_intro g' fp c0
#pop-options

let state_at_heads g g' c =
  same_heads_facts g g';
  let n = U64.v c in
  (if n > 0 then max_cell_below_congr g g' (n - 1));
  if n >= U64.v zero_addr + 8 && n < heap_size && n % 8 = 0 &&
     W.reaches g zero_addr (n - 8)
  then assert (read_word g' (mk_hp_addr (n - 8)) == read_word g (mk_hp_addr (n - 8)))

let body_word g p a =
  let aux (x: nat) : Lemma (W.reaches g zero_addr x ==> x <> U64.v a)
    = if W.reaches g zero_addr x && x = U64.v a then Edit.no_pos_inside g p x in
  FStar.Classical.forall_intro aux;
  fl_cell_iff g a;
  if is_obj a && U64.v a >= U64.v zero_addr + 8 then begin
    let q = mk_hp_addr (U64.v a - 8) in
    if W.reaches g zero_addr (U64.v q) && U64.v q > U64.v p then Edit.no_pos_inside g p (U64.v q)
  end

#push-options "--z3rlimit 20"
let body_write g fp p a v =
  body_word g p a;
  Edit.write_off_walk g a v;
  let g' = write_word g a v in
  Edit.cells_transfer g g';
  let nx (x: U64.t)
    : Lemma (requires FreeList.fl_cell g x) (ensures FreeList.fl_next g' x == FreeList.fl_next g x)
    = FLA.fl_cell_facts g x;
      read_write_different g a (x <: hp_addr) v
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires nx);
  if FStar.IndefiniteDescription.strong_excluded_middle (FLA.fl_ascending g fp)
  then FLA.fl_ascending_transfer g g' fp
#pop-options

/// ---------------------------------------------------------------------------
/// Pointer targets across a change
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let storable_transfer g g' free free' w =
  if is_pointer w then begin
    let dst : obj_addr = w in
    let t = resolve_object dst g in
    if is_infix dst g then begin
      infix_addr_wf_elim g (objects zero_addr g) dst;
      parent_closure_addr_nat_spec dst g;
      resolve_infix_spec dst g;
      hd_address_spec dst; hd_address_spec t;
      colour_of g t;
      W.bnext_facts g (hd_address t);
      assert (same_block g g' (hd_address t));
      assert (read_word g' (hd_address dst) == read_word g (hd_address dst));
      resolve_object_locality dst g g';
      resolve_object_locality t g g';
      colour_of g' t;
      is_closure_spec t g; is_closure_spec t g';
      assert (in_use free' g' t);
      in_use_not_blue free' g' t;
      infix_addr_wf_transfer g g' (objects zero_addr g) (objects zero_addr g') dst
    end else begin
      resolve_non_infix dst g;
      resolve_object_locality dst g g';
      resolve_non_infix dst g';
      infix_addr_wf_non_infix g' (objects zero_addr g') dst
    end
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Start
/// ---------------------------------------------------------------------------

let start_target (g0: heap) (src dst: obj_addr)
  : Lemma (requires well_formed_heap g0 /\ Mark.noGreyObjects g0 /\ Mark.tri_color_invariant g0 /\
                    in_use (free_incremental sweep_start.cursor) g0 src /\ scannable g0 src /\ points_to g0 src dst)
          (ensures in_use (free_incremental sweep_start.cursor) g0 (resolve_object dst g0) /\
                   infix_addr_wf g0 (objects zero_addr g0) dst)
  = W.objects_mem_iff g0 zero_addr src;
    Mark.color_exhaustive src g0; Mark.colors_exclusive src g0;
    assert (is_black src g0);
    points_to_target_not_free free_stw g0 src dst;
    let t = resolve_object dst g0 in
    assert (points_to g0 src dst);
    assert (~(is_white t g0));
    Mark.color_exhaustive t g0; Mark.colors_exclusive t g0

let sweep_inv_incremental_start g0 fp =
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
  wf_with_parts ();
  pointers_lead_to_non_free_intro (free_incremental sweep_start.cursor) g0 (fun src dst -> start_target g0 src dst);
  interior_pointers_valid_intro (free_incremental sweep_start.cursor) g0 (fun src dst -> start_target g0 src dst);
  inv_st_intro g0 fp sweep_start;
  W.reaches_refl g0 zero_addr;
  front_unchanged_intro g0 g0 c (fun _ -> ());
  marked_survive_intro g0 g0 (fun _ -> ());
  survivors_were_marked_intro g0 g0 c (fun p -> W.reaches_bounds g0 zero_addr (U64.v p))

/// ---------------------------------------------------------------------------
/// Step
/// ---------------------------------------------------------------------------

/// The step, run against the reference heap.
let step_ref (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires inv_st g fp st /\ U64.v st.cursor + 8 < heap_size)
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
    inv_st_elim g fp st;
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

/// One step's effect on the blocks: non-free before iff after, same contents.
let step_live (g: heap) (fp: U64.t) (st: sweep_state) (q: hp_addr)
  : Lemma (requires inv_st g fp st /\ U64.v st.cursor + 8 < heap_size)
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
  : Lemma (requires inv_st g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    Seq.mem x (objects zero_addr g') ==> ~(is_infix x g')))
  = step_ref g fp st;
    inv_st_elim g fp st;
    let c = U64.v st.cursor in
    let r = ref_of g c in
    let (g', fp', st') = sweep_step g fp st in
    let c' = U64.v st'.cursor in
    sweep_inv_elim r g' fp' st';
    ref_walk g c;
    wf_with_parts ();
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

/// The pending-free set after a step is part of the one before.
let step_pending_free (g: heap) (fp: U64.t) (st: sweep_state) (x: obj_addr)
  : Lemma (requires inv_st g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    pending_free st'.cursor g' x ==> pending_free st.cursor g x))
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
  : Lemma (requires inv_st g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    heap_objects_dense g' /\ Seq.length (objects zero_addr g') > 0))
  = step_ref g fp st;
    inv_st_elim g fp st;
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
        = front_unchanged_elim r g' c' w in
      FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
      W.walk_frame_from r g' ca;
      W.reaches_trans g' zero_addr ca e
    end;
    W.dense_of_reaches_end g' e

/// Behind and in front of the cursor, after a step.
let step_regions (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires inv_st g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    behind_swept g' (U64.v st'.cursor) /\ front_unswept g' (U64.v st'.cursor)))
  = step_ref g fp st;
    inv_st_elim g fp st;
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

let step_st (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires inv_st g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    inv_st g' fp' st' /\
                    (forall (x: obj_addr). in_use (free_incremental st'.cursor) g' x == in_use (free_incremental st.cursor) g x) /\
                    (forall (x: obj_addr). in_use (free_incremental st.cursor) g x ==> same_block g g' (hd_address x)) /\
                    (forall (x: obj_addr). pending_free st'.cursor g' x ==> pending_free st.cursor g x) /\
                    U64.v st'.cursor > U64.v st.cursor /\ U64.v st'.cursor <= heap_size))
  = step_ref g fp st;
  step_dense g fp st;
  step_regions g fp st;
  inv_st_elim g fp st;
  let c = U64.v st.cursor in
  let r = ref_of g c in
  let (g', fp', st') = sweep_step g fp st in
  let c' = U64.v st'.cursor in
  sweep_inv_elim r g' fp' st';
  W.bnext_facts g st.cursor;
  // well formed given what counts as free, with the (smaller) pending-free set
  let keep (x: obj_addr)
    : Lemma ((in_use (free_incremental st'.cursor) g' x == in_use (free_incremental st.cursor) g x) /\
             (in_use (free_incremental st.cursor) g x ==> same_block g g' (hd_address x)))
    = live_obj g st x; live_obj g' st' x;
      step_live g fp st (hd_address x)
  in
  FStar.Classical.forall_intro keep;
  wf_with_parts ();
  FStar.Classical.forall_intro (step_part4 g fp st);
  free_incremental_ok st'.cursor;
  wf_transport g g' (free_incremental st.cursor) (free_incremental st'.cursor);
  inv_st_intro g' fp' st';
  FStar.Classical.forall_intro (step_pending_free g fp st)

let sweep_inv_incremental_step g fp c = step_st g fp (state_at g c)

let pending_free_within_step g fp c dead =
  step_st g fp (state_at g c)

/// `same_block` composes.
let same_block_trans (g g' g'': heap) (q: hp_addr)
  : Lemma (requires same_block g g' q /\ same_block g' g'' q)
          (ensures same_block g g'' q)
  = W.bnext_facts g q; W.bnext_facts g' q

#push-options "--fuel 1"
let sweep_steps_unfold g fp st k = ()
#pop-options

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
    if not (sweep_done st.cursor) then step_st g fp st;
    if k = 0 || sweep_done st.cursor || not (can_sweep g st) then ()
    else begin
      step_st g fp st;
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

/// ---------------------------------------------------------------------------
/// Step, stop-the-world
/// ---------------------------------------------------------------------------

let stw_marked (g0 g: heap) (fp: U64.t) (st: sweep_state) (p: hp_addr)
  : Lemma (requires inv_st g fp st /\ stw_rel g0 g (U64.v st.cursor) /\
                    U64.v st.cursor + 8 < heap_size /\ pos g0 p /\ black_at g0 p)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    pos g' p /\ not (blue_at g' p) /\ wz_at g' p == wz_at g0 p /\
                    getTag (read_word g' p) == getTag (read_word g0 p) /\
                    (forall (a: hp_addr). U64.v p < U64.v a /\ U64.v a < W.bnext g0 p ==>
                       read_word g' a == read_word g0 a)))
  = let c = U64.v st.cursor in
    marked_survive_elim g0 g p;
    if U64.v p >= c then front_unchanged_elim g0 g c p;
    step_live g fp st p

let stw_behind (g0 g: heap) (fp: U64.t) (st: sweep_state) (p: hp_addr)
  : Lemma (requires inv_st g fp st /\ stw_rel g0 g (U64.v st.cursor) /\
                    U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    pos g' p /\ U64.v p < U64.v st'.cursor /\ not (blue_at g' p) ==>
                      pos g0 p /\ black_at g0 p))
  = step_ref g fp st;
    inv_st_elim g fp st;
    let c = U64.v st.cursor in
    let (g', fp', st') = sweep_step g fp st in
    let c' = U64.v st'.cursor in
    step_live g fp st p;
    if pos g' p && U64.v p < c' && not (blue_at g' p) then begin
      if U64.v p < c then survivors_were_marked_elim g0 g c p
      else begin
        if U64.v p > c then Edit.no_pos_inside g st.cursor (U64.v p);
        front_unswept_elim g c p;
        front_unchanged_elim g0 g c p
      end
    end

let step_stw_st (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires inv_st g fp st /\ stw_rel g0 g (U64.v st.cursor) /\
                    U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    stw_rel g0 g' (U64.v st'.cursor)))
  = step_ref g fp st;
  inv_st_elim g fp st;
  let c = U64.v st.cursor in
  let r = ref_of g c in
  let (g', fp', st') = sweep_step g fp st in
  let c' = U64.v st'.cursor in
  sweep_inv_elim r g' fp' st';
  front_unchanged_elim g0 g c st.cursor;
  W.reaches_snoc g0 zero_addr st.cursor;
  let fs (a: hp_addr) : Lemma (requires U64.v a >= c') (ensures read_word g' a == read_word g0 a)
    = front_unchanged_elim r g' c' a;
      ref_read g c a;
      front_unchanged_elim g0 g c a
  in
  front_unchanged_intro g0 g' c' fs;
  marked_survive_intro g0 g' (fun p -> stw_marked g0 g fp st p);
  survivors_were_marked_intro g0 g' c' (fun p -> stw_behind g0 g fp st p)

let sweep_inv_stw_step g0 g fp c = step_stw_st g0 g fp (state_at g c)

#push-options "--z3rlimit 20"
let rec steps_stw_aux (g0 g: heap) (fp: U64.t) (st: sweep_state) (k: nat)
  : Lemma (requires inv_st g fp st /\ stw_rel g0 g (U64.v st.cursor))
          (ensures (let (g', fp', st') = sweep_steps g fp st k in
                    stw_rel g0 g' (U64.v st'.cursor)))
          (decreases k)
  = sweep_steps_unfold g fp st k;
    if not (sweep_done st.cursor) then step_st g fp st;
    if k = 0 || sweep_done st.cursor || not (can_sweep g st) then ()
    else begin
      step_stw_st g0 g fp st;
      let (g1, fp1, st1) = sweep_step g fp st in
      steps_stw_aux g0 g1 fp1 st1 (k - 1)
    end
#pop-options

let sweep_inv_stw_steps g0 g fp c k = steps_stw_aux g0 g fp (state_at g c) k

#push-options "--z3rlimit 20"
let rec steps_done_aux (g: heap) (fp: U64.t) (st: sweep_state) (k: nat)
  : Lemma (requires inv_st g fp st /\ k * 8 >= heap_size - U64.v st.cursor)
          (ensures (let (g', fp', st') = sweep_steps g fp st k in sweep_done st'.cursor))
          (decreases k)
  = sweep_steps_unfold g fp st k;
    inv_st_elim g fp st;
    if sweep_done st.cursor then ()
    else begin
      step_st g fp st;
      let (g1, fp1, st1) = sweep_step g fp st in
      inv_st_elim g1 fp1 st1;
      assert (U64.v st1.cursor >= U64.v st.cursor + 8);
      steps_done_aux g1 fp1 st1 (k - 1)
    end
#pop-options

let sweep_steps_done g fp c k = steps_done_aux g fp (state_at g c) k

let sweep_inv_incremental_ready g fp c =
  let st = state_at g c in
  to_ref g fp st;
  sweep_inv_facts (ref_of g (U64.v st.cursor)) g fp st
