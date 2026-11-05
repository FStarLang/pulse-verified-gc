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

let sweep_inv_incremental_intro g fp st
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

let front_unchanged_elim g0 g c a = reveal_opaque (`%front_unchanged) (front_unchanged g0 g c)

let front_unchanged_intro g0 g c pf =
  reveal_opaque (`%front_unchanged) (front_unchanged g0 g c);
  FStar.Classical.forall_intro (FStar.Classical.move_requires pf)

let marked_survive_elim g0 g p = reveal_opaque (`%marked_survive) (marked_survive g0 g)

let marked_survive_intro g0 g pf
  = reveal_opaque (`%marked_survive) (marked_survive g0 g);
    FStar.Classical.forall_intro (FStar.Classical.move_requires pf)

let survivors_were_marked_elim g0 g c p = reveal_opaque (`%survivors_were_marked) (survivors_were_marked g0 g c)

let survivors_were_marked_intro g0 g c pf
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

let live_obj g c x = obj_pos g x; colour_of g x

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

#push-options "--z3rlimit 20"
let sweep_inv_incremental_start g0 fp =
  let c = U64.v zero_addr in
  W.reaches_refl g0 zero_addr;
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
  wf_parts ();
  wf_with_parts ();
  pointers_lead_to_non_free_intro (free_incremental sweep_start.cursor) g0 (fun src dst -> start_target g0 src dst);
  interior_pointers_valid_intro (free_incremental sweep_start.cursor) g0 (fun src dst -> start_target g0 src dst);
  sweep_inv_incremental_intro g0 fp sweep_start
#pop-options

let sweep_inv_stw_start g0 fp =
  let c = U64.v zero_addr in
  sweep_inv_incremental_start g0 fp;
  W.reaches_refl g0 zero_addr;
  front_unchanged_intro g0 g0 c (fun _ -> ());
  marked_survive_intro g0 g0 (fun _ -> ());
  survivors_were_marked_intro g0 g0 c (fun p -> W.reaches_bounds g0 zero_addr (U64.v p))

/// ---------------------------------------------------------------------------
/// Up to `k` steps
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let sweep_steps_unfold g fp st k = ()
#pop-options
