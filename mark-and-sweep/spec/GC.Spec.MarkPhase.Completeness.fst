module GC.Spec.MarkPhase.Completeness

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph.Within

module U64 = FStar.UInt64
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module MPA = GC.Spec.MarkPhase.Alloc
module S = GC.Spec.MarkPhase.Slice
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module SPC = GC.Spec.SweepPhase.Completeness
module SPE = GC.Spec.SweepPhase.Intrinsic.End
module SL = GC.Spec.SweepPhase.Slice
module FLA = GC.Spec.FreeList.Ascending
module AC = GC.Spec.Allocator.Cursor
module AP = GC.Spec.Allocator.Phase
module SA = GC.Spec.Allocator
module Ph = GC.Spec.Phase
module FT = GC.Spec.FieldTarget
module HG = GC.Spec.HeapGraph
module W = GC.Spec.Walk
module Util = GC.Spec.SweepPhase.Util
module Header = GC.Lib.Header

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// Reachable when the cycle starts
/// ---------------------------------------------------------------------------

let reachable_held g held x =
  reach_within_refl (MP.field_edge g) (fun _ -> True) x

#push-options "--fuel 1 --ifuel 1"
let rec path_closed (g: heap) (c: obj_addr -> prop) (x y: obj_addr) (l: list obj_addr)
  : Lemma (requires c x /\ (forall (u v: obj_addr). c u /\ MP.field_edge g u v ==> c v) /\
                    path_within (MP.field_edge g) (fun _ -> True) x y l)
          (ensures c y) (decreases l)
  = match l with
    | [] -> ()
    | z :: rest -> path_closed g c z y rest
#pop-options

let reachable_closed g held c x =
  eliminate exists (r: obj_addr). held r /\ reach_within (MP.field_edge g) (fun _ -> True) r x
  with eliminate exists (l: list obj_addr). path_within (MP.field_edge g) (fun _ -> True) r x l
       with path_closed g c r x l

/// ---------------------------------------------------------------------------
/// The account
/// ---------------------------------------------------------------------------

let unaccounted_ok s =
  reveal_opaque (`%free_def_ok) free_def_ok;
  let det (g g': heap) (x: obj_addr)
    : Lemma ((is_block g x <==> is_block g' x) /\ read_word g (hd_address x) == read_word g' (hd_address x) ==>
             unaccounted s g x == unaccounted s g' x)
    = if read_word g (hd_address x) = read_word g' (hd_address x) then MM.header_kept_facts g g' x
  in
  FStar.Classical.forall_intro_3 det

let in_use_unaccounted s g x = ()

/// A non-free block for the account: a block, not blue.
let in_use_block (s: obj_addr -> prop) (g: heap) (x: obj_addr)
  : Lemma (requires in_use (unaccounted s) g x)
          (ensures Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ in_use free_stw g x)
  = ()

/// The account's pointer clauses, from well-formedness: every white target
/// of an edge out of a block that is not free for the account is in `s`.
let account_wf_intro (s: obj_addr -> prop) (g: heap)
  (h: (src: obj_addr) -> (t: obj_addr) ->
      Lemma (requires in_use (unaccounted s) g src /\ MP.field_edge g src t /\ is_white t g)
            (ensures s t))
  : Lemma (requires well_formed_heap g) (ensures well_formed_heap_with (unaccounted s) g)
  = let un = unaccounted s in
    wf_with_parts ();
    let tgt (src dst: obj_addr)
      : Lemma (requires in_use un g src /\ scannable g src /\ points_to g src dst)
              (ensures in_use un g (resolve_object dst g) /\
                       infix_addr_wf g (objects zero_addr g) dst)
      = points_to_target_not_free free_stw g src dst;
        let t = resolve_object dst g in
        assert (MP.field_edge g src t);
        if is_white t g then h src t
    in
    pointers_lead_to_non_free_intro un g tgt;
    interior_pointers_valid_intro un g tgt

/// An edge out of a block that is not free for the account ends at one.
let edge_accounted (s: obj_addr -> prop) (g: heap) (u t: obj_addr)
  : Lemma (requires well_formed_heap_with (unaccounted s) g /\ in_use (unaccounted s) g u /\
                    MP.field_edge g u t)
          (ensures in_use (unaccounted s) g t)
  = eliminate exists (c: obj_addr). points_to g u c /\ resolve_object c g == t
    with points_to_target_not_free (unaccounted s) g u c

/// ---------------------------------------------------------------------------
/// Start
/// ---------------------------------------------------------------------------

let account_start g held =
  let s = reachable g held in
  let dk (x: obj_addr)
    : Lemma (requires Seq.mem x (objects zero_addr g) /\ (is_gray x g \/ is_black x g)) (ensures s x)
    = reachable_held g held x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires dk);
  let h (src t: obj_addr)
    : Lemma (requires in_use (unaccounted s) g src /\ MP.field_edge g src t /\ is_white t g)
            (ensures s t)
    = Mark.colors_exclusive src g;
      Mark.color_exhaustive src g;
      if is_white src g then ()
      else dk src;
      eliminate exists (r: obj_addr). held r /\ reach_within (MP.field_edge g) (fun _ -> True) r src
      with begin
        reach_within_edge (MP.field_edge g) (fun _ -> True) src t;
        reach_within_trans (MP.field_edge g) (fun _ -> True) r src t
      end
  in
  account_wf_intro s g h

/// ---------------------------------------------------------------------------
/// Recolouring a block that is not free
/// ---------------------------------------------------------------------------

/// Greying or blackening a block that is not blue is a recolouring, and
/// keeps every other header, every resolution and every header fact but the
/// colour.
let recolour (g: heap) (t: obj_addr) (c: color)
  : Lemma (requires Seq.mem t (objects zero_addr g) /\ ~(is_blue t g) /\
                    (c == Header.Gray \/ c == Header.Black))
          (ensures (let g' = set_object_color t g c in
                    AP.recoloured g g' /\
                    objects zero_addr g' == objects zero_addr g /\
                    (c == Header.Gray ==> is_gray t g') /\ (c == Header.Black ==> is_black t g') /\
                    ~(is_white t g') /\ ~(is_blue t g') /\
                    (forall (y: obj_addr). y <> t ==> read_word g' (hd_address y) == read_word g (hd_address y)) /\
                    (forall (y: obj_addr). resolve_object y g' == resolve_object y g /\
                                      is_infix y g' == is_infix y g /\
                                      is_closure y g' == is_closure y g /\
                                      wosize_of_object y g' == wosize_of_object y g) /\
                    is_no_scan t g' == is_no_scan t g))
  = let g' = set_object_color t g c in
    let hd = hd_address t in
    let v = colorHeader (read_word g hd) c in
    (if c = Header.Gray then begin makeGray_eq t g; makeGray_spec t g end
     else begin makeBlack_eq t g; makeBlack_spec t g end);
    assert (g' == write_word g hd v);
    read_write_same g hd v;
    colorHeader_preserves_wosize (read_word g hd) c;
    colorHeader_getColor (read_word g hd) c;
    color_preserves_tag t g c;
    tag_of_object_spec t g; tag_of_object_spec t g';
    color_of_object_spec t g; color_of_object_spec t g';
    is_blue_iff t g; is_blue_iff t g';
    is_white_iff t g'; is_gray_iff t g'; is_black_iff t g';
    AP.recolour_one g t v;
    color_change_preserves_objects g t c;
    color_preserves_is_no_scan t g c;
    let other (y: obj_addr) : Lemma (y <> t ==> read_word g' (hd_address y) == read_word g (hd_address y)) =
      if y <> t then begin
        hd_address_injective y t;
        color_change_preserves_other_read t (hd_address y) g c
      end
    in
    FStar.Classical.forall_intro other;
    let any (y: obj_addr)
      : Lemma (resolve_object y g' == resolve_object y g /\ is_infix y g' == is_infix y g /\
               is_closure y g' == is_closure y g /\ wosize_of_object y g' == wosize_of_object y g)
      = color_change_preserves_resolve t y g c;
        color_change_preserves_is_infix t y g c;
        color_change_preserves_is_closure t y g c;
        color_change_preserves_wosize_any t y g c
    in
    FStar.Classical.forall_intro any

/// Recolouring an accounted block dark keeps the account, and which blocks
/// are free for it.
let account_recolour (s: obj_addr -> prop) (g: heap) (t: obj_addr) (c: color)
  : Lemma (requires mark_account s g /\ well_formed_heap g /\
                    Seq.mem t (objects zero_addr g) /\ ~(is_blue t g) /\ s t /\
                    (c == Header.Gray \/ c == Header.Black))
          (ensures (let g' = set_object_color t g c in
                    mark_account s g' /\ well_formed_heap g' /\
                    (forall (y: obj_addr). in_use (unaccounted s) g' y == in_use (unaccounted s) g y)))
  = let g' = set_object_color t g c in
    let un = unaccounted s in
    recolour g t c;
    unaccounted_ok s;
    Mark.color_change_preserves_wf g t c;
    let iu (y: obj_addr) : Lemma (in_use un g' y == in_use un g y) =
      if y = t then ()
      else in_use_is_determined_from_header un g g' y
    in
    FStar.Classical.forall_intro iu;
    AP.recoloured_wf g g' un un;
    let dk (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\ (is_gray y g' \/ is_black y g'))
              (ensures s y)
      = if y <> t then MM.header_kept_facts g g' y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires dk)

let account_grey s g t =
  makeGray_eq t g;
  Mark.colors_exclusive t g;
  recolour g t Header.Gray;
  account_recolour s g t Header.Gray

let account_darken s g w =
  if is_pointer w &&
     Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
     is_white (resolve_object (w <: obj_addr) g) g
  then account_grey s g (resolve_object (w <: obj_addr) g)

/// ---------------------------------------------------------------------------
/// Mark moves
/// ---------------------------------------------------------------------------

/// The field `k` of a block, as a word of its body.
let field_word (g: heap) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires blocks_fit g /\ Seq.mem x (objects zero_addr g) /\ U64.v k <= U64.v (wosize_of_object x g))
          (ensures U64.v x + (U64.v k - 1) * 8 + 8 <= heap_size /\
                   HG.get_field g x k == read_word g (U64.uint_to_t (U64.v x + (U64.v k - 1) * 8)))
  = hd_address_spec x;
    wosize_of_object_bound x g;
    FStar.Math.Lemmas.pow2_plus 3 54;
    assert_norm (pow2 3 == 8);
    HG.get_field_addr_eq g x k

let account_move s g g' =
  let un = unaccounted s in
  wf_with_parts ();
  unaccounted_ok s;
  eliminate S.grey_move g g' \/ S.black_move g g'
  with begin
    eliminate exists (x: obj_addr) (k: U64.t{U64.v k >= 1}).
      S.scan_target g x /\ U64.v k <= U64.v (wosize_of_object x g) /\ g' == S.scan_field g x k
    with begin
      let w = HG.get_field g x k in
      Mark.colors_exclusive x g;
      assert (s x);
      assert (in_use un g x);
      field_word g x k;
      let j : nat = U64.v k - 1 in
      (if is_pointer w then FT.wf_with_field un g x j);
      account_darken s g w
    end
  end
  and begin
    eliminate exists (x: obj_addr).
      Seq.mem x (objects zero_addr g) /\ is_gray x g /\
      (is_no_scan x g \/ S.fields_dark g x 1 (U64.v (wosize_of_object x g))) /\ g' == makeBlack x g
    with begin
      Mark.colors_exclusive x g;
      makeBlack_eq x g;
      account_recolour s g x Header.Black
    end
  end

let account_steps s g g' =
  let p (h: heap) : prop = mark_account s h /\ well_formed_heap h in
  let step (h h': heap) : Lemma (requires p h /\ S.mark_move h h') (ensures p h') =
    account_move s h h';
    S.mark_move_darker h h'
  in
  S.mark_steps_ind p step g g'

/// ---------------------------------------------------------------------------
/// What marking keeps
/// ---------------------------------------------------------------------------

let same_block_refl (g: heap) (q: hp_addr) : Lemma (SPI.same_block g g q) = ()

let same_block_trans (g1 g2 g3: heap) (q: hp_addr)
  : Lemma (requires SPI.same_block g1 g2 q /\ SPI.same_block g2 g3 q)
          (ensures SPI.same_block g1 g3 q)
  = ()

let mark_move_keeps_blocks g g' =
  eliminate S.grey_move g g' \/ S.black_move g g'
  with begin
    eliminate exists (x: obj_addr) (k: U64.t{U64.v k >= 1}).
      S.scan_target g x /\ U64.v k <= U64.v (wosize_of_object x g) /\ g' == S.scan_field g x k
    with begin
      let w = HG.get_field g x k in
      if is_pointer w &&
         Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
         is_white (resolve_object (w <: obj_addr) g) g
      then begin
        let t = resolve_object (w <: obj_addr) g in
        makeGray_eq t g;
        Mark.colors_exclusive t g;
        recolour g t Header.Gray;
        AP.recoloured_facts g g'
      end
    end
  end
  and begin
    eliminate exists (x: obj_addr).
      Seq.mem x (objects zero_addr g) /\ is_gray x g /\
      (is_no_scan x g \/ S.fields_dark g x 1 (U64.v (wosize_of_object x g))) /\ g' == makeBlack x g
    with begin
      Mark.colors_exclusive x g;
      makeBlack_eq x g;
      recolour g x Header.Black;
      AP.recoloured_facts g g'
    end
  end

let mark_steps_keep_blocks g g' =
  let p (h: heap) : prop =
    well_formed_heap h /\ objects zero_addr h == objects zero_addr g /\
    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
       SPI.same_block g h (hd_address x) /\ (is_blue x h <==> is_blue x g))
  in
  let step (h h': heap) : Lemma (requires p h /\ S.mark_move h h') (ensures p h') =
    mark_move_keeps_blocks h h';
    S.mark_move_darker h h';
    let tr (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g))
              (ensures SPI.same_block g h' (hd_address x))
      = same_block_trans g h h' (hd_address x)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires tr)
  in
  let q (x: obj_addr) : Lemma (SPI.same_block g g (hd_address x)) = same_block_refl g (hd_address x) in
  FStar.Classical.forall_intro q;
  S.mark_steps_ind p step g g'

/// ---------------------------------------------------------------------------
/// The program
/// ---------------------------------------------------------------------------

let account_load s g u t = edge_accounted s g u t

let account_write s g x a v =
  let g' = write_word g a v in
  unaccounted_ok s;
  MM.write_wf_with (unaccounted s) g x a v;
  MM.write_heads g x a v;
  let dk (y: obj_addr)
    : Lemma (requires Seq.mem y (objects zero_addr g') /\ (is_gray y g' \/ is_black y g'))
            (ensures s y)
    = ()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires dk)

/// A word of the body of `x` is its field `j`.
let body_field (g: heap) (x: obj_addr) (a: hp_addr)
  : Lemma (requires SPM.in_body g x a)
          (ensures (let j = (U64.v a - U64.v x) / 8 in
                    j < U64.v (wosize_of_object x g) /\ U64.v x + j * 8 + 8 <= heap_size /\
                    U64.uint_to_t (U64.v x + j * 8) == a))
  = FStar.Math.Lemmas.lemma_div_exact (U64.v a - U64.v x) 8

/// What the barrier's darkening keeps of a program write.
let darken_keeps_write (s: obj_addr -> prop) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires mark_account s g /\ well_formed_heap g /\ cycle_write s g x a v)
          (ensures (let g1 = MM.darken g (read_word g a) in
                    mark_account s g1 /\ SPM.program_write (unaccounted s) g1 x a v))
  = let un = unaccounted s in
    let w = read_word g a in
    unaccounted_ok s;
    wf_with_parts ();
    body_field g x a;
    let j = (U64.v a - U64.v x) / 8 in
    (if is_pointer w then FT.wf_with_field un g x j);
    account_darken s g w;
    if is_pointer w &&
       Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
       is_white (resolve_object (w <: obj_addr) g) g
    then begin
      let t = resolve_object (w <: obj_addr) g in
      let g1 = MM.darken g w in
      makeGray_eq t g;
      Mark.colors_exclusive t g;
      account_recolour s g t Header.Gray;
      recolour g t Header.Gray;
      (if x = t then color_preserves_is_no_scan t g Header.Gray
       else MM.header_kept_facts g g1 x);
      if is_pointer v && not (is_no_scan x g) then begin
        let vv : obj_addr = v in
        let objs = objects zero_addr g in
        infix_addr_wf_congr g g1 objs vv
      end
    end

let account_barrier s g x a v =
  darken_keeps_write s g x a v;
  account_write s (MM.darken g (read_word g a)) x a v

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

let unaccounted_or_new_ok s obj =
  unaccounted_ok s;
  reveal_opaque (`%free_def_ok) free_def_ok

let account_alloc s held g fp wz tag =
  let r = AC.alloc_phase g fp Ph.Marking wz tag in
  MPA.marking_alloc g held fp wz tag;
  if r.SA.obj_out <> 0UL then begin
    let g' = r.SA.heap_out in
    let obj : obj_addr = r.SA.obj_out in
    let s' = SPC.with_new s r.SA.obj_out in
    let un = unaccounted s in
    let un' = unaccounted_or_new s' obj in
    unaccounted_ok s;
    unaccounted_or_new_ok s' obj;
    MPA.free_or_new_ok obj;
    free_stw_ok ();
    wf_with_parts ();
    assert (MPA.marking_fresh g' held obj);
    let iu (x: obj_addr) : Lemma (in_use un' g' x == in_use un g x) =
      MPA.alloc_in_use g fp wz tag obj x;
      if x = obj then ()
      else if in_use free_stw g x then MM.header_kept_facts g g' x
      else ()
    in
    FStar.Classical.forall_intro iu;
    let kb (x: obj_addr) : Lemma (requires in_use un g x) (ensures SPI.same_block g g' (hd_address x)) = () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires kb);
    SPI.wf_transport g g' un un';
    let dk (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\ (is_gray y g' \/ is_black y g'))
              (ensures s' y)
      = if y = obj then ()
        else begin
          Mark.colors_exclusive y g';
          MPA.alloc_in_use g fp wz tag obj y;
          MM.header_kept_facts g g' y
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires dk)
  end

let account_fresh_write s g obj a v =
  let g' = write_word g a v in
  let free = unaccounted_or_new s obj in
  unaccounted_or_new_ok s obj;
  free_def_ok_elim free;
  Mark.colors_exclusive obj g;
  MM.write_heads g obj a v;
  SPI.same_heads_facts g g';
  wf_with_parts ();
  SPM.same_heads_part4 g g';
  Util.part1_holds g';
  let kb (y: obj_addr)
    : Lemma (requires in_use free g y) (ensures SPI.same_block g g' (hd_address y))
    = SPM.other_body g obj y a;
      SPI.obj_pos g y;
      let body (b: hp_addr)
        : Lemma (requires U64.v (hd_address y) < U64.v b /\ U64.v b < W.bnext g (hd_address y))
                (ensures read_word g' b == read_word g b)
        = read_write_different g a b v
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires body)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires kb);
  SPI.wf_transport g g' free free

let account_fresh_close s g obj =
  let fresh = unaccounted_or_new s obj in
  let un = unaccounted s in
  unaccounted_or_new_ok s obj;
  unaccounted_ok s;
  wf_with_parts ();
  free_def_ok_elim un;
  free_def_ok_elim fresh;
  Mark.colors_exclusive obj g;
  let closure (src: obj_addr) (j: nat)
    : Lemma (requires in_use un g src /\ ~(is_no_scan src g) /\
                      j < U64.v (wosize_of_object src g) /\ U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer w ==>
                      in_use un g (resolve_object (w <: obj_addr) g) /\
                      infix_addr_wf g (objects zero_addr g) (w <: obj_addr)))
    = let w = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
      if src = obj then assert (SPI.storable un g (SPM.field_val g obj j))
      else if is_pointer w then FT.wf_with_field fresh g src j
  in
  pointer_clauses_from_field_closure un g closure

/// ---------------------------------------------------------------------------
/// The end of marking, and the cycle
/// ---------------------------------------------------------------------------

let account_marked s g = ()

let cycle_handover s g =
  SPC.survivor_or_new_start g

let cycle_sweep_slice s g fp ph budget =
  match ph with
  | Ph.Idle -> ()
  | Ph.Sweeping c ->
      SL.sweep_slice_phase g fp c budget;
      let (g', fp', st') = SL.sweep_slice g fp (SPI.state_at g c) budget in
      if SPI.sweep_done st'.GC.Spec.FusedSweep.cursor then
        SPE.sweep_inv_incremental_end g' fp' st'.GC.Spec.FusedSweep.cursor

let cycle_sweep_alloc s g fp c wz tag =
  FStar.Classical.forall_intro (SPM.alloc_in_use g fp c wz tag)

let cycle_sweep_write s g fp c x a v =
  SPM.body_write_shape g fp c x a v;
  SPI.same_heads_facts g (write_word g a v);
  SPI.free_incremental_ok c

let cycle_weaken s s' g ph = ()

let cycle_complete s g = ()
