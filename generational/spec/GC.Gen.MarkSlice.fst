module GC.Gen.MarkSlice

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MarkState

module U64 = FStar.UInt64
module HG = GC.Spec.HeapGraph
module MM = GC.Spec.MarkPhase.Mutator
module S = GC.Spec.MarkPhase.Slice
module MB = GC.Impl.MarkBounded
module MBP = GC.Impl.MarkBoundedPrecondition
module SweepInv = GC.Spec.SweepInv
module Mark = GC.Spec.Mark
module Header = GC.Lib.Header

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The darkening the implementation runs
/// ---------------------------------------------------------------------------

let darken_spec_eq g st w cap =
  if is_pointer w then begin
    let t = resolve_object (w <: obj_addr) g in
    let h : hp_addr = U64.sub t mword in
    f_address_spec h;
    U64.v_inj (f_address h) t
  end

/// ---------------------------------------------------------------------------
/// Colours
/// ---------------------------------------------------------------------------

/// A colour change of `o` keeps the colours of every other block.
let cc_colours (o y: obj_addr) (g: heap) (c: color)
  : Lemma (requires o <> y)
          (ensures (let g' = set_object_color o g c in
                    (is_black y g' <==> is_black y g) /\ (is_white y g' <==> is_white y g) /\
                    (is_gray y g' <==> is_gray y g) /\ (is_blue y g' <==> is_blue y g)))
  = let g' = set_object_color o g c in
    color_change_preserves_other_color o y g c;
    is_black_iff y g; is_black_iff y g';
    is_white_iff y g; is_white_iff y g';
    is_gray_iff y g; is_gray_iff y g';
    is_blue_iff y g; is_blue_iff y g'

/// Greying a white block: only it changes colour, and it is grey.
let grey_facts (t: obj_addr) (g: heap)
  : Lemma (requires is_white t g)
          (ensures (let g' = makeGray t g in
                    objects zero_addr g' == objects zero_addr g /\
                    is_gray t g' /\ ~(is_white t g') /\ ~(is_blue t g') /\
                    (forall (y: obj_addr). {:pattern (is_gray y g')}
                       y <> t ==> (is_gray y g' <==> is_gray y g)) /\
                    (forall (y: obj_addr). {:pattern (is_white y g')}
                       y <> t ==> (is_white y g' <==> is_white y g)) /\
                    (forall (y: obj_addr). {:pattern (is_blue y g')}
                       y <> t ==> (is_blue y g' <==> is_blue y g))))
  = makeGray_eq t g;
    color_change_preserves_objects g t Header.Gray;
    makeGray_is_gray t g;
    Mark.colors_exclusive t (makeGray t g);
    let aux (y: obj_addr) : Lemma (y <> t ==>
        ((is_gray y (makeGray t g) <==> is_gray y g) /\
         (is_white y (makeGray t g) <==> is_white y g) /\
         (is_blue y (makeGray t g) <==> is_blue y g))) =
      if y <> t then cc_colours t y g Header.Gray
    in
    FStar.Classical.forall_intro aux

/// Blackening a block: only it changes colour, and it is not grey.
let black_facts (x: obj_addr) (g: heap)
  : Lemma (ensures (let g' = makeBlack x g in
                    ~(is_gray x g') /\
                    (forall (y: obj_addr). {:pattern (is_gray y g')}
                       y <> x ==> (is_gray y g' <==> is_gray y g))))
  = makeBlack_eq x g;
    makeBlack_is_black x g;
    Mark.colors_exclusive x (makeBlack x g);
    let aux (y: obj_addr) : Lemma (y <> x ==> (is_gray y (makeBlack x g) <==> is_gray y g)) =
      if y <> x then cc_colours x y g Header.Black
    in
    FStar.Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// The cache across a darker heap
/// ---------------------------------------------------------------------------

let entries_ok (g: heap) (st: seq obj_addr) : prop =
  forall (y: obj_addr). {:pattern (Seq.mem y st)} Seq.mem y st ==> entry_ok g y

let entries_darker (g g': heap) (st: seq obj_addr)
  : Lemma (requires S.darker g g' /\ entries_ok g st) (ensures entries_ok g' st)
  = ()

let rescan_darker (g g': heap) (p: mark_pos)
  : Lemma (requires S.darker g g' /\ rescan_ok g p) (ensures rescan_ok g' p)
  = ()

let entries_cons (g: heap) (x: obj_addr) (st: seq obj_addr)
  : Lemma ((entries_ok g (Seq.cons x st) <==> entry_ok g x /\ entries_ok g st) /\
           (forall (y: obj_addr). Seq.mem y (Seq.cons x st) <==> y == x \/ Seq.mem y st))
  = let aux (y: obj_addr) : Lemma (Seq.mem y (Seq.cons x st) <==> y == x \/ Seq.mem y st) =
      Seq.mem_cons x st
    in
    FStar.Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// The partly scanned object
/// ---------------------------------------------------------------------------

/// A pointer field of a block on the walk points at its value.
let field_points_to (g: heap) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\
                    U64.v k <= U64.v (wosize_of_object x g) /\ is_pointer (HG.get_field g x k))
          (ensures points_to g x (HG.get_field g x k))
  = let wz = wosize_of_object x g in
    wosize_of_object_bound x g;
    hd_address_spec x;
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    wf_object_size_bound g x;
    HG.get_field_addr_eq g x k;
    field_read_implies_exists_pointing g x wz (U64.sub k 1UL) (HG.get_field g x k)

/// The target of a pointer field of a scannable block that is not free is on
/// the walk.
let field_target_mem (g: heap) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    ~(is_no_scan x g) /\
                    U64.v k <= U64.v (wosize_of_object x g) /\ is_pointer (HG.get_field g x k))
          (ensures Seq.mem (resolve_object (HG.get_field g x k) g) (objects zero_addr g))
  = field_points_to g x k;
    points_to_target_not_blue g x (HG.get_field g x k)

/// The fields `1 .. k-1` dark and the field `k` dark: `1 .. k` dark.
let fields_dark_snoc (g: heap) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires S.fields_dark g x 1 (U64.v k - 1) /\ S.field_dark g x k)
          (ensures S.fields_dark g x 1 (U64.v k))
  = let aux (j: U64.t{U64.v j >= 1}) : Lemma (1 <= U64.v j /\ U64.v j <= U64.v k ==> S.field_dark g x j) =
      if U64.v j = U64.v k then U64.v_inj j k
    in
    FStar.Classical.forall_intro aux

let slice_scan_field g st ov p cap =
  let x : obj_addr = p.cur in
  let k : (k: U64.t{U64.v k >= 1}) = p.fld in
  let w = HG.get_field g x k in
  let g' = MM.darken g w in
  let st' = pushed g st w cap in
  let ov' = ov || dropped g st w cap in
  wosize_of_object_bound x g;
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  let p' = { p with fld = U64.add p.fld 1UL } in
  Mark.colors_exclusive x g;
  if is_pointer w then field_target_mem g x k;
  assert (S.scan_target g x);
  assert (g' == S.scan_field g x k);
  assert (S.grey_move g g');
  S.mark_move_darker g g';
  S.scan_field_is_grey g x k;
  S.scan_field_dark g x k;
  S.scan_field_weight g x k;
  S.darker_fields_dark g g' x 1 (U64.v k - 1);
  fields_dark_snoc g' x k;
  entries_darker g g' st;
  rescan_darker g g' p;
  if darken_target g w then begin
    let t = resolve_object (w <: obj_addr) g in
    grey_facts t g;
    entries_cons g' t st;
    assert (t <> x);
    assert (is_gray x g');
    assert (cur_ok g' p');
    assert (entries_ok g' st');
    let cov (y: obj_addr) : Lemma (requires grey_obj g' y)
        (ensures Seq.mem y st' \/ y == p'.cur \/ ov' == true \/ (p'.rc <> 0UL /\ U64.v y > U64.v p'.rc)) =
      if y <> t then assert (grey_obj g y)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires cov);
    assert (covered g' st' ov' p')
  end else begin
    assert (g' == g);
    assert (st' == st);
    assert (ov' == ov);
    assert (cur_ok g' p');
    assert (covered g st ov p')
  end

/// Blackening a grey block of the walk whose fields are dark (or that has none
/// to scan): a black move; every other grey block stays grey, so the cache
/// holds with the block dropped from the stack, the partly scanned object or
/// both (`st'` a stack whose grey entries cover those of `st` but `x`).
let blacken_cache (g: heap) (x: obj_addr) (st st': seq obj_addr) (ov: bool) (p p': mark_pos)
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\ is_gray x g /\
                    (is_no_scan x g \/ S.fields_dark g x 1 (U64.v (wosize_of_object x g))) /\
                    entries_ok g st' /\ cur_ok (makeBlack x g) p' /\ rescan_ok g p /\
                    p'.rc == p.rc /\ covered g st ov p /\
                    (forall (y: obj_addr). y <> x /\ grey_obj g y ==>
                       (Seq.mem y st ==> Seq.mem y st') /\ (y == p.cur ==> y == p'.cur)))
          (ensures (let g' = makeBlack x g in
                    marking_cache g' st' ov p' /\
                    S.black_move g g' /\ S.mark_weight g' + 1 == S.mark_weight g))
  = let g' = makeBlack x g in
    assert (S.black_move g g');
    S.mark_move_darker g g';
    S.weight_black g x;
    black_facts x g;
    entries_darker g g' st';
    rescan_darker g g' p;
    let cov (y: obj_addr) : Lemma (requires grey_obj g' y)
        (ensures Seq.mem y st' \/ y == p'.cur \/ ov == true \/ (p'.rc <> 0UL /\ U64.v y > U64.v p'.rc)) =
      assert (grey_obj g y)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires cov)

let slice_blacken_cur g st ov p =
  let x : obj_addr = p.cur in
  blacken_cache g x st st ov p ({ p with cur = 0UL })

let slice_pop_grey g x st ov p =
  entries_cons g x st;
  let p' = { p with cur = x; fld = 1UL } in
  assert (cur_ok g p');
  let cov (y: obj_addr) : Lemma (requires grey_obj g y)
      (ensures Seq.mem y st \/ y == p'.cur \/ ov == true \/ (p'.rc <> 0UL /\ U64.v y > U64.v p'.rc)) =
    ()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires cov)

let slice_pop_blacken g x st ov p =
  entries_cons g x st;
  blacken_cache g x (Seq.cons x st) st ov p p

let slice_pop_skip g x st ov p =
  entries_cons g x st;
  let cov (y: obj_addr) : Lemma (requires grey_obj g y)
      (ensures Seq.mem y st \/ y == p.cur \/ ov == true \/ (p.rc <> 0UL /\ U64.v y > U64.v p.rc)) =
    ()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires cov)

let slice_pop_entry g x st ov p =
  entries_cons g x st

/// ---------------------------------------------------------------------------
/// Rescanning
/// ---------------------------------------------------------------------------

/// Every block of the walk lies after `zero_addr`, which is not 0.
let walk_after_zero (g: heap) (y: obj_addr)
  : Lemma (requires Seq.mem y (objects zero_addr g))
          (ensures U64.v y > U64.v zero_addr /\ zero_addr <> 0UL)
  = objects_addresses_gt_start zero_addr g y;
    zero_addr_above_2048 ()

let slice_rescan_begin g st ov p =
  zero_addr_above_2048 ();
  if p.rc = zero_addr then begin
    objects_nonempty_head zero_addr g;
    let hd = f_address zero_addr in
    U64.v_inj hd (U64.add zero_addr 8UL);
    assert (Seq.mem hd (objects zero_addr g))
  end

let slice_rescan_visit g st ov p h =
  let y : obj_addr = U64.add h 8UL in
  f_address_spec h;
  U64.v_inj (f_address h) y;
  SweepInv.member_implies_objects_nonempty h g;
  objects_nonempty_next h g;
  hd_address_spec y;
  U64.v_inj (hd_address y) h;
  wosize_of_object_spec y g;
  wosize_of_object_bound y g;
  let wz = wosize_of_object y g in
  let next = U64.v h + 8 * (1 + U64.v wz) in
  assert (next <= heap_size /\ next % 8 == 0);
  SweepInv.objects_dense_obj_in h g;
  if next + 8 < heap_size then begin
    SweepInv.obj_in_objects_elim (U64.uint_to_t (next + 8)) g;
    U64.v_inj (U64.add (U64.uint_to_t next) 8UL) (U64.uint_to_t (next + 8))
  end;
  assert (walk_at g (U64.uint_to_t next));
  Mark.colors_exclusive y g;
  let st' = if is_gray y g then Seq.cons y st else st in
  entries_cons g y st;
  let cov (y': obj_addr) : Lemma (requires grey_obj g y')
      (ensures Seq.mem y' st' \/ y' == p.cur \/ ov == true \/ U64.v y' > next) =
    assert (grey_obj g y');
    if U64.v y' > U64.v h && y' <> y then objects_separated zero_addr g y y'
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires cov)

let slice_rescan_stop g st ov p h =
  let y : obj_addr = U64.add h 8UL in
  walk_after_zero g y;
  let cov (y': obj_addr) : Lemma (requires grey_obj g y')
      (ensures Seq.mem y' st \/ y' == p.cur \/ ov == true \/ (h <> 0UL /\ U64.v y' > U64.v h)) =
    assert (grey_obj g y')
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires cov)

let slice_rescan_end g st ov p h =
  let cov (y': obj_addr) : Lemma (requires grey_obj g y')
      (ensures Seq.mem y' st \/ y' == p.cur \/ ov == true) =
    assert (grey_obj g y')
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires cov)

let slice_rescan_start g ov p =
  zero_addr_above_2048 ();
  let p' = { p with rc = zero_addr } in
  let cov (y: obj_addr) : Lemma (requires grey_obj g y)
      (ensures p'.rc <> 0UL /\ U64.v y > U64.v p'.rc) =
    walk_after_zero g y
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires cov)

/// ---------------------------------------------------------------------------
/// Termination
/// ---------------------------------------------------------------------------

/// One step of a lexicographic encoding: `a` then `b < bb`.
[@@"opaque_to_smt"]
let enc (a b: nat) (bb: pos) : nat = a * bb + b

let enc_lt (a a' b b': nat) (bb: pos)
  : Lemma (requires b < bb /\ b' < bb /\ (a' < a \/ (a' == a /\ b' < b)))
          (ensures enc a' b' bb < enc a b bb)
  = reveal_opaque (`%enc) enc;
    if a' < a then FStar.Math.Lemmas.lemma_mult_le_right bb (a' + 1) a

let fields_left_bound (g: heap) (p: mark_pos)
  : Lemma (fields_left g p <= pow2 54)
  = if p.cur <> 0UL && is_val_addr p.cur then wosize_of_object_bound (p.cur <: obj_addr) g

let ov_nat (ov: bool) : nat = if ov then 1 else 0

let slice_measure g st ov p cap =
  enc (enc (enc (enc (S.mark_weight g) (ov_nat ov) 2)
                (rescan_left p) (heap_size + 2))
           (stack_left st p) (2 * cap + 2))
      (fields_left g p) (pow2 54 + 2)

let slice_measure_lt g st ov p g' st' ov' p' cap =
  let w = S.mark_weight g in
  let w' = S.mark_weight g' in
  fields_left_bound g p;
  fields_left_bound g' p';
  let m1 = enc w (ov_nat ov) 2 in
  let m1' = enc w' (ov_nat ov') 2 in
  FStar.Classical.move_requires (enc_lt w w' (ov_nat ov) (ov_nat ov')) 2;
  let m2 = enc m1 (rescan_left p) (heap_size + 2) in
  let m2' = enc m1' (rescan_left p') (heap_size + 2) in
  FStar.Classical.move_requires (enc_lt m1 m1' (rescan_left p) (rescan_left p')) (heap_size + 2);
  let m3 = enc m2 (stack_left st p) (2 * cap + 2) in
  let m3' = enc m2' (stack_left st' p') (2 * cap + 2) in
  FStar.Classical.move_requires (enc_lt m2 m2' (stack_left st p) (stack_left st' p')) (2 * cap + 2);
  FStar.Classical.move_requires (enc_lt m3 m3' (fields_left g p) (fields_left g' p')) (pow2 54 + 2)

/// ---------------------------------------------------------------------------
/// Root darkening
/// ---------------------------------------------------------------------------

let check_and_darken_heap (g: heap) (st st': seq obj_addr) (v: U64.t) (cap cap': nat)
  : Lemma (fst (MB.check_and_darken_bounded_spec g st v cap) ==
           fst (MB.check_and_darken_bounded_spec g st' v cap'))
  = ()

#push-options "--fuel 1"
let rec darken_roots_prefix_heap (g: heap) (st st': seq obj_addr) (rs: seq U64.t)
    (idx: nat{idx <= Seq.length rs}) (cap cap': nat)
  : Lemma (ensures fst (MB.darken_roots_bounded_prefix_spec g st rs idx cap) ==
                   fst (MB.darken_roots_bounded_prefix_spec g st' rs idx cap'))
          (decreases idx)
  = if idx > 0 then begin
      darken_roots_prefix_heap g st st' rs (idx - 1) cap cap';
      let (g0, st0) = MB.darken_roots_bounded_prefix_spec g st rs (idx - 1) cap in
      let (g0', st0') = MB.darken_roots_bounded_prefix_spec g st' rs (idx - 1) cap' in
      check_and_darken_heap g0 st0 st0' (Seq.index rs (idx - 1)) cap cap'
    end
#pop-options

let darken_roots_heap g st st' rs cap cap' =
  darken_roots_prefix_heap g st st' rs (Seq.length rs) cap cap'

/// What root darkening keeps, from a heap with nothing grey: the walk, the
/// entries grey or black, and, while the stack is not full, every grey block
/// on it.
let start_inv (g gi: heap) (sti: seq obj_addr) (cap: nat) : prop =
  Seq.length sti <= cap /\
  objects zero_addr gi == objects zero_addr g /\
  entries_ok gi sti /\
  (Seq.length sti < cap ==> (forall (y: obj_addr). {:pattern (grey_obj gi y)} grey_obj gi y ==> Seq.mem y sti))

let start_step (g gi: heap) (sti: seq obj_addr) (r: U64.t) (cap: nat)
  : Lemma (requires start_inv g gi sti cap /\
                    (is_pointer r ==> Seq.mem (resolve_object (r <: obj_addr) gi) (objects zero_addr gi)))
          (ensures (let res = MB.check_and_darken_bounded_spec gi sti r cap in
                    start_inv g (fst res) (snd res) cap))
  = darken_spec_eq gi sti r cap;
    if darken_target gi r then begin
      let t = resolve_object (r <: obj_addr) gi in
      let gi' = makeGray t gi in
      let sti' = pushed gi sti r cap in
      grey_facts t gi;
      entries_cons gi' t sti;
      let ent (y: obj_addr) : Lemma (requires Seq.mem y sti') (ensures entry_ok gi' y) =
        if Seq.length sti < cap then entries_cons gi' t sti;
        if y <> t then assert (entry_ok gi y)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires ent);
      let cov (y: obj_addr) : Lemma (requires Seq.length sti' < cap /\ grey_obj gi' y)
          (ensures Seq.mem y sti') =
        if y <> t then assert (grey_obj gi y)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires cov)
    end

let root_target (g gi: heap) (st: seq obj_addr) (rs: seq U64.t)
    (idx: nat{idx <= Seq.length rs}) (cap: nat) (r: U64.t)
  : Lemma (requires gi == fst (MB.darken_roots_bounded_prefix_spec g st rs idx cap) /\
                    MBP.root_valid_for_darkening g r)
          (ensures is_pointer r ==> Seq.mem (resolve_object (r <: obj_addr) gi) (objects zero_addr gi))
  = MB.darken_roots_bounded_prefix_preserves_resolve g st rs idx cap (r <: obj_addr);
    MB.darken_roots_bounded_prefix_preserves_objects g st rs idx cap

#push-options "--fuel 1"
let rec start_prefix (g: heap) (rs: seq U64.t) (idx: nat{idx <= Seq.length rs}) (cap: nat)
  : Lemma (requires SweepInv.no_gray_objects g /\
                    (forall (i: nat). i < Seq.length rs ==>
                       MBP.root_valid_for_darkening g (Seq.index rs i)))
          (ensures (let res = MB.darken_roots_bounded_prefix_spec g Seq.empty rs idx cap in
                    start_inv g (fst res) (snd res) cap))
          (decreases idx)
  = if idx = 0 then begin
      let cov (y: obj_addr) : Lemma (requires grey_obj g y) (ensures False) =
        SweepInv.no_gray_elim y g
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires cov)
    end else begin
      start_prefix g rs (idx - 1) cap;
      let (g0, st0) = MB.darken_roots_bounded_prefix_spec g Seq.empty rs (idx - 1) cap in
      let r = Seq.index rs (idx - 1) in
      root_target g g0 Seq.empty rs (idx - 1) cap r;
      start_step g g0 st0 r cap
    end
#pop-options

let mark_cache_start g rs cap =
  start_prefix g rs (Seq.length rs) cap;
  let (g', st') = MB.darken_roots_bounded_spec g Seq.empty rs cap in
  let cov (y: obj_addr) : Lemma (requires grey_obj g' y)
      (ensures Seq.mem y st' \/ Seq.length st' = cap) =
    ()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires cov)
