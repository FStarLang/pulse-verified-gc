module GC.Gen.MarkState

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module GenInv = GC.Gen.HeapInvariant
module GMM = GC.Gen.MarkPhase.Minor
module MM = GC.Spec.MarkPhase.Mutator
module SPM = GC.Spec.SweepPhase.Mutator
module SPI = GC.Spec.SweepPhase.Intrinsic
module Promote = GC.Gen.Promote
module S = GC.Spec.MarkPhase.Slice
module MPA = GC.Spec.MarkPhase.Alloc
module FT = GC.Spec.FieldTarget
module HG = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module Header = GC.Lib.Header

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

let mark_cache_marking g st ov p = reveal_opaque (`%mark_cache_ok) (mark_cache_ok g Ph.Marking st ov p)

let mark_cache_not_marking g ph st ov p = reveal_opaque (`%mark_cache_ok) (mark_cache_ok g ph st ov p)

let mark_cache_empty g ph =
  reveal_opaque (`%mark_cache_ok) (mark_cache_ok g ph Seq.empty false no_pos)

let mark_cache_off g g' ph ph' st ov p =
  mark_cache_not_marking g ph st ov p;
  mark_cache_not_marking g' ph' st ov p

let marking_cache_done g st ov p =
  let aux (y: obj_addr) : Lemma (Seq.mem y (objects zero_addr g) ==> not (is_gray y g))
    = if Seq.mem y (objects zero_addr g) && is_gray y g then begin
        assert (grey_obj g y);
        if Seq.mem y st then FStar.Seq.Properties.mem_index y st
      end
  in
  FStar.Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// Bodies and fields
/// ---------------------------------------------------------------------------

let bodies_disjoint g x y a =
  if x <> y then begin
    SPM.other_body g x y a;
    SPM.in_body_block g y a
  end

/// A word in the body of `x` lies outside the body of every other block.
let outside_body (g: heap) (x y: obj_addr) (a: hp_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\ x <> y /\
                    SPM.in_body g x a)
          (ensures U64.v a < U64.v y \/ U64.v a >= U64.v y + U64.v (wosize_of_object y g) * 8)
  = FStar.Classical.move_requires (bodies_disjoint g x y) a

/// A word in the body of a non-free block is no header.
let body_not_header (g: heap) (y t: obj_addr) (b: hp_addr)
  : Lemma (requires Seq.mem y (objects zero_addr g) /\ ~(is_blue y g) /\ SPM.in_body g y b /\
                    Seq.mem t (objects zero_addr g))
          (ensures hd_address t <> b)
  = SPM.in_body_block g y b;
    SPI.colour_of g y;
    SPI.body_word g (hd_address y) b;
    SPI.obj_pos g t

/// The field `k` of `y` is the word `y + (k - 1) * 8`.
let field_word (g: heap) (y: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires U64.v y + U64.v k * 8 <= heap_size)
          (ensures U64.v y + (U64.v k - 1) * 8 < heap_size /\
                   (U64.v y + (U64.v k - 1) * 8) % 8 == 0 /\
                   HG.get_field g y k == read_word g (U64.uint_to_t (U64.v y + (U64.v k - 1) * 8)))
  = hd_address_spec y

/// A field stays dark when its word, the header at the pointer and the header
/// of its resolved target are unchanged.
let field_dark_kept (g g': heap) (y: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires S.field_dark g y k /\ HG.get_field g' y k == HG.get_field g y k /\
                    (is_pointer (HG.get_field g y k) ==>
                      (let w : obj_addr = HG.get_field g y k in
                       read_word g' (hd_address w) == read_word g (hd_address w) /\
                       read_word g' (hd_address (resolve_object w g)) ==
                         read_word g (hd_address (resolve_object w g)))))
          (ensures S.field_dark g' y k)
  = if is_pointer (HG.get_field g y k) then begin
      let w : obj_addr = HG.get_field g y k in
      resolve_object_locality w g g';
      MM.header_kept_facts g g' (resolve_object w g)
    end

/// ---------------------------------------------------------------------------
/// A write into a body keeps the dark fields of the other words
/// ---------------------------------------------------------------------------

/// The field `k` of a non-free scannable block `y`, if it is not the word
/// written, stays dark: the write touches no header of a block, and not the
/// infix header a field may point at (it lies in the body of a closure that
/// is not free, and `x` is not one).
let field_dark_write (free: free_def) (g: heap) (y x: obj_addr) (a: hp_addr) (v: U64.t)
  (k: U64.t{U64.v k >= 1})
  : Lemma (requires free_def_ok free /\ well_formed_heap_with free g /\ in_use free g y /\
                    ~(is_no_scan y g) /\ U64.v k <= U64.v (wosize_of_object y g) /\
                    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ SPM.in_body g x a /\
                    ~(in_use free g x /\ is_closure x g) /\
                    U64.v a <> U64.v y + (U64.v k - 1) * 8 /\
                    S.field_dark g y k)
          (ensures S.field_dark (write_word g a v) y k)
  = let g' = write_word g a v in
    wf_with_parts ();
    free_def_ok_elim free;
    hd_address_spec y;
    let j : nat = U64.v k - 1 in
    field_word g y k;
    field_word g' y k;
    let fa : hp_addr = U64.uint_to_t (U64.v y + j * 8) in
    read_write_different g a fa v;
    if is_pointer (HG.get_field g y k) then begin
      let w : obj_addr = HG.get_field g y k in
      FT.wf_with_field free g y j;
      let r = resolve_object w g in
      body_not_header g x r a;
      read_write_different g a (hd_address r) v;
      if is_infix w g then begin
        infix_addr_wf_elim g (objects zero_addr g) w;
        parent_closure_addr_nat_spec w g;
        resolve_infix_spec w g;
        hd_address_spec w;
        SPM.other_body g x r a;
        SPM.in_body_block g r (hd_address w);
        read_write_different g a (hd_address w) v
      end else
        resolve_non_infix w g
    end;
    field_dark_kept g g' y k

let fields_dark_write (free: free_def) (g: heap) (y x: obj_addr) (a: hp_addr) (v: U64.t) (n: nat)
  : Lemma (requires free_def_ok free /\ well_formed_heap_with free g /\ in_use free g y /\
                    ~(is_no_scan y g) /\ n <= U64.v (wosize_of_object y g) /\
                    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ SPM.in_body g x a /\
                    ~(in_use free g x /\ is_closure x g) /\
                    (U64.v a < U64.v y \/ U64.v a >= U64.v y + n * 8) /\
                    S.fields_dark g y 1 n)
          (ensures S.fields_dark (write_word g a v) y 1 n)
  = let aux (k: U64.t{U64.v k >= 1})
      : Lemma (1 <= U64.v k /\ U64.v k <= n ==> S.field_dark (write_word g a v) y k)
      = if U64.v k <= n then field_dark_write free g y x a v k
    in
    FStar.Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// A change that keeps every block that is not free, with its header
/// ---------------------------------------------------------------------------

/// The cache survives a change that keeps every block that is not free with
/// its header, makes no new grey object, and keeps the partly scanned
/// object's scanned fields dark.
let cache_kept (g g': heap) (st: seq obj_addr) (ov: bool) (p: mark_pos)
  : Lemma (requires marking_cache g st ov p /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\ ~(is_blue y g) ==>
                       Seq.mem y (objects zero_addr g') /\
                       read_word g' (hd_address y) == read_word g (hd_address y)) /\
                    (forall (y: obj_addr). grey_obj g' y ==> grey_obj g y) /\
                    (p.cur <> 0UL ==> is_val_addr p.cur /\
                                      S.fields_dark g' (p.cur <: obj_addr) 1 (U64.v p.fld - 1)))
          (ensures marking_cache g' st ov p)
  = let keep (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g) /\ ~(is_blue y g))
              (ensures Seq.mem y (objects zero_addr g') /\
                       (is_white y g' <==> is_white y g) /\ (is_gray y g' <==> is_gray y g) /\
                       (is_blue y g' <==> is_blue y g) /\ is_no_scan y g' == is_no_scan y g /\
                       wosize_of_object y g' == wosize_of_object y g)
      = MM.header_kept_facts g g' y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires keep);
    if p.cur <> 0UL then begin
      let c : obj_addr = p.cur in
      Mark.colors_exclusive c g;
      keep c
    end

/// A write into the body of a block that is not free keeps every header and
/// the grey objects.
let write_keeps (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ SPM.in_body g x a)
          (ensures (forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\ ~(is_blue y g) ==>
                      Seq.mem y (objects zero_addr (write_word g a v)) /\
                      read_word (write_word g a v) (hd_address y) == read_word g (hd_address y)) /\
                   (forall (y: obj_addr). grey_obj (write_word g a v) y ==> grey_obj g y))
  = MM.write_heads g x a v

/// ---------------------------------------------------------------------------
/// Initialising a block just allocated
/// ---------------------------------------------------------------------------

let mark_cache_write g ph st ov p x a v =
  let g' = write_word g a v in
  match ph with
  | Ph.Marking ->
    mark_cache_marking g st ov p;
    mark_cache_marking g' st ov p;
    write_keeps g x a v;
    if p.cur <> 0UL then begin
      let c : obj_addr = p.cur in
      MPA.free_or_new_ok x;
      Mark.colors_exclusive x g;
      Mark.colors_exclusive c g;
      outside_body g x c a;
      fields_dark_write (MPA.free_or_new x) g c x a v (U64.v p.fld - 1)
    end;
    cache_kept g g' st ov p
  | _ ->
    mark_cache_not_marking g ph st ov p;
    mark_cache_not_marking g' ph st ov p

/// ---------------------------------------------------------------------------
/// The barrier's write
/// ---------------------------------------------------------------------------

let mark_cache_barrier_write g st ov p x a v =
  let g' = write_word g a v in
  let p' = reset_cur p a in
  mark_cache_marking g st ov p;
  mark_cache_marking g' st ov p';
  write_keeps g x a v;
  if p.cur <> 0UL then begin
    let c : obj_addr = p.cur in
    if not (in_scanned p a) then begin
      free_stw_ok ();
      Mark.colors_exclusive c g;
      if x <> c then outside_body g x c a;
      fields_dark_write free_stw g c x a v (U64.v p.fld - 1)
    end
  end;
  assert (marking_cache g st ov p');
  cache_kept g g' st ov p'

/// ---------------------------------------------------------------------------
/// Darkening
/// ---------------------------------------------------------------------------

/// Greying `t` keeps the header of every other block.
let grey_other (g: heap) (t y: obj_addr)
  : Lemma (requires y <> t)
          (ensures read_word (makeGray t g) (hd_address y) == read_word g (hd_address y))
  = makeGray_eq t g;
    hd_address_injective t y;
    color_change_preserves_other_read t (hd_address y) g Header.Gray

/// Greying the white block `t` greys `t` and nothing else.
let grey_greys (g: heap) (t: obj_addr)
  : Lemma (requires Seq.mem t (objects zero_addr g) /\ is_white t g)
          (ensures (forall (y: obj_addr). grey_obj (makeGray t g) y <==> (y == t \/ grey_obj g y)) /\
                   ~(grey_obj g t))
  = let g1 = makeGray t g in
    makeGray_eq t g;
    makeGray_is_gray t g;
    color_change_preserves_objects g t Header.Gray;
    Mark.colors_exclusive t g;
    let col (y: obj_addr)
      : Lemma (y <> t ==> (is_gray y g1 <==> is_gray y g))
      = if y <> t then begin
          color_change_preserves_other_color t y g Header.Gray;
          is_gray_iff y g; is_gray_iff y g1
        end
    in
    FStar.Classical.forall_intro col

/// A dark field of a block that is not free stays dark when a white block is
/// greyed.
let field_dark_grey (g: heap) (t y: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires blocks_fit g /\ Seq.mem t (objects zero_addr g) /\ is_white t g /\
                    Seq.mem y (objects zero_addr g) /\ ~(is_blue y g) /\
                    U64.v k <= U64.v (wosize_of_object y g) /\ S.field_dark g y k)
          (ensures S.field_dark (makeGray t g) y k)
  = let g1 = makeGray t g in
    makeGray_eq t g;
    hd_address_spec y;
    field_word g y k;
    field_word g1 y k;
    let fa : hp_addr = U64.uint_to_t (U64.v y + (U64.v k - 1) * 8) in
    body_not_header g y t fa;
    color_change_preserves_other_read t fa g Header.Gray;
    if is_pointer (HG.get_field g y k) then begin
      let w : obj_addr = HG.get_field g y k in
      color_change_preserves_resolve t w g Header.Gray;
      let r = resolve_object w g in
      if r <> t then begin
        grey_other g t r;
        MM.header_kept_facts g g1 r
      end
    end

let fields_dark_grey (g: heap) (t y: obj_addr) (n: nat)
  : Lemma (requires blocks_fit g /\ Seq.mem t (objects zero_addr g) /\ is_white t g /\
                    Seq.mem y (objects zero_addr g) /\ ~(is_blue y g) /\
                    n <= U64.v (wosize_of_object y g) /\ S.fields_dark g y 1 n)
          (ensures S.fields_dark (makeGray t g) y 1 n)
  = let aux (k: U64.t{U64.v k >= 1})
      : Lemma (1 <= U64.v k /\ U64.v k <= n ==> S.field_dark (makeGray t g) y k)
      = if U64.v k <= n then field_dark_grey g t y k
    in
    FStar.Classical.forall_intro aux

let mark_cache_darken g st ov p w cap =
  mark_cache_marking g st ov p;
  let ov' = ov || Seq.length st = cap in
  if darken_target g w then begin
    let t = resolve_object (w <: obj_addr) g in
    let st' = if Seq.length st < cap then Seq.cons t st else st in
    let g1 = makeGray t g in
    grey_greys g t;
    makeGray_is_gray t g;
    makeGray_eq t g;
    color_change_preserves_objects g t Header.Gray;
    Mark.colors_exclusive t g1;
    let mem_cons (y: obj_addr)
      : Lemma (Seq.mem y st' <==> ((Seq.length st < cap /\ y == t) \/ Seq.mem y st))
      = if Seq.length st < cap then Seq.mem_cons t st
    in
    FStar.Classical.forall_intro mem_cons;
    let kept (y: obj_addr)
      : Lemma (y <> t ==>
               ((is_white y g1 <==> is_white y g) /\ (is_gray y g1 <==> is_gray y g) /\
                (is_blue y g1 <==> is_blue y g) /\ is_no_scan y g1 == is_no_scan y g /\
                wosize_of_object y g1 == wosize_of_object y g))
      = if y <> t then begin
          grey_other g t y;
          MM.header_kept_facts g g1 y
        end
    in
    FStar.Classical.forall_intro kept;
    if p.cur <> 0UL then begin
      let c : obj_addr = p.cur in
      wf_parts ();
      Mark.colors_exclusive c g;
      fields_dark_grey g t c (U64.v p.fld - 1)
    end;
    assert (MM.darken g w == g1);
    mark_cache_marking g1 st' ov' p
  end else begin
    assert (MM.darken g w == g);
    mark_cache_marking g st ov' p
  end

/// ---------------------------------------------------------------------------
/// A minor collection
/// ---------------------------------------------------------------------------

let mark_cache_minor minor g fp roots st ov p =
  let g' = (GMM.collect_marking minor g fp roots).Promote.mc_major in
  mark_cache_marking g st ov p;
  mark_cache_marking g' st ov p;
  let greys (y: obj_addr) : Lemma (grey_obj g' y ==> grey_obj g y)
    = GMM.minor_keeps_greys minor g fp roots y
  in
  FStar.Classical.forall_intro greys;
  let keep (y: obj_addr)
    : Lemma (requires Seq.mem y (objects zero_addr g) /\ ~(is_blue y g))
            (ensures Seq.mem y (objects zero_addr g') /\
                     read_word g' (hd_address y) == read_word g (hd_address y))
    = GMM.minor_keeps_block minor g fp roots y
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires keep);
  if p.cur <> 0UL then begin
    let c : obj_addr = p.cur in
    Mark.colors_exclusive c g;
    let n = U64.v p.fld - 1 in
    let aux (k: U64.t{U64.v k >= 1})
      : Lemma (1 <= U64.v k /\ U64.v k <= n ==> S.field_dark g' c k)
      = if U64.v k <= n then GMM.minor_keeps_field_dark minor g fp roots c k
    in
    FStar.Classical.forall_intro aux
  end;
  cache_kept g g' st ov p
