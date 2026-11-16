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
/// Bodies
/// ---------------------------------------------------------------------------

let bodies_disjoint g x y a =
  if x <> y then begin
    SPM.other_body g x y a;
    SPM.in_body_block g y a
  end

/// ---------------------------------------------------------------------------
/// A change that keeps every block that is not free, with its header
/// ---------------------------------------------------------------------------

/// The cache survives a change that keeps every block that is not free with
/// its header and makes no new grey object.
let cache_kept (g g': heap) (st: seq obj_addr) (ov: bool) (p: mark_pos)
  : Lemma (requires marking_cache g st ov p /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\ ~(is_blue y g) ==>
                       Seq.mem y (objects zero_addr g') /\
                       read_word g' (hd_address y) == read_word g (hd_address y)) /\
                    (forall (y: obj_addr). grey_obj g' y ==> grey_obj g y))
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
    cache_kept g g' st ov p
  | _ ->
    mark_cache_not_marking g ph st ov p;
    mark_cache_not_marking g' ph st ov p

/// ---------------------------------------------------------------------------
/// The barrier's write
/// ---------------------------------------------------------------------------

let mark_cache_barrier_write g st ov p x a v =
  let g' = write_word g a v in
  mark_cache_marking g st ov p;
  mark_cache_marking g' st ov p;
  write_keeps g x a v;
  cache_kept g g' st ov p

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
  cache_kept g g' st ov p

/// ---------------------------------------------------------------------------
/// A change that keeps every non-free block
/// ---------------------------------------------------------------------------

let mark_cache_keeps_blocks g g' st ov p =
  mark_cache_marking g st ov p;
  mark_cache_marking g' st ov p;
  free_stw_ok ();
  free_def_ok_elim free_stw;
  cache_kept g g' st ov p
