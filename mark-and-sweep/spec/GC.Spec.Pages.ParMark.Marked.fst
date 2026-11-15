/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.ParMark.Marked - the heap the parallel mark's bitmap stands for
/// ---------------------------------------------------------------------------
///
/// When the bitmap's bits are exactly the headers of the objects reachable
/// from the roots (`Reach.marks_reach`), the heap the sweep is given,
/// `Bitmap.with_marks h bs`, is `h` with those objects painted black
/// (`wm_paint`), and it meets what `GcCorrect.gc_correct_gen` asks of a mark:
/// **`bitmap_marked`**: `GP.marked h (with_marks h bs) roots` and
/// `MP.mark_inv (with_marks h bs) st`.
///
/// The colour facts follow from painting one object at a time
/// (`paint_facts`, with the single-recolour lemmas of `GC.Spec.Mark`,
/// `GC.Spec.Fields` and `MarkPhase.mark_inv_recolour`); the tri-colour
/// invariant from the closure: a black object is reachable, so the targets
/// of its fields are, so they are black.

module GC.Spec.Pages.ParMark.Marked

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Blocks
open GC.Spec.Pages.Recolour
open GC.Spec.Pages.Bitmap
open GC.Spec.Pages.ParMark.Model
open GC.Spec.Pages.ParMark.Reach
open GC.Spec.Pages.ParMark.Heap

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module L = FStar.List.Tot
module HG = GC.Spec.HeapGraph
module HM = GC.Spec.HeapModel
module G = GC.Spec.Graph
module DFS = GC.Spec.DFS
module R = GC.Spec.Pages.Replace
module HE = GC.Gen.HeapExtensional
module PA = GC.Spec.Pages.Allocator
module I = GC.Spec.AllocIface
module MP = GC.Spec.Pages.MarkPhase
module GP = GC.Spec.Pages.GcPillars
module Mark = GC.Spec.Mark
module Corr = GC.Spec.Correctness
module CF = GC.Spec.Pages.ColourFacts

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The marked objects, as a list
/// ---------------------------------------------------------------------------

let olist (h: heap) : GTot (list obj_addr) = Seq.seq_to_list (objects zero_addr h)

let is_marked (bs: Seq.seq FStar.UInt32.t) (x: obj_addr) : bool = marked bs (U64.v x - 8)

/// The objects whose header's bit is set.
let mlist (h: heap) (bs: Seq.seq FStar.UInt32.t) : GTot (list obj_addr) = L.filter (is_marked bs) (olist h)

let mlist_mem (h: heap) (bs: Seq.seq FStar.UInt32.t) (x: obj_addr)
  : Lemma (L.mem x (mlist h bs) <==> Seq.mem x (objects zero_addr h) /\ marked bs (U64.v x - 8))
  = L.mem_filter (is_marked bs) (olist h) x;
    seq_list_mem (objects zero_addr h) x

/// The setting: the bits are the reachable objects' headers.
[@@"opaque_to_smt"]
let setting (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq FStar.UInt32.t) : prop =
  par_pre h st roots /\ hp_of h p /\ Seq.length bs == bm_len /\ marks_reach p (root_tgts h roots) bs

let setting_elim (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq FStar.UInt32.t)
  : Lemma (requires setting h st roots p bs)
          (ensures par_pre h st roots /\ hp_of h p /\ Seq.length bs == bm_len)
  = reveal_opaque (`%setting) setting

let setting_intro (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq FStar.UInt32.t)
  : Lemma (requires par_pre h st roots /\ hp_of h p /\ Seq.length bs == bm_len /\
                    marks_reach p (root_tgts h roots) bs)
          (ensures setting h st roots p bs)
  = reveal_opaque (`%setting) setting

/// A bit is the header of a reachable, claimable object.
let marked_reach (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq FStar.UInt32.t) (a: nat)
  : Lemma (requires setting h st roots p bs /\ marked bs a)
          (ensures a + 8 >= 8 /\ reach p (root_tgts h roots) (a + 8) /\ hok h (a + 8))
  = reveal_opaque (`%setting) setting;
    view_ok_heap h st roots p;
    eliminate exists (y: nat). reach p (root_tgts h roots) y /\ a == y - 8
    with reach_ok p (hview h) (root_tgts h roots) y

/// An object is marked exactly when it is reachable.
let obj_marked_iff (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq FStar.UInt32.t)
  (x: obj_addr)
  : Lemma (requires setting h st roots p bs)
          (ensures marked bs (U64.v x - 8) <==> reach p (root_tgts h roots) (U64.v x))
  = reveal_opaque (`%setting) setting;
    if marked bs (U64.v x - 8) then marked_reach h st roots p bs (U64.v x - 8)

/// ---------------------------------------------------------------------------
/// The heap the bitmap stands for is a painting
/// ---------------------------------------------------------------------------

let wm_paint_core (h: heap) (bs: Seq.seq FStar.UInt32.t) (xs: list obj_addr)
  : Lemma (requires (forall (x: obj_addr). L.mem x xs ==> marked bs (hx x)) /\
                    (forall (b: nat). marked bs b ==> ~(avoid xs b)))
          (ensures with_marks h bs == paint h xs Black)
  = let l = with_marks h bs in
    let r = paint h xs Black in
    let aux (b: nat) : Lemma (b < heap_size /\ b % 8 == 0 ==>
                              read_word l (U64.uint_to_t b) == read_word r (U64.uint_to_t b))
      = if b < heap_size && b % 8 = 0 then begin
          let ba : hp_addr = U64.uint_to_t b in
          wm_read h (marked bs) ba;
          paint_read h xs Black ba
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext l r

let mlist_marked (h: heap) (bs: Seq.seq FStar.UInt32.t) (x: obj_addr)
  : Lemma (L.mem x (mlist h bs) ==> marked bs (hx x))
  = mlist_mem h bs x

let marked_listed (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq FStar.UInt32.t) (b: nat)
  : Lemma (requires setting h st roots p bs)
          (ensures marked bs b ==> ~(avoid (mlist h bs) b))
  = if marked bs b then begin
      marked_reach h st roots p bs b;
      let yo = as_obj h (b + 8) in
      mlist_mem h bs yo
    end

let wm_paint (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq FStar.UInt32.t)
  : Lemma (requires setting h st roots p bs)
          (ensures with_marks h bs == paint h (mlist h bs) Black)
  = FStar.Classical.forall_intro (mlist_marked h bs);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (marked_listed h st roots p bs));
    wm_paint_core h bs (mlist h bs)

let black_step_eq (g: heap) (x: obj_addr)
  : Lemma (wr g (hx x) (colorHeader (hdr g (hx x)) Black) == set_object_color x g Black)
  = hd_address_spec x;
    makeBlack_spec x g;
    makeBlack_eq x g;
    assert (mk_hp_addr (hx x) == hd_address x)

#push-options "--fuel 1"
let paint_cons (g: heap) (x: obj_addr) (xs: list obj_addr)
  : Lemma (paint g (x :: xs) Black == set_object_color x (paint g xs Black) Black)
  = black_step_eq (paint g xs Black) x
#pop-options

/// ---------------------------------------------------------------------------
/// Painting live objects black changes nothing but their colour
/// ---------------------------------------------------------------------------

let same_objs (h g: heap) : prop =
  objects zero_addr g == objects zero_addr h /\ well_formed_heap g /\
  HM.create_graph g == HM.create_graph h

let same_hdrs (h g: heap) : prop =
  forall (y: obj_addr). (is_blue y g <==> is_blue y h) /\ resolve_object y g == resolve_object y h /\
                   is_no_scan y g == is_no_scan y h /\ wosize_of_object y g == wosize_of_object y h

let same_fields (h g: heap) : prop =
  (forall (x: obj_addr) (i: U64.t{U64.v i >= 1}).
     Seq.mem x (objects zero_addr h) /\ U64.v i <= U64.v (wosize_of_object x h) ==>
     HG.get_field g x i == HG.get_field h x i) /\
  (forall (src dst: obj_addr). Seq.mem src (objects zero_addr h) ==> points_to g src dst == points_to h src dst)

let same (h g: heap) (st: pstate) : prop =
  same_objs h g /\ same_hdrs h g /\ same_fields h g /\ MP.mark_inv g st

let no_scan_step (g: heap) (y z: obj_addr)
  : Lemma (is_no_scan z (set_object_color y g Black) == is_no_scan z g)
  = let g1 = set_object_color y g Black in
    is_no_scan_spec z g;
    is_no_scan_spec z g1;
    tag_of_object_spec z g;
    tag_of_object_spec z g1;
    if z = y then color_preserves_tag y g Black
    else begin
      hd_address_injective y z;
      color_change_header_locality y (hd_address z) g Black
    end

let hdrs_step (h g: heap) (y: obj_addr)
  : Lemma (requires same_hdrs h g /\ ~(is_blue y g) /\ Seq.mem y (objects zero_addr g))
          (ensures same_hdrs h (set_object_color y g Black))
  = let g1 = set_object_color y g Black in
    CF.step_facts g y Black;
    let one (z: obj_addr)
      : Lemma ((is_blue z g1 <==> is_blue z h) /\ resolve_object z g1 == resolve_object z h /\
               is_no_scan z g1 == is_no_scan z h /\ wosize_of_object z g1 == wosize_of_object z h)
      = color_change_preserves_resolve y z g Black;
        color_change_preserves_wosize_any y z g Black;
        no_scan_step g y z
    in
    FStar.Classical.forall_intro one

#push-options "--z3rlimit 40"
let fields_step (h g: heap) (y: obj_addr)
  : Lemma (requires same_objs h g /\ same_hdrs h g /\ same_fields h g /\ Seq.mem y (objects zero_addr g))
          (ensures same_fields h (set_object_color y g Black))
  = let g1 = set_object_color y g Black in
    let f1 (x: obj_addr) (i: U64.t{U64.v i >= 1})
      : Lemma (Seq.mem x (objects zero_addr h) /\ U64.v i <= U64.v (wosize_of_object x h) ==>
               HG.get_field g1 x i == HG.get_field h x i)
      = if Seq.mem x (objects zero_addr h) && U64.v i <= U64.v (wosize_of_object x h) then
          Mark.color_preserves_get_field y x g Black i
    in
    let f2 (src dst: obj_addr)
      : Lemma (Seq.mem src (objects zero_addr h) ==> points_to g1 src dst == points_to h src dst)
      = if Seq.mem src (objects zero_addr h) then begin
          if src = y then color_change_preserves_points_to_self g y Black dst
          else color_change_preserves_points_to_other g y Black src dst
        end
    in
    FStar.Classical.forall_intro_2 f1;
    FStar.Classical.forall_intro_2 f2
#pop-options

let same_step (h g: heap) (st: pstate) (y: obj_addr)
  : Lemma (requires same h g st /\ Seq.mem y (objects zero_addr h) /\ ~(is_blue y h))
          (ensures same h (set_object_color y g Black) st)
  = CF.step_facts g y Black;
    Mark.color_preserves_create_graph y g Black;
    MP.mark_inv_recolour g st y Black;
    hdrs_step h g y;
    fields_step h g y

let same_refl (h: heap) (st: pstate)
  : Lemma (requires PA.inv I.Idle h st) (ensures same h h st)
  = idle_facts h st;
    MP.mark_inv_of_ok h st

/// Live objects, painted black one at a time.
#push-options "--fuel 1"
let rec paint_same (h: heap) (st: pstate) (ys: list obj_addr)
  : Lemma (requires PA.inv I.Idle h st /\
                    (forall (y: obj_addr). L.mem y ys ==> Seq.mem y (objects zero_addr h) /\ ~(is_blue y h)))
          (ensures same h (paint h ys Black) st)
          (decreases ys)
  = match ys with
    | [] -> same_refl h st
    | y :: rest ->
      paint_same h st rest;
      paint_cons h y rest;
      same_step h (paint h rest Black) st y
#pop-options

/// ---------------------------------------------------------------------------
/// Colours
/// ---------------------------------------------------------------------------

/// The painted objects are live.
let painted_live (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq FStar.UInt32.t)
  : Lemma (requires setting h st roots p bs)
          (ensures forall (y: obj_addr). L.mem y (mlist h bs) ==> Seq.mem y (objects zero_addr h) /\ ~(is_blue y h))
  = let one (y: obj_addr) : Lemma (L.mem y (mlist h bs) ==> Seq.mem y (objects zero_addr h) /\ ~(is_blue y h))
      = mlist_mem h bs y;
        if L.mem y (mlist h bs) then begin
          marked_reach h st roots p bs (hx y);
          hw_obj h y
        end
    in
    FStar.Classical.forall_intro one

/// In the `Idle` state every object is white or free.
let idle_colour (h: heap) (st: pstate) (x: obj_addr)
  : Lemma (requires PA.inv I.Idle h st /\ Seq.mem x (objects zero_addr h))
          (ensures is_white x h \/ is_blue x h)
  = idle_facts h st;
    if not (is_blue x h) then begin
      MP.live_white h st x;
      R.hdr_obj h x;
      is_white_iff x h
    end

/// A painted object is black; any other keeps its colour.
let paint_colour (h: heap) (xs: list obj_addr) (x: obj_addr)
  : Lemma ((L.mem x xs ==> is_black x (paint h xs Black)) /\
           (~(L.mem x xs) ==> color_of_object x (paint h xs Black) == color_of_object x h))
  = let g = paint h xs Black in
    R.hdr_obj g x;
    R.hdr_obj h x;
    hx_word x;
    if L.mem x xs then begin
      paint_on h xs Black x;
      colorHeader_getColor (hdr h (hx x)) Black;
      is_black_iff x g
    end else begin
      let one (y: obj_addr) : Lemma (L.mem y xs ==> hx y <> hx x) = () in
      FStar.Classical.forall_intro one;
      paint_off h xs Black (mk_hp_addr (hx x))
    end

/// In the painted heap: black exactly when painted, never grey.
let painted_colours (h: heap) (st: pstate) (xs: list obj_addr) (x: obj_addr)
  : Lemma (requires PA.inv I.Idle h st /\ Seq.mem x (objects zero_addr h))
          (ensures (is_black x (paint h xs Black) <==> L.mem x xs) /\ ~(is_gray x (paint h xs Black)))
  = let g = paint h xs Black in
    paint_colour h xs x;
    idle_colour h st x;
    is_black_iff x g; is_gray_iff x g; is_white_iff x h; is_blue_iff x h;
    is_black_iff x h; is_gray_iff x h

/// ---------------------------------------------------------------------------
/// Density
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let objects_nonempty (h: heap) (st: pstate)
  : Lemma (requires PA.inv I.Idle h st) (ensures Seq.length (objects zero_addr h) > 0)
  = idle_facts h st;
    let z = U64.v zero_addr in
    let xo : obj_addr = U64.uint_to_t (z + 8) in
    R.obj_iff h xo;
    steps_to_refl h z;
    pages_end_bound ();
    if n_pages > 0 then begin
      let e = page_base (span st.pm 0) in
      assert (walk_page st.pm 0);
      if (entry st.pm 0).kind = LargeCont then assert (cont_ok st.pm 0);
      assert (page_shape h st.pm 0);
      page_steps h st.pm 0;
      page_base_mono (span st.pm 0) n_pages;
      steps_to_next h zero_addr e;
      R.block_bytes_words h z
    end else begin
      assert (pages_end == z);
      assert (heap_size - z >= 16);
      assert (blue_block h pages_end ((heap_size - pages_end) / 8))
    end;
    SP.mem_index xo (objects zero_addr h)
#pop-options

let dense (h: heap) (st: pstate) (g: heap)
  : Lemma (requires PA.inv I.Idle h st /\ objects zero_addr g == objects zero_addr h /\
                    (forall (p: hp_addr). getWosize (read_word g p) == getWosize (read_word h p)))
          (ensures heap_objects_dense h /\ heap_objects_dense g /\ Seq.length (objects zero_addr h) > 0)
  = objects_nonempty h st;
    pages_ok_tiled h st;
    GC.Spec.WalkEnd.dense_from_walk_end h;
    GC.Spec.SweepInv.heap_objects_dense_transfer h g

let paint_wosize (h: heap) (xs: list obj_addr) (p: hp_addr)
  : Lemma (getWosize (read_word (paint h xs Black) p) == getWosize (read_word h p))
  = paint_read h xs Black p;
    colorHeader_preserves_wosize (read_word h p) Black

/// ---------------------------------------------------------------------------
/// The tri-colour invariant, from the closure
/// ---------------------------------------------------------------------------

/// A field that points to `t`.
#push-options "--fuel 1 --z3rlimit 40"
let rec efptu_field (g: heap) (x: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (t: obj_addr)
  : Lemma (requires exists_field_pointing_to_unchecked g x wz t)
          (ensures exists (k: nat). k < U64.v wz /\
                     (match word_at g (U64.v x + 8 * k) with Some fv -> is_pointer_to fv t | None -> False))
          (decreases U64.v wz)
  = if wz = 0UL then () else begin
    let idx = U64.sub wz 1UL in
    FStar.Math.Lemmas.pow2_plus 54 3;
    assert_norm (pow2 3 == 8);
    FStar.Math.Lemmas.pow2_lt_compat 64 58;
    FStar.Math.Lemmas.pow2_double_sum 57;
    FStar.Math.Lemmas.modulo_lemma (U64.v idx * 8) (pow2 64);
    FStar.Math.Lemmas.modulo_lemma (U64.v x + U64.v idx * 8) (pow2 64);
    let far = U64.add_mod x (U64.mul_mod idx mword) in
    assert (U64.v far == U64.v x + 8 * U64.v idx);
    if U64.v far < heap_size && U64.v far % 8 = 0 &&
       is_pointer_to (read_word g (far <: hp_addr)) t then
      assert (mk_hp_addr (U64.v x + 8 * U64.v idx) == far)
    else efptu_field g x idx t
    end
#pop-options

/// That field is one the model scans, and its target is the resolved one.
#push-options "--z3rlimit 40"
let field_tgt (h: heap) (p: params) (obj child: obj_addr) (k: nat)
  : Lemma (requires hp_of h p /\ Mark.no_pointer_to_blue h /\ Seq.mem obj (objects zero_addr h) /\
                    ~(is_no_scan obj h) /\ ~(is_blue obj h) /\ k < U64.v (wosize_of_object obj h) /\
                    points_to h obj child /\
                    (match word_at h (U64.v obj + 8 * k) with Some fv -> is_pointer_to fv child | None -> False))
          (ensures field_of p (U64.v obj) (U64.v obj + 8 * k) /\
                   p.tgt (U64.v obj + 8 * k) == Some (U64.v (resolve_object child h)))
  = let a = U64.v obj + 8 * k in
    let Some fv = word_at h a in
    hd_address_spec child;
    hd_address_spec (ptr_obj fv);
    assert (fv == child);
    let rc = resolve_object child h in
    tres_eq h child;
    hw_obj h obj;
    hw_obj h rc;
    FStar.Math.Lemmas.lemma_mod_plus (U64.v obj) k 8
#pop-options

/// The marks are closed under the model's edges.
let marks_closed (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq FStar.UInt32.t)
  (x a y: nat)
  : Lemma (requires setting h st roots p bs /\ x >= 8 /\ marked bs (x - 8) /\ field_of p x a /\ p.tgt a == Some y)
          (ensures hok h y /\ marked bs (y - 8))
  = let rts = root_tgts h roots in
    setting_elim h st roots p bs;
    marked_reach h st roots p bs (x - 8);
    reach_step p rts x a y;
    view_ok_heap h st roots p;
    reach_ok p (hview h) rts y;
    reveal_opaque (`%setting) setting

let tri_one (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq FStar.UInt32.t)
  (obj child: obj_addr)
  : Lemma (requires setting h st roots p bs /\ Seq.mem obj (objects zero_addr h) /\
                    marked bs (hx obj) /\ ~(is_no_scan obj h) /\ ~(is_blue obj h) /\ points_to h obj child)
          (ensures Seq.mem (resolve_object child h) (objects zero_addr h) /\
                   marked bs (hx (resolve_object child h)))
  = setting_elim h st roots p bs;
    idle_facts h st;
    wosize_of_object_bound obj h;
    efptu_field h obj (wosize_of_object obj h) child;
    eliminate exists (k: nat). k < U64.v (wosize_of_object obj h) /\
                     (match word_at h (U64.v obj + 8 * k) with Some fv -> is_pointer_to fv child | None -> False)
    with begin
      field_tgt h p obj child k;
      marks_closed h st roots p bs (U64.v obj) (U64.v obj + 8 * k) (U64.v (resolve_object child h))
    end

let tri_colour (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq FStar.UInt32.t)
  : Lemma (requires setting h st roots p bs)
          (ensures Mark.tri_color_invariant (paint h (mlist h bs) Black))
  = let xs = mlist h bs in
    let g = paint h xs Black in
    setting_elim h st roots p bs;
    painted_live h st roots p bs;
    paint_same h st xs;
    let one (obj child: obj_addr)
      : Lemma (Seq.mem obj (objects zero_addr g) ==> is_black obj g ==> ~(is_no_scan obj g) ==>
               points_to g obj child ==> ~(is_white (resolve_object child g) g))
      = if Seq.mem obj (objects zero_addr g) && is_black obj g && not (is_no_scan obj g) &&
           points_to g obj child then begin
          painted_colours h st xs obj;
          mlist_mem h bs obj;
          Mark.colors_exclusive obj g;
          tri_one h st roots p bs obj child;
          let rc = resolve_object child h in
          mlist_mem h bs rc;
          painted_colours h st xs rc;
          Mark.colors_exclusive rc g
        end
    in
    FStar.Classical.forall_intro_2 one

let npb (h: heap) (st: pstate) (g: heap)
  : Lemma (requires PA.inv I.Idle h st /\ same h g st) (ensures Mark.no_pointer_to_blue g)
  = idle_facts h st;
    let one (src dst: obj_addr)
      : Lemma (Seq.mem src (objects zero_addr g) /\ ~(is_blue src g) /\
               fields_constrained g src /\ points_to g src dst ==>
               ~(is_blue (resolve_object dst g) g))
      = ()
    in
    FStar.Classical.forall_intro_2 one

/// ---------------------------------------------------------------------------
/// What the collection needs of the mark
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let black_iff_reach (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq FStar.UInt32.t)
  (x: obj_addr)
  : Lemma (requires setting h st roots p bs /\ G.mem_graph_vertex (HM.create_graph h) x)
          (ensures (setting_elim h st roots p bs; graph_facts h st roots;
                    is_black x (paint h (mlist h bs) Black) <==>
                    Seq.mem x (DFS.reachable_set (HM.create_graph h) (HG.coerce_to_vertex_list roots))))
  = setting_elim h st roots p bs;
    graph_facts h st roots;
    HM.graph_vertices_mem h x;
    painted_colours h st (mlist h bs) x;
    mlist_mem h bs x;
    obj_marked_iff h st roots p bs x;
    reach_iff h st roots p (U64.v x);
    assert (as_obj h (U64.v x) == x)
#pop-options

let paint_marked (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq FStar.UInt32.t)
  : Lemma (requires setting h st roots p bs)
          (ensures GP.marked h (paint h (mlist h bs) Black) roots /\ MP.mark_inv (paint h (mlist h bs) Black) st)
  = let xs = mlist h bs in
    let g = paint h xs Black in
    setting_elim h st roots p bs;
    idle_facts h st;
    painted_live h st roots p bs;
    paint_same h st xs;
    FStar.Classical.forall_intro (paint_wosize h xs);
    dense h st g;
    npb h st g;
    tri_colour h st roots p bs;
    let grey (x: obj_addr) : Lemma (Seq.mem x (objects zero_addr g) ==> not (is_gray x g))
      = if Seq.mem x (objects zero_addr g) then painted_colours h st xs x
    in
    FStar.Classical.forall_intro grey;
    let noblack (x: obj_addr) : Lemma (Seq.mem x (objects zero_addr h) ==> ~(is_black x h))
      = if Seq.mem x (objects zero_addr h) then begin
          idle_colour h st x;
          Mark.colors_exclusive x h
        end
    in
    FStar.Classical.forall_intro noblack;
    graph_facts h st roots;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (black_iff_reach h st roots p bs));
    Corr.mark_post_intro h g roots 0UL

/// **The heap the bitmap stands for is a correct mark of `h`**: the
/// hypotheses of `GcCorrect.gc_correct_gen`.
let bitmap_marked (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (bs: Seq.seq FStar.UInt32.t)
  : Lemma (requires par_pre h st roots /\ hp_of h p /\ Seq.length bs == bm_len /\
                    marks_reach p (root_tgts h roots) bs)
          (ensures GP.marked h (with_marks h bs) roots /\ MP.mark_inv (with_marks h bs) st /\
                   GP.graph_pre h roots)
  = setting_intro h st roots p bs;
    wm_paint h st roots p bs;
    paint_marked h st roots p bs

/// ---------------------------------------------------------------------------
/// Vacuity
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
[@@expect_failure [19]]
let bitmap_marked_hyps_not_false (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params)
  (bs: Seq.seq FStar.UInt32.t)
  : Lemma (requires par_pre h st roots /\ hp_of h p /\ Seq.length bs == bm_len /\
                    marks_reach p (root_tgts h roots) bs)
          (ensures False)
  = ()
#pop-options
