module GC.Spec.MarkPhase.Stw

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module Mark = GC.Spec.Mark
module MB = GC.Spec.MarkBounded
module MBC = GC.Spec.MarkBoundedCorrectness
module Corr = GC.Spec.Correctness
module HM = GC.Spec.HeapModel
module HG = GC.Spec.HeapGraph
module G = GC.Spec.Graph
module DFS = GC.Spec.DFS
module MP = GC.Spec.MarkPhase
module SweepInv = GC.Spec.SweepInv
module S = GC.Spec.MarkPhase.Slice

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// Start
/// ---------------------------------------------------------------------------

let marking_inv_stw_start g0 roots =
  MBC.mark_color_inv_init g0;
  MBC.gray_black_reachable_init g0 roots;
  MBC.gray_stays_init g0

/// ---------------------------------------------------------------------------
/// Blackening: the stop-the-world step on a one-element stack
/// ---------------------------------------------------------------------------

#push-options "--fuel 2"
let singleton_bsp (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ is_gray x g)
          (ensures (let st = Seq.cons x Seq.empty in
                    MB.bounded_stack_props g st /\ Seq.length st > 0 /\ Seq.head st == x /\
                    (forall (y: obj_addr). Seq.mem y st ==> y == x)))
  = let st : seq obj_addr = Seq.cons x Seq.empty in
    Seq.mem_cons x (Seq.empty #obj_addr);
    Seq.lemma_tl x (Seq.empty #obj_addr);
    assert (Seq.equal (Seq.tail st) Seq.empty);
    assert (Mark.stack_elements_valid g st);
    assert (Mark.stack_no_dups st)
#pop-options

let black_step (g0 g: heap) (roots: seq obj_addr) (x: obj_addr)
  : Lemma (requires marking_inv_stw g0 g roots /\ Seq.mem x (objects zero_addr g) /\ is_gray x g /\
                    (is_no_scan x g \/ S.fields_dark g x 1 (U64.v (wosize_of_object x g))))
          (ensures marking_inv_stw g0 (makeBlack x g) roots)
  = let st : seq obj_addr = Seq.cons x Seq.empty in
    singleton_bsp g x;
    S.black_move_is_step g x;
    MB.mark_step_bounded_heap_eq g st st 0;
    MP.mark_step_heap g st;
    assert (fst (MB.mark_step_bounded g st 0) == makeBlack x g);
    MBC.mark_step_bounded_preserves_color_inv g0 g st 0;
    MBC.mark_step_bounded_preserves_gbr g0 g st 0 roots;
    MBC.mark_step_bounded_preserves_gray_stays g0 g st 0

/// ---------------------------------------------------------------------------
/// Greying a white block
/// ---------------------------------------------------------------------------

/// The colour facts of greying the white block `t`.
let grey_colours (g: heap) (t: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem t (objects zero_addr g) /\ is_white t g)
          (ensures (let g' = makeGray t g in
                    g' == set_object_color t g Header.Gray /\
                    well_formed_heap g' /\ objects zero_addr g' == objects zero_addr g /\
                    is_gray t g' /\ ~(is_white t g') /\ ~(is_black t g') /\ ~(is_blue t g') /\
                    ~(is_black t g) /\ ~(is_blue t g) /\ ~(is_gray t g) /\
                    (forall (y: obj_addr). y <> t ==>
                       ((is_black y g' <==> is_black y g) /\ (is_white y g' <==> is_white y g) /\
                        (is_gray y g' <==> is_gray y g) /\ (is_blue y g' <==> is_blue y g)))))
  = let g' = makeGray t g in
    makeGray_eq t g;
    makeGray_is_gray t g;
    Mark.colors_exclusive t g;
    Mark.colors_exclusive t g';
    Mark.color_change_preserves_wf g t Header.Gray;
    color_change_preserves_objects g t Header.Gray;
    let col (y: obj_addr)
      : Lemma (y <> t ==> ((is_black y g' <==> is_black y g) /\ (is_white y g' <==> is_white y g) /\
                           (is_gray y g' <==> is_gray y g) /\ (is_blue y g' <==> is_blue y g)))
      = if y <> t then begin
          color_change_preserves_other_color t y g Header.Gray;
          is_black_iff y g; is_black_iff y g';
          is_white_iff y g; is_white_iff y g';
          is_gray_iff y g; is_gray_iff y g';
          is_blue_iff y g; is_blue_iff y g'
        end
    in
    FStar.Classical.forall_intro col

/// Greying keeps every block's size, scan bit, freeness and fields.
let grey_shape (g: heap) (t y: obj_addr) (i: U64.t)
  : Lemma (requires well_formed_heap g /\ Seq.mem t (objects zero_addr g) /\ is_white t g /\
                    Seq.mem y (objects zero_addr g))
          (ensures (let g' = makeGray t g in
                    wosize_of_object y g' == wosize_of_object y g /\
                    is_no_scan y g' == is_no_scan y g /\
                    is_blue y g' == is_blue y g /\
                    (U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object y g) ==>
                     HG.get_field g' y i == HG.get_field g y i)))
  = grey_colours g t;
    color_change_preserves_wosize_any t y g Header.Gray;
    (if y = t then color_preserves_is_no_scan t g Header.Gray
     else color_change_preserves_other_is_no_scan t y g Header.Gray);
    (if U64.v i >= 1 && U64.v i <= U64.v (wosize_of_object y g)
     then Mark.color_preserves_get_field t y g Header.Gray i)

/// Greying keeps the strong tri-colour invariant: it only removes whiteness,
/// and keeps every black block, its fields and their resolution.
let grey_tri_colour_one (g: heap) (t b c: obj_addr)
  : Lemma (requires well_formed_heap g /\ Mark.tri_color_invariant g /\
                    Seq.mem t (objects zero_addr g) /\ is_white t g /\
                    Seq.mem b (objects zero_addr (makeGray t g)) /\ is_black b (makeGray t g) /\
                    ~(is_no_scan b (makeGray t g)) /\ points_to (makeGray t g) b c)
          (ensures ~(is_white (resolve_object c (makeGray t g)) (makeGray t g)))
  = let g' = makeGray t g in
    grey_colours g t;
    assert (b <> t);
    grey_shape g t b 0UL;
    color_change_preserves_points_to_other g t Header.Gray b c;
    color_change_preserves_resolve t c g Header.Gray;
    let r = resolve_object c g in
    assert (~(is_white r g))

let grey_tri_colour (g: heap) (t: obj_addr)
  : Lemma (requires well_formed_heap g /\ Mark.tri_color_invariant g /\
                    Seq.mem t (objects zero_addr g) /\ is_white t g)
          (ensures Mark.tri_color_invariant (makeGray t g))
  = let g' = makeGray t g in
    let aux (b c: obj_addr)
      : Lemma (Seq.mem b (objects zero_addr g') ==> is_black b g' ==> ~(is_no_scan b g') ==>
               points_to g' b c ==> ~(is_white (resolve_object c g') g'))
      = FStar.Classical.move_requires (grey_tri_colour_one g t b) c
    in
    FStar.Classical.forall_intro_2 aux

let grey_color_inv (g0 g: heap) (t: obj_addr)
  : Lemma (requires MBC.mark_color_inv g0 g /\ Seq.mem t (objects zero_addr g) /\ is_white t g)
          (ensures MBC.mark_color_inv g0 (makeGray t g))
  = let g' = makeGray t g in
    grey_colours g t;
    SweepInv.color_change_preserves_density t g Header.Gray;
    Mark.color_preserves_create_graph t g Header.Gray;
    grey_tri_colour g t;
    let sh (y: obj_addr)
      : Lemma (Seq.mem y (objects zero_addr g0) ==>
               (wosize_of_object y g' == wosize_of_object y g /\
                is_no_scan y g' == is_no_scan y g /\
                is_blue y g' == is_blue y g))
      = if Seq.mem y (objects zero_addr g0) then grey_shape g t y 0UL
    in
    FStar.Classical.forall_intro sh;
    let fd (y: obj_addr) (i: U64.t)
      : Lemma (Seq.mem y (objects zero_addr g0) /\ U64.v i >= 1 /\
               U64.v i <= U64.v (wosize_of_object y g0) ==>
               HG.get_field g' y i == HG.get_field g y i)
      = if Seq.mem y (objects zero_addr g0) then grey_shape g t y i
    in
    FStar.Classical.forall_intro_2 fd

/// The scanned field's target is reachable, as its scanned (grey) parent is.
let grey_target_reachable (g0 g: heap) (roots: seq obj_addr) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires MBC.mark_color_inv g0 g /\ MBC.gray_black_reachable g0 g roots /\
                    S.scan_target g x /\ U64.v k <= U64.v (wosize_of_object x g) /\
                    is_pointer (HG.get_field g x k) /\
                    Seq.mem (resolve_object (HG.get_field g x k) g) (objects zero_addr g))
          (ensures Seq.mem (resolve_object (HG.get_field g x k) g)
                     (DFS.reachable_set (HM.create_graph g0) (HG.coerce_to_vertex_list roots)))
  = let v = HG.get_field g x k in
    let t = resolve_object v g in
    let graph = HM.create_graph g0 in
    let roots' = HG.coerce_to_vertex_list roots in
    Mark.colors_exclusive x g;
    assert (Seq.mem x (DFS.reachable_set graph roots'));
    HM.objects_is_vertex_set g;
    Mark.wf_implies_object_fits g x;
    HG.pointer_field_is_graph_edge g (objects zero_addr g) x k;
    assert (G.mem_graph_edge (HM.create_graph g) x t);
    HM.graph_vertices_mem g x;
    HM.graph_vertices_mem g t;
    DFS.reachable_successor_closed graph roots' x t
let grey_gbr (g0 g: heap) (roots: seq obj_addr) (t: obj_addr)
  : Lemma (requires MBC.mark_color_inv g0 g /\ MBC.gray_black_reachable g0 g roots /\
                    Seq.mem t (objects zero_addr g) /\ is_white t g /\
                    Seq.mem t (DFS.reachable_set (HM.create_graph g0) (HG.coerce_to_vertex_list roots)))
          (ensures MBC.gray_black_reachable g0 (makeGray t g) roots)
  = grey_colours g t

let grey_stays (g0 g: heap) (t: obj_addr)
  : Lemma (requires MBC.mark_color_inv g0 g /\ MBC.gray_stays g0 g /\
                    Seq.mem t (objects zero_addr g) /\ is_white t g)
          (ensures MBC.gray_stays g0 (makeGray t g))
  = grey_colours g t;
    Mark.colors_exclusive t g

let grey_step (g0 g: heap) (roots: seq obj_addr) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires marking_inv_stw g0 g roots /\ S.scan_target g x /\
                    U64.v k <= U64.v (wosize_of_object x g))
          (ensures marking_inv_stw g0 (S.scan_field g x k) roots)
  = S.scan_field_is_grey g x k;
    let v = HG.get_field g x k in
    if is_pointer v && is_white (resolve_object v g) g then begin
      let t = resolve_object v g in
      grey_color_inv g0 g t;
      grey_target_reachable g0 g roots x k;
      grey_gbr g0 g roots t;
      grey_stays g0 g t
    end

/// ---------------------------------------------------------------------------
/// Moves
/// ---------------------------------------------------------------------------

let marking_inv_stw_move g0 g g' roots =
  eliminate S.grey_move g g' \/ S.black_move g g'
  with begin
    eliminate exists (x: obj_addr) (k: U64.t{U64.v k >= 1}).
      S.scan_target g x /\ U64.v k <= U64.v (wosize_of_object x g) /\ g' == S.scan_field g x k
    with grey_step g0 g roots x k
  end
  and begin
    eliminate exists (x: obj_addr).
      Seq.mem x (objects zero_addr g) /\ is_gray x g /\
      (is_no_scan x g \/ S.fields_dark g x 1 (U64.v (wosize_of_object x g))) /\
      g' == makeBlack x g
    with black_step g0 g roots x
  end

let marking_inv_stw_steps g0 g g' roots =
  let p (h: heap) : prop = marking_inv_stw g0 h roots in
  let step (h h': heap) : Lemma (requires p h /\ S.mark_move h h') (ensures p h') =
    marking_inv_stw_move g0 h h' roots
  in
  S.mark_steps_ind p step g g'

/// ---------------------------------------------------------------------------
/// End
/// ---------------------------------------------------------------------------

let marking_inv_stw_done g0 g roots fp =
  SweepInv.no_gray_intro g;
  MBC.mark_post_from_bounded_mark g0 g roots fp
