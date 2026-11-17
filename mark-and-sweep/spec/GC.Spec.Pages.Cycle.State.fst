/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cycle.State - the page states of the incremental cycle
/// ---------------------------------------------------------------------------
///
/// Plan §23.2-23.3.  The facts about the page allocator's states that the
/// page cycle (`GC.Spec.Pages.Cycle.*`) uses, from the page proofs:
///
///   - **the walk** (`walk_full`): in the `Idle`, `Marking` and mid-sweep
///     invariants the walk of the heap reaches `heap_size` exactly, and the
///     heap is dense (`GC.Spec.Pages.TailWalk`, through whitening for
///     `Marking`);
///   - **mark moves keep the `Marking` invariant** (`mark_steps_inv`): a move
///     only recolours an object that is not free, which
///     `GC.Spec.Pages.MarkPhase.mark_inv_recolour` keeps;
///   - **the hand-over** (`handover_ready`): with nothing grey, the
///     `Marking` invariant is the start of the page sweep (`sweep_ready` of
///     `start_sweep`, and `mark_done`).

module GC.Spec.Pages.Cycle.State

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
open GC.Spec.Pages.Recolour
open GC.Spec.Pages.ColourFacts
open GC.Spec.Pages.AllocPhase

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module W = GC.Spec.Walk
module HG = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module MPh = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module S = GC.Spec.MarkPhase.Slice
module TW = GC.Spec.Pages.TailWalk
module St = GC.Spec.Pages.Step
module PMP = GC.Spec.Pages.MarkPhase
module MS = GC.Spec.Pages.MidSweep
module SA = GC.Spec.Pages.SweepAll
module SS = GC.Spec.Pages.StartSweep
module Wf = GC.Spec.Pages.Wf
module Th = GC.Spec.Pages.Theorems
module NO = GC.Spec.Pages.NewOnly
module F = GC.Spec.Pages.Fill
module B = GC.Spec.Pages.Blocks
module A = GC.Spec.Pages.Alloc
module AP = GC.Spec.Pages.AllocPhase
module MPA = GC.Spec.MarkPhase.Alloc
module SPI = GC.Spec.SweepPhase.Intrinsic
module PA = GC.Spec.Pages.Allocator
module I = GC.Spec.AllocIface

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The walk
/// ---------------------------------------------------------------------------

/// The walk of `g` reaches the end of the heap exactly, and `g` is dense.
let walk_full (g: heap) : prop =
  W.reaches g zero_addr heap_size /\ W.walk_end g zero_addr == heap_size /\
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0

let ok_walk (g: heap) (st: pstate)
  : Lemma (requires pages_ok g st) (ensures walk_full g)
  = St.pages_ok_elim g st;
    TW.shape_walk_end g st.pm

/// Whitening changes only colours, so it keeps the walk.
let whiten_walk (g: heap) (ys: list obj_addr)
  : Lemma (requires walk_full (whiten g ys)) (ensures walk_full g)
  = let gw = whiten g ys in
    let sz (q: hp_addr)
      : Lemma (getWosize (read_word g q) == getWosize (read_word gw q))
      = paint_read g ys White q;
        colorHeader_preserves_wosize (read_word g q) White
    in
    FStar.Classical.forall_intro sz;
    W.walk_congr gw g zero_addr;
    W.walk_end_of_reaches g zero_addr heap_size;
    W.reaches_unfold g zero_addr heap_size;
    W.dense_of_reaches_end g heap_size

let mc_walk (g: heap) (st: pstate)
  : Lemma (requires pages_ok_mc g st) (ensures walk_full g)
  = eliminate exists (ys: list obj_addr). live_list g ys /\ pages_ok (whiten g ys) st
    with begin
      ok_walk (whiten g ys) st;
      whiten_walk g ys
    end

let sw_walk (g: heap) (st: pstate)
  : Lemma (requires MS.pages_ok_sw g st) (ensures walk_full g)
  = MS.pages_ok_sw_elim g st;
    TW.shape_walk_end g st.pm

/// ---------------------------------------------------------------------------
/// Mark moves keep the `Marking` invariant
/// ---------------------------------------------------------------------------

/// Darkening a value greys a white object, if it names one.
let darken_mark_inv (st: pstate) (g: heap) (w: U64.t)
  : Lemma (requires PMP.mark_inv g st) (ensures PMP.mark_inv (MM.darken g w) st)
  = if is_pointer w &&
       Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
       is_white (resolve_object (w <: obj_addr) g) g
    then begin
      let t = resolve_object (w <: obj_addr) g in
      Mark.colors_exclusive t g;
      makeGray_eq t g;
      PMP.mark_inv_recolour g st t Gray
    end

/// Blackening a grey object.
let blacken_mark_inv (st: pstate) (g: heap) (x: obj_addr)
  : Lemma (requires PMP.mark_inv g st /\ Seq.mem x (objects zero_addr g) /\ is_gray x g)
          (ensures PMP.mark_inv (makeBlack x g) st)
  = Mark.colors_exclusive x g;
    makeBlack_eq x g;
    PMP.mark_inv_recolour g st x Black

let move_mark_inv (st: pstate) (g: heap) (sp: MPh.scan_pos) (g': heap) (sp': MPh.scan_pos)
  : Lemma (requires PMP.mark_inv g st /\ S.mark_move g sp g' sp')
          (ensures PMP.mark_inv g' st)
  = let grey (x: obj_addr)
      : Lemma (requires x == sp.MPh.cur /\ S.scan_target g x /\ 1 <= sp.MPh.fld /\
                        sp.MPh.fld <= U64.v (wosize_of_object x g) /\
                        g' == S.scan_field g x (U64.uint_to_t sp.MPh.fld))
              (ensures PMP.mark_inv g' st)
      = darken_mark_inv st g (HG.get_field g x (U64.uint_to_t sp.MPh.fld))
    in
    let black (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g) /\ is_gray x g /\ g' == makeBlack x g)
              (ensures PMP.mark_inv g' st)
      = blacken_mark_inv st g x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires grey);
    FStar.Classical.forall_intro (FStar.Classical.move_requires black)

/// **Mark moves keep the `Marking` invariant.**
let mark_steps_inv (st: pstate) (g: heap) (sp: MPh.scan_pos) (g': heap) (sp': MPh.scan_pos)
  : Lemma (requires PMP.mark_inv g st /\ S.mark_steps g sp g' sp')
          (ensures PMP.mark_inv g' st)
  = S.mark_steps_ind (fun h q -> PMP.mark_inv h st) (move_mark_inv st) g sp g' sp'

/// ---------------------------------------------------------------------------
/// The hand-over
/// ---------------------------------------------------------------------------

/// **With nothing grey, the `Marking` invariant starts the page sweep.**
let handover_ready (g: heap) (st: pstate) (o: obj_addr -> prop) (sp: MPh.scan_pos)
  : Lemma (requires PMP.mark_inv g st /\ MPh.marking_inv g o sp /\ Mark.noGreyObjects g)
          (ensures SA.sweep_ready g (SS.start_sweep st) /\ SA.mark_done g)
  = SS.start_ready g st;
    MPh.marking_done g o sp;
    Wf.wfh_old_parts_one g

/// ---------------------------------------------------------------------------
/// Allocation while marking
/// ---------------------------------------------------------------------------

/// Whitening never makes an object free.
let whiten_not_blue (g: heap) (ys: list obj_addr) (y: obj_addr)
  : Lemma (requires ~(is_blue y g)) (ensures ~(is_blue y (whiten g ys)))
  = let h = hd_address y in
    paint_read g ys White h;
    colorHeader_getColor (read_word g h) White;
    is_blue_iff y g;
    is_blue_iff y (whiten g ys);
    color_of_object_spec y g;
    color_of_object_spec y (whiten g ys)

/// Recolouring the new object keeps every other header.
let recolour_other (g: heap) (o: obj_addr) (col: color) (y: obj_addr)
  : Lemma (requires col <> Blue /\ y <> o)
          (ensures objects zero_addr (AP.recolour g (o <: U64.t) col) == objects zero_addr g /\
                   read_word (AP.recolour g (o <: U64.t) col) (hd_address y) == read_word g (hd_address y))
  = AP.recolour_eq g o col;
    color_change_preserves_objects g o col;
    hd_address_spec y;
    hd_address_spec o;
    color_change_header_locality o (hd_address y) g col

/// **Allocation while marking makes only the new object non-free.**  The
/// allocator run on the whitened heap is the whitened allocator
/// (`AllocPhase.base`), where `NewOnly.alloc_new_only` holds; whitening and
/// recolouring the new object change no other object's freedom.
#push-options "--z3rlimit 40"
let mark_new_only (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires PMP.mark_inv g st)
          (ensures (let (g', _, o) = PA.alloc I.Marking g st wz in NO.new_only g g' o))
  = eliminate exists (ys: list obj_addr). live_list g ys /\ pages_ok (whiten g ys) st
    with begin
      let (ga, sa, o) = A.alloc g st wz in
      let gw = whiten g ys in
      base g ys st wz;
      NO.alloc_new_only gw st wz;
      assert (NO.new_only gw (whiten ga ys) o);
      let (g', _, o') = PA.alloc I.Marking g st wz in
      assert (o' == o);
      let one (y: obj_addr)
        : Lemma (requires Seq.mem y (objects zero_addr g') /\ ~(is_blue y g') /\ U64.v y <> U64.v o)
                (ensures Seq.mem y (objects zero_addr g) /\ ~(is_blue y g))
        = (if o = 0UL then ()
           else begin
             let x : obj_addr = o in
             recolour_other ga x Black y;
             assert (g' == AP.recolour ga o Black);
             color_of_header_eq y ga g';
             is_blue_iff y ga; is_blue_iff y g'
           end);
          assert (Seq.mem y (objects zero_addr ga) /\ ~(is_blue y ga));
          whiten_not_blue ga ys y
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires one)
    end
#pop-options

/// A block whose header and fields are kept is the same block.
let kept_same_block (g g': heap) (y: obj_addr)
  : Lemma (requires read_word g' (hd_address y) == read_word g (hd_address y) /\
                    (forall (b: hp_addr). U64.v y <= U64.v b /\
                       U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 ==>
                       read_word g' b == read_word g b))
          (ensures SPI.same_block g g' (hd_address y))
  = hd_address_spec y;
    wosize_of_object_spec y g

/// Headers kept, objects kept: no infix block, and the blocks fit.
let fill_back (g' g'': heap) (x: obj_addr)
  : Lemma (requires F.fctx g' g'' x /\ no_infix_block g'' /\ blocks_fit g'')
          (ensures no_infix_block g' /\ blocks_fit g')
  = let one (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g'))
              (ensures ~(is_infix y g') /\
                       U64.v (hd_address y) + 8 + U64.v (wosize_of_object y g') * 8 <= Seq.length g')
      = F.obj_same g' g'' x y;
        is_infix_spec y g';
        is_infix_spec y g'';
        tag_of_object_spec y g';
        tag_of_object_spec y g'';
        wosize_of_object_spec y g';
        wosize_of_object_spec y g''
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// **Allocation while marking, the heap facts**: the new object is a black
/// block that was not in use; every block in use keeps its header and
/// fields; the blocks in use after, with the new object counted free, are
/// those before; and the heap has no infix block and its blocks fit.
#push-options "--z3rlimit 40"
let mark_alloc_facts (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires PMP.mark_inv g st)
          (ensures (let (g', st', o) = PA.alloc I.Marking g st wz in
                    o =!= 0UL ==>
                    U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                    (let x : obj_addr = o in
                     Seq.mem x (objects zero_addr g') /\ is_black x g' /\
                     ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                     MPA.keeps_blocks free_stw g g' /\
                     (forall (y: obj_addr). in_use (MPA.free_or_new x) g' y == in_use free_stw g y) /\
                     no_infix_block g' /\ blocks_fit g')))
  = let (g', st', o) = PA.alloc I.Marking g st wz in
    PMP.mark_inv_alloc g st wz;
    assert (PA.alloc I.Marking g st wz == AP.alloc_col Black g st wz);
    mark_new_only g st wz;
    if o <> 0UL then begin
      let x : obj_addr = o in
      is_black_iff x g';
      let kb (y: obj_addr)
        : Lemma (requires in_use free_stw g y)
                (ensures Seq.mem y (objects zero_addr g') /\
                         read_word g' (hd_address y) == read_word g (hd_address y) /\
                         SPI.same_block g g' (hd_address y))
        = kept_same_block g g' y
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires kb);
      let iu (y: obj_addr) : Lemma (in_use (MPA.free_or_new x) g' y == in_use free_stw g y)
        = if in_use free_stw g y then begin
            kb y;
            color_of_header_eq y g g';
            is_blue_iff y g; is_blue_iff y g'
          end
      in
      FStar.Classical.forall_intro iu;
      let g'' = B.zeros g' (U64.v x) (U64.v (wosize_of_object x g')) in
      F.cleared_written g' x;
      assert (PMP.mark_inv g'' st');
      wf_with_parts ();
      fill_back g' g'' x
    end
#pop-options
