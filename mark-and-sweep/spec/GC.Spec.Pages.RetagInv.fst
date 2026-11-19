/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.RetagInv - the page invariants across a retag and a fill
/// ---------------------------------------------------------------------------
///
/// Plan §27.1.  From a heap `g0` in a page invariant, a heap `gt` that
/// rewrites the header of a non-free object `x` at its size and colour
/// (`Retag.rctx`), then a heap `g''` that writes its fields (`F.fctx`): if
/// `g''` is well formed, it is in the same invariant.  For the `Marking`
/// invariant (`AP.pages_ok_mc`, up to colours) the same steps are taken on
/// the whitened heaps (`mc_chain`); for the mid-sweep one (`MS.pages_ok_sw`)
/// directly (`sw_chain`).

module GC.Spec.Pages.RetagInv

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
open GC.Spec.Pages.Frame
open GC.Spec.Pages.Replace
open GC.Spec.Pages.Retag

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module F = GC.Spec.Pages.Fill
module Sc = GC.Spec.Pages.Scrub
module Rc = GC.Spec.Pages.Recolour
module CF = GC.Spec.Pages.ColourFacts
module AP = GC.Spec.Pages.AllocPhase
module MS = GC.Spec.Pages.MidSweep
module CW = GC.Spec.Pages.FillFacts
module Wf = GC.Spec.Pages.Wf

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Whitening commutes with both steps
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30"
let w_rctx (h h': heap) (x: obj_addr) (ys: list obj_addr)
  : Lemma (requires rctx h h' x /\ CF.live_list h ys)
          (ensures rctx (Rc.whiten h ys) (Rc.whiten h' ys) x)
  = r_objs h h' x;
    CF.whiten_facts h ys;
    Rc.hx_word x;
    hd_address_spec x;
    let rd (a: hp_addr)
      : Lemma (a <> hd_address x ==> read_word (Rc.whiten h' ys) a == read_word (Rc.whiten h ys) a)
      = Rc.paint_read h ys White a; Rc.paint_read h' ys White a
    in
    FStar.Classical.forall_intro rd;
    let a = hd_address x in
    Rc.paint_read h ys White a; Rc.paint_read h' ys White a;
    r_hdr h h' x (U64.v x - 8);
    assert (mk_hp_addr (U64.v x - 8) == a);
    colorHeader_preserves_wosize (read_word h a) White;
    colorHeader_preserves_wosize (read_word h' a) White;
    colorHeader_getColor (read_word h a) White;
    colorHeader_getColor (read_word h' a) White
#pop-options

let w_fctx (h h': heap) (x: obj_addr) (ys: list obj_addr)
  : Lemma (requires F.fctx h h' x /\ CF.live_list h ys)
          (ensures F.fctx (Rc.whiten h ys) (Rc.whiten h' ys) x)
  = CF.whiten_facts h ys;
    CW.whiten_obj h ys x;
    let rd (a: hp_addr)
      : Lemma (U64.v a < U64.v x \/ U64.v a >= F.fields_end h x ==>
               read_word (Rc.whiten h' ys) a == read_word (Rc.whiten h ys) a)
      = Rc.paint_read h ys White a; Rc.paint_read h' ys White a
    in
    FStar.Classical.forall_intro rd

/// ---------------------------------------------------------------------------
/// The chains
/// ---------------------------------------------------------------------------

let core_chain (g0 gt g'': heap) (x: obj_addr) (st: pstate)
  : Lemma (requires Sc.core g0 st /\ rctx g0 gt x /\ F.fctx gt g'' x)
          (ensures Sc.core g'' st)
  = core_retag g0 gt x st;
    r_objs g0 gt x;
    Sc.core_fill gt g'' x st

/// The live objects stay live through both steps.
let live_chain (g0 gt g'': heap) (x: obj_addr) (ys: list obj_addr)
  : Lemma (requires rctx g0 gt x /\ F.fctx gt g'' x /\ CF.live_list g0 ys)
          (ensures CF.live_list gt ys /\ CF.live_list g'' ys)
  = r_objs g0 gt x;
    let one (y: obj_addr)
      : Lemma (requires L.mem y ys) (ensures Seq.mem y (objects zero_addr g'') /\ ~(is_blue y g''))
      = F.obj_same gt g'' x y;
        color_of_header_eq y gt g'';
        is_blue_iff y gt; is_blue_iff y g''
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// **The `Marking` invariant up to colours.**
#push-options "--z3rlimit 30"
let mc_chain (g0 gt g'': heap) (x: obj_addr) (st: pstate)
  : Lemma (requires AP.pages_ok_mc g0 st /\ rctx g0 gt x /\ F.fctx gt g'' x /\ well_formed_heap g'')
          (ensures AP.pages_ok_mc g'' st)
  = eliminate exists (ys: list obj_addr). CF.live_list g0 ys /\ pages_ok (Rc.whiten g0 ys) st
    with begin
      live_chain g0 gt g'' x ys;
      CF.whiten_facts g'' ys;
      Sc.core_of_ok (Rc.whiten g0 ys) st;
      w_rctx g0 gt x ys;
      w_fctx gt g'' x ys;
      core_chain (Rc.whiten g0 ys) (Rc.whiten gt ys) (Rc.whiten g'' ys) x st;
      Wf.wfh_old_parts ();
      Sc.ok_of_core (Rc.whiten g'' ys) st
    end
#pop-options

/// No grey block in an unswept page, across a retag.
let no_grey_r (g g': heap) (x: obj_addr) (pm: page_map)
  : Lemma (requires rctx g g' x /\ MS.no_grey_unswept g pm) (ensures MS.no_grey_unswept g' pm)
  = all_eq g g' x;
    let pool (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat)
      : Lemma (requires (entry pm i).kind == Pool c /\ not (entry pm i).swept /\ k < n_slots c /\
                        slot_used g' i c k)
              (ensures color_at g' (slot_base i c k) =!= Gray)
      = slot_eq g g' x i c k
    in
    FStar.Classical.forall_intro_3 (fun i c k -> FStar.Classical.move_requires (pool i c) k);
    let run (h: nat{h < n_pages}) (a: nat)
      : Lemma (requires LargeHead? (entry pm h).kind /\ not (entry pm h).swept /\
                        run_block g' h (run_len (entry pm h).kind) a)
              (ensures color_at g' a =!= Gray)
      = r_steps g g' x (page_base h) a;
        r_hdr g g' x a;
        assert (run_block g h (run_len (entry pm h).kind) a)
    in
    FStar.Classical.forall_intro_2 (fun h a -> FStar.Classical.move_requires (run h) a)

/// **The mid-sweep invariant.**
let sw_chain (g0 gt g'': heap) (x: obj_addr) (st: pstate)
  : Lemma (requires MS.pages_ok_sw g0 st /\ rctx g0 gt x /\ F.fctx gt g'' x /\
                    well_formed_heap_with (MS.free_sw st.pm) g'')
          (ensures MS.pages_ok_sw g'' st)
  = MS.pages_ok_sw_elim g0 st;
    core_retag g0 gt x st;
    no_grey_r g0 gt x st.pm;
    r_objs g0 gt x;
    CW.no_grey_fill gt g'' x st;
    Sc.core_fill gt g'' x st;
    MS.pages_ok_sw_intro g'' st
