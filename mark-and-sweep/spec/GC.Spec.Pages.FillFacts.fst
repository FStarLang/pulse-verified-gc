/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.FillFacts - writing the fields of a block in use
/// ---------------------------------------------------------------------------
///
/// Two facts of `GC.Spec.Pages.Cycle.Write` that the allocator with a tag
/// (`GC.Spec.Pages.AllocTagOk`) also uses, moved here so that it need not
/// depend on the page cycle: whitening keeps every object's size, closure
/// and no-scan tags (`whiten_obj`), and a write into the fields of a block
/// that is not free keeps "no grey block in an unswept page"
/// (`no_grey_fill`).  `Cycle.Write` keeps both names.

module GC.Spec.Pages.FillFacts

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module Rc = GC.Spec.Pages.Recolour
module F = GC.Spec.Pages.Fill
module Sc = GC.Spec.Pages.Scrub
module MS = GC.Spec.Pages.MidSweep

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// Whitening keeps the size, the closure tag and the no-scan tag of every
/// object.
#push-options "--fuel 1 --ifuel 1"
let rec whiten_obj (g: heap) (ys: list obj_addr) (y: obj_addr)
  : Lemma (ensures (let gw = Rc.whiten g ys in
                    wosize_of_object y gw == wosize_of_object y g /\
                    is_closure y gw == is_closure y g /\
                    is_no_scan y gw == is_no_scan y g))
          (decreases ys)
  = match ys with
    | [] -> ()
    | x :: ys' ->
      whiten_obj g ys' y;
      let g' = Rc.whiten g ys' in
      Rc.whiten_step_eq g' x;
      color_change_preserves_wosize_any x y g' Header.White;
      color_change_preserves_is_closure x y g' Header.White;
      if x = y then color_preserves_is_no_scan y g' Header.White
      else color_change_preserves_other_is_no_scan x y g' Header.White
#pop-options

/// No grey block appears in an unswept page: the headers its clauses read
/// are walk positions, kept by a write into the fields of a block that is
/// not free.
let no_grey_fill (g g': heap) (x: obj_addr) (st: pstate)
  : Lemma (requires F.fctx g g' x /\ ~(is_blue x g) /\ Sc.core g st /\ MS.no_grey_unswept g st.pm)
          (ensures MS.no_grey_unswept g' st.pm)
  = let pm = st.pm in
    Sc.core_shape g st;
    let pool (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat)
      : Lemma (requires (entry pm i).kind == Pool c /\ not (entry pm i).swept /\ k < n_slots c /\
                        slot_used g' i c k)
              (ensures color_at g' (slot_base i c k) =!= Header.Gray)
      = assert (page_shape g pm i);
        walk_pages_reached g pm i;
        F.pool_fill_slots g g' x i c;
        assert (F.slot_same g g' i c k)
    in
    FStar.Classical.forall_intro_3 (fun i c k -> FStar.Classical.move_requires (pool i c) k);
    let run (h: nat{h < n_pages}) (a: nat)
      : Lemma (requires LargeHead? (entry pm h).kind /\ not (entry pm h).swept /\
                        run_block g' h (run_len (entry pm h).kind) a)
              (ensures color_at g' a =!= Header.Gray)
      = let n = run_len (entry pm h).kind in
        assert (page_shape g pm h);
        assert (run_shape g h n);
        walk_pages_reached g pm h;
        F.run_block_fill g g' x h n a
    in
    FStar.Classical.forall_intro_2 (fun h a -> FStar.Classical.move_requires (run h) a)
