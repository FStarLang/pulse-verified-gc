/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepingStart - the `Sweeping` invariant where the sweep starts
/// ---------------------------------------------------------------------------
///
/// `start_sweep` empties the lists and marks every page that is not free
/// unswept.  The invariant's clauses on lists and on the contents of pages
/// (L4, L5, L7, L8, L9) constrain swept pages only, and the shapes do not
/// change, so `start_sweep` keeps `pages_ok` (`start_keeps_ok`).
///
/// So the allocator's `Sweeping` invariant holds where the sequential sweep
/// starts, with every page that is not free unswept (`sweeping_at_start`).
/// This is the `Sweeping` phase's witness with unswept pages
/// (`GC.Spec.Pages.Vacuity.sweeping_witness`).

module GC.Spec.Pages.SweepingStart

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module FLs = GC.Spec.FreeLists
module FL = GC.Spec.FreeList
module AL = GC.Spec.Allocator.Lemmas
module Chain = GC.Spec.Allocator.Lemmas.Chain
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module AP = GC.Spec.Pages.AllocPhase
module SS = GC.Spec.Pages.StartSweep

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// Empty large lists are L9 when no run is swept, as for the empty heap of
/// pages (`Init.init_large_ok`).
#push-options "--fuel 1"
let empty_large_ok (g: heap) (st: pstate)
  : Lemma (requires st.large == FLs.fls_empty /\ (forall (y: obj_addr). ~(large_listable g st.pm y)))
          (ensures large_ok g st)
  = let fls = FLs.fls_empty in
    let null (i: nat) (y: U64.t)
      : Lemma (FLs.fls_head fls i == 0UL /\ AL.chain_avoids g 0UL y heap_words = true)
      = Chain.chain_avoids_null g y heap_words
    in
    FStar.Classical.forall_intro_2 null;
    AL.fl_valid_null g heap_words;
    FLs.fls_valid_intro g fls;
    AL.fl_chain_terminates_terminal g 0UL heap_words;
    FLs.fls_terminates_intro g fls;
    let sound (i: nat) (y: U64.t) : Lemma (~(FL.reachable_on_fl g (FLs.fls_head fls i) y))
      = introduce forall (n: nat). ~(FL.on_fl g 0UL y n) with (if n = 0 then () else ())
    in
    FStar.Classical.forall_intro_2 sound;
    FStar.Classical.forall_intro (FLs.fls_avoids_iff g fls)

/// Empty page lists are L8 when no pool page has a free slot it may hand out.
let empty_avail_ok (st: pstate)
  : Lemma (requires st.avail == Seq.create n_cls 0UL /\ st.atail == Seq.create n_cls 0UL /\
                    (forall (c: nat{c < n_cls}) (p: nat{p < n_pages}). ~(has_free_slot st.pm c p)))
          (ensures avail_ok st)
  = let aux (c: nat{c < n_cls})
      : Lemma (exists (ps: list nat).
                 page_chain st.pm (Seq.index st.avail c) ps /\ L.noRepeats ps /\
                 (forall (p: nat{p < n_pages}). L.mem p ps <==> has_free_slot st.pm c p) /\
                 Seq.index st.atail c == chain_tail ps)
      = assert (page_chain st.pm (Seq.index st.avail c) []);
        assert (L.noRepeats #nat [])
    in
    FStar.Classical.forall_intro aux
#pop-options

/// **`start_sweep` keeps `pages_ok`.**
let start_keeps_ok (g: heap) (st: pstate)
  : Lemma (requires pages_ok g st) (ensures pages_ok g (SS.start_sweep st))
  = let st' = SS.start_sweep st in
    GC.Spec.Pages.Step.pages_ok_elim g st;
    SS.clear_map_ok st.pm;
    FStar.Classical.forall_intro (SS.clear_entry st.pm);
    let shape (i: nat{i < n_pages}) : Lemma (page_shape g st'.pm i) = assert (page_shape g st.pm i) in
    FStar.Classical.forall_intro shape;
    let page (i: nat{i < n_pages})
      : Lemma (pool_list_ok g st'.pm i /\ pool_white g st'.pm i /\ run_swept_ok g st'.pm i) = ()
    in
    FStar.Classical.forall_intro page;
    let no_swept_run (y: obj_addr) : Lemma (~(large_listable g st'.pm y)) = () in
    FStar.Classical.forall_intro no_swept_run;
    empty_large_ok g st';
    empty_avail_ok st';
    reveal_opaque (`%pages_ok) pages_ok

/// **The `Sweeping` invariant holds where the sweep starts**: from the
/// `Marking` invariant, every page that is not free unswept.
let sweeping_at_start (g: heap) (st: pstate)
  : Lemma (requires PA.inv I.Marking g st)
          (ensures PA.inv I.Sweeping g (SS.start_sweep st) /\
                   (forall (j: nat{j < n_pages}). (entry (SS.start_sweep st).pm j).kind =!= Free ==>
                      not (entry (SS.start_sweep st).pm j).swept))
  = FStar.Classical.forall_intro (SS.clear_entry st.pm);
    eliminate exists (ys: list obj_addr). GC.Spec.Pages.ColourFacts.live_list g ys /\
                                     pages_ok (GC.Spec.Pages.Recolour.whiten g ys) st
    with start_keeps_ok (GC.Spec.Pages.Recolour.whiten g ys) st
