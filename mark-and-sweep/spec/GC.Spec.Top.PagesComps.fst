/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesComps - the pages collector, and all its contracts
/// ---------------------------------------------------------------------------
///
/// The byte-level collector with the page allocator and sweep
/// (GC.Spec.Top.PagesAlloc, PagesSweep), akhil's mark and write barrier on
/// the byte heap (GC.Spec.Top.ByteMark, ByteBarrier), and the minor
/// collection of GC.Spec.Pages.Promote with the page instances
/// (GC.Spec.Top.PagesMinor), over `byte_rep`.  `pages_components_ok`: every
/// hypothesis of `gc_correct` about components holds of it, when there is a
/// page (`n_pages > 0`; the page count is a function of the abstract
/// `heap_size`, so this is an assumption on the configuration, G34).

module GC.Spec.Top.PagesComps

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.ByteRep
module PAl = GC.Spec.Top.PagesAlloc
module PSw = GC.Spec.Top.PagesSweep
module PFi = GC.Spec.Top.PagesFits
module BM = GC.Spec.Top.ByteMark
module BB = GC.Spec.Top.ByteBarrier
module PM = GC.Spec.Top.PagesMinor

let pc : comps =
  { t = GC.Spec.Base.heap; yt = GC.Gen.MinorHeap.minor_state; r = byte_rep;
    k = PAl.pk; a = PAl.pa; s = PSw.psweep; m = BM.bmark; n = PM.pminor; b = BB.bbarrier; fits = PFi.pfits }

/// Room holds whenever the capacity condition does, in every state.
let pages_room_complete () : Lemma (room_complete pc)
  = let f (sty: style) (n ny: nat) (es: list event) (i: nat)
      : Lemma (run_ok pc sty n ny es /\ i <= FStar.List.Tot.length es ==>
               (let x = at pc n ny es i in
                forall (sz: size_t). pc.fits x.ph x.ast x.w.cmaj sz ==> pc.a.room x.ph x.ast x.w.cmaj sz == true))
      = let x = at pc n ny es i in
        FStar.Classical.forall_intro (PFi.pfits_room x.ph x.ast x.w.cmaj) in
    let f2 (sty: style) (n: nat) : Lemma (forall ny es i. run_ok pc sty n ny es /\ i <= FStar.List.Tot.length es ==>
               (let x = at pc n ny es i in
                forall (sz: size_t). pc.fits x.ph x.ast x.w.cmaj sz ==> pc.a.room x.ph x.ast x.w.cmaj sz == true))
      = FStar.Classical.forall_intro_3 (f sty n) in
    FStar.Classical.forall_intro_2 f2

/// **Every contract holds of the pages collector**, when there is a page.
let pages_components_ok () : Lemma (requires GC.Spec.Pages.Layout.n_pages > 0) (ensures components_ok pc)
  = byte_rep_faithful ();
    GC.Spec.Top.PagesFrame.pages_allocator_ok ();
    PFi.pfits_init ();
    pages_room_complete ();
    GC.Spec.Top.PagesStepOk.pages_sweep_ok ();
    BM.byte_mark_ok ();
    GC.Spec.Top.PagesMinorOk.pages_minor_ok ();
    BB.byte_barrier_ok ()
