/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFComps - the first-fit collector, and all its contracts
/// ---------------------------------------------------------------------------
///
/// Design doc §13.  The second full instance on the byte representation:
/// akhil's first-fit allocator and fused sweep (GC.Spec.Top.FFAlloc,
/// FFSweep), with the same mark and write barrier as the pages collector
/// (GC.Spec.Top.ByteMark, ByteBarrier) and the same minor collection
/// (GC.Spec.Pages.Promote, generic in its allocator) run with first-fit's
/// allocator (GC.Spec.Top.FFMinor), over `byte_rep`.
/// `ff_components_ok`: every hypothesis of `gc_correct` about components
/// holds of it, with no assumption on the configuration (the initial free
/// block always has a field, `FFAlloc.init_facts`).

module GC.Spec.Top.FFComps

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.ByteRep
module FAl = GC.Spec.Top.FFAlloc
module FSw = GC.Spec.Top.FFSweep
module FFi = GC.Spec.Top.FFFits
module BM = GC.Spec.Top.ByteMark
module BB = GC.Spec.Top.ByteBarrier
module FM = GC.Spec.Top.FFMinor

let fc : comps =
  { t = GC.Spec.Base.heap; yt = GC.Gen.MinorHeap.minor_state; r = byte_rep;
    k = FAl.ffk; a = FAl.ffa; s = FSw.ffsweep; m = BM.bmark; n = FM.ffminor; b = BB.bbarrier; fits = FFi.fffits }

/// Room holds whenever the capacity condition does, in every state.
let ff_room_complete () : Lemma (room_complete fc)
  = let f (sty: style) (n ny: nat) (es: list event) (i: nat)
      : Lemma (run_ok fc sty n ny es /\ i <= FStar.List.Tot.length es ==>
               (let x = at fc n ny es i in
                forall (sz: size_t). fc.fits x.ph x.ast x.w.cmaj sz ==> fc.a.room x.ph x.ast x.w.cmaj sz == true))
      = let x = at fc n ny es i in
        FStar.Classical.forall_intro (FFi.fffits_room x.ph x.ast x.w.cmaj) in
    let f2 (sty: style) (n: nat) : Lemma (forall ny es i. run_ok fc sty n ny es /\ i <= FStar.List.Tot.length es ==>
               (let x = at fc n ny es i in
                forall (sz: size_t). fc.fits x.ph x.ast x.w.cmaj sz ==> fc.a.room x.ph x.ast x.w.cmaj sz == true))
      = FStar.Classical.forall_intro_3 (f sty n) in
    FStar.Classical.forall_intro_2 f2

/// **Every contract holds of the first-fit collector.**
let ff_components_ok () : Lemma (components_ok fc)
  = byte_rep_faithful ();
    GC.Spec.Top.FFFrame.ff_allocator_ok ();
    FFi.fffits_init ();
    ff_room_complete ();
    GC.Spec.Top.FFSweepOk.ff_sweep_ok ();
    BM.byte_mark_ok ();
    GC.Spec.Top.FFMinorOk.ff_minor_ok ();
    BB.byte_barrier_ok ()

/// **The contracts are not vacuous on the allocator's side**: the initial
/// heap meets the invariant idle and, by the start of marking, while
/// marking; the capacity condition holds there for one field, so the
/// allocation succeeds in both phases.  (Witness runs with roots, reachable
/// and unreachable blocks come with the runs.)
let ff_nonvacuous () : Lemma (let (h, s) = fc.a.init GC.Spec.Top.Word.msize in
                              fc.a.inv Idle h s /\ fc.a.inv Marking h s /\
                              fc.fits Idle s h 1 /\ fc.a.room Idle s h 1 == true /\ fc.a.room Marking s h 1 == true)
  = let (h, s) = fc.a.init GC.Spec.Top.Word.msize in
    GC.Spec.Top.Low.set_low_self h;
    GC.Spec.Top.FFInit.idle ();
    GC.Spec.Top.FFInit.objs ();
    FAl.init_facts ();
    assert (GC.Spec.FreeList.fl_cell h GC.Spec.Top.FFInit.x0);
    assert (fc.fits Idle s h 1);
    FFi.fffits_room Idle s h 1;
    GC.Spec.Top.FFInst.inv_start_ok h s;
    assert (fc.fits Marking s h 1);
    FFi.fffits_room Marking s h 1
