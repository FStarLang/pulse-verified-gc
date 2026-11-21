/// ---------------------------------------------------------------------------
/// GC.Spec.Top.ToyComps - the toy collector, and all its contracts
/// ---------------------------------------------------------------------------
///
/// The toy components assembled into one collector `tc`, over the model heap
/// as its own representation (GC.Spec.Top.ToyRep), and `toy_components_ok`:
/// every hypothesis of `gc_correct` about components holds of it
/// (faithful representation, allocator, nontrivial, sweep, mark, minor,
/// barrier).

module GC.Spec.Top.ToyComps

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.IdRep
open GC.Spec.Top.ToyRep
open GC.Spec.Top.Toy
open GC.Spec.Top.ToyMark
open GC.Spec.Top.ToyMinor

/// Normalisation by evaluation: it computes the configurations of a run
/// with sharing (plain normalisation re-evaluates each heap once per use,
/// exponentially in the number of mark slices).
let assert_nbe (p: prop) : Pure unit (requires norm [nbe; iota; zeta; delta; primops] p) (ensures fun _ -> p)
  = norm_spec [nbe; iota; zeta; delta; primops] p

let tc : comps =
  { t = mheap; yt = mheap; r = toy_rep;
    k = tk; a = toy; s = tsweep; m = tmark; n = tminor; b = tbarrier; fits = toy_fits }

let toy_collector_nontrivial () : Lemma (nontrivial tc)
  = toy_fits_init ();
    let f (sty: style) (n ny: nat) (es: list event) (i: nat)
      : Lemma (run_ok tc sty n ny es /\ i <= FStar.List.Tot.length es ==>
               (let x = at tc n ny es i in
                forall (sz: size_t). tc.fits x.ph x.ast x.w.cmaj sz ==> tc.a.room x.ph x.ast x.w.cmaj sz == true))
      = let x = at tc n ny es i in
        FStar.Classical.forall_intro (toy_fits_room x.ph x.ast x.w.cmaj) in
    let f2 (sty: style) (n: nat) : Lemma (forall ny es i. run_ok tc sty n ny es /\ i <= FStar.List.Tot.length es ==>
               (let x = at tc n ny es i in
                forall (sz: size_t). tc.fits x.ph x.ast x.w.cmaj sz ==> tc.a.room x.ph x.ast x.w.cmaj sz == true))
      = FStar.Classical.forall_intro_3 (f sty n) in
    FStar.Classical.forall_intro_2 f2

let toy_components_ok () : Lemma (components_ok tc)
  = toy_rep_faithful ();
    toy_allocator_ok ();
    toy_collector_nontrivial ();
    toy_sweep_ok ();
    toy_mark_ok ();
    toy_minor_ok ();
    toy_barrier_ok ()

/// Reachability is within any set holding outside_refs and closed under edges.
let rec reach_within (w: world) (s: nat -> prop) (o: nat) (r: reach w o)
  : Lemma (requires (forall (x: nat). outside_ref w x ==> s x) /\
                    (forall (x x': nat). s x /\ major_edge w.maj x x' ==> s x'))
          (ensures s o)
          (decreases r)
  = match r with
    | RBase _ _ -> ()
    | RStep x _ r' _ -> reach_within w s x r'

let not_reachable (w: world) (s: nat -> prop) (o: nat)
  : Lemma (requires (forall (x: nat). outside_ref w x ==> s x) /\
                    (forall (x x': nat). s x /\ major_edge w.maj x x' ==> s x') /\ ~(s o))
          (ensures ~(reachable w o))
  = let aux (r: reach w o) : Lemma False = reach_within w s o r in
    FStar.Classical.forall_intro aux

/// A configuration of the toy is a world of model heaps; it is the one
/// model world that represents it.
let tc_views (x: config tc) (w: world) : Lemma (views x w <==> w == tview x.w)
  = toy_rep_id (); cviews_id toy_rep x.w w

let tc_vw (x: config tc) : Lemma (has_view x /\ vw x == tview x.w)
  = tc_views x (tview x.w);
    tc_views x (vw x)

/// Every word is storable, every size a size.
let tc_storable (vs: list value) : Lemma (storable_all tc.r vs) = ()

let tc_store (v: value) : Lemma (tc.r.storable v == true) = ()

let tc_sizes (n ny: nat) : Lemma (tc.r.size_ok n /\ tc.r.ysize_ok ny) = ()

/// The mutator's obligations, on the toy's world.
let mutator_of (x: config tc) (e: event)
  : Lemma (requires mutator_ok_w tc (tview x.w) e) (ensures mutator_ok x e)
  = tc_vw x
