/// ---------------------------------------------------------------------------
/// GC.Spec.Top.ToyComps - the toy collector, and all its contracts
/// ---------------------------------------------------------------------------
///
/// The toy components assembled into one collector `tc`, and
/// `toy_components_ok`: every hypothesis of `gc_correct` about components
/// holds of it (allocator, nontrivial, sweep, mark, minor, barrier).

module GC.Spec.Top.ToyComps

open GC.Spec.Top.Heap
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Toy
open GC.Spec.Top.ToyMark
open GC.Spec.Top.ToyMinor

/// Normalisation by evaluation: it computes the configurations of a run
/// with sharing (plain normalisation re-evaluates each heap once per use,
/// exponentially in the number of mark slices).
let assert_nbe (p: prop) : Pure unit (requires norm [nbe; iota; zeta; delta; primops] p) (ensures fun _ -> p)
  = norm_spec [nbe; iota; zeta; delta; primops] p

let tc : comps = { k = tk; a = toy; s = tsweep; m = tmark; n = tminor; b = tbarrier; fits = toy_fits }

let toy_collector_nontrivial () : Lemma (nontrivial tc)
  = toy_fits_init ();
    let f (sty: style) (n ny: nat) (es: list event) (i: nat)
      : Lemma (run_ok tc sty n ny es /\ i <= FStar.List.Tot.length es ==>
               (let x = at tc n ny es i in
                forall (sz: size_t). tc.fits x.ph x.ast x.w.maj sz ==> tc.a.room x.ph x.ast x.w.maj sz == true))
      = let x = at tc n ny es i in
        FStar.Classical.forall_intro (toy_fits_room x.ph x.ast x.w.maj) in
    let f2 (sty: style) (n: nat) : Lemma (forall ny es i. run_ok tc sty n ny es /\ i <= FStar.List.Tot.length es ==>
               (let x = at tc n ny es i in
                forall (sz: size_t). tc.fits x.ph x.ast x.w.maj sz ==> tc.a.room x.ph x.ast x.w.maj sz == true))
      = FStar.Classical.forall_intro_3 (f sty n) in
    FStar.Classical.forall_intro_2 f2

let toy_components_ok () : Lemma (components_ok tc)
  = toy_allocator_ok ();
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
