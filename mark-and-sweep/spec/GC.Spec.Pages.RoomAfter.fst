/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.RoomAfter - room for a second small object
/// ---------------------------------------------------------------------------
///
/// Plan §27.9.  When a page is free and a one-word allocation succeeds,
/// there is room for another one-word object: either the allocation took a
/// slot and changed no page's kind, so the free page is still free; or it
/// took a fresh pool page of the two-word class, which has at least two
/// slots (`two_slots`; 2048 with the chosen parameters), and left one
/// free.  So the allocator's "no room" (`GC.Spec.Pages.Theorems.no_fit`) is
/// false after it.

module GC.Spec.Pages.RoomAfter

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Seq = FStar.Seq
module P = GC.Spec.Pages.Pool
module PI = GC.Spec.Pages.PoolInit
module A = GC.Spec.Pages.Alloc
module Th = GC.Spec.Pages.Theorems
module Wt = GC.Spec.Pages.Witness

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// A page of the two-word class holds at least two slots.  A fact of the
/// parameters (2048 with the chosen ones), which `GC.Spec.Pages.Params`
/// keeps abstract; a hypothesis here, as `Cycle.Vacuity.roomy` is.
let two_slots : prop = n_slots Wt.cA >= 2

let small2 (_: unit) : Lemma (2 <= small_max) = Wt.sizes ()

let class2 (_: unit) : Lemma (2 <= small_max /\ Wt.cA == class_of 2)
  = small2 ()

let small_wz1 (_: unit) : Lemma (P.small_wz 1 Wt.cA)
  = class2 ();
    class_of_fits 2;
    P.small_wz_intro 1 Wt.cA

/// As a standing fact: the statements below mention `pop_as ... 1`.
let small_wz1_fact : squash (P.small_wz 1 Wt.cA) = small_wz1 ()

/// Taking a fresh pool page, then a slot of it, leaves the page with a free
/// slot.
#push-options "--z3rlimit 40"
let acq_pop (g: heap) (st: pstate) (i: nat{i < n_pages})
  : Lemma (requires two_slots /\ Seq.length st.avail == n_cls /\ P.avail_at st Wt.cA == 0UL /\
                    (let (g1, st1) = P.acquire g st i Wt.cA in
                     let (_, _, o) = P.pop_as false g1 st1 Wt.cA 1 in o =!= 0UL))
          (ensures (let (g1, st1) = P.acquire g st i Wt.cA in
                    let (_, s2, _) = P.pop_as false g1 st1 Wt.cA 1 in
                    has_free_slot s2.pm Wt.cA i))
  = class2 ();
    Wt.acq_kinds st i Wt.cA;
    let (g1, st1) = P.acquire g st i Wt.cA in
    assert (P.avail_at st1 Wt.cA == U64.uint_to_t (i + 1));
    assert (entry st1.pm i == P.acq_entry st i Wt.cA);
    assert ((entry st1.pm i).nfree == n_slots Wt.cA /\ (entry st1.pm i).swept /\ (entry st1.pm i).kind == Pool Wt.cA)
#pop-options

/// **Room for a second one-word object.**
#push-options "--z3rlimit 40"
let room_after (g: heap) (st: pstate) (j: nat{j < n_pages})
  : Lemma (requires two_slots /\ Seq.length st.avail == n_cls /\ Wt.kind_of st j == Free /\
                    (let (_, _, o) = A.alloc g st 1 in o =!= 0UL))
          (ensures (let (_, s1, _) = A.alloc g st 1 in ~(Th.no_fit g s1 2)))
  = class2 ();
    assert (A.alloc g st 1 == P.small_alloc_as false g st 1);
    let (_, s1, _) = A.alloc g st 1 in
    if P.avail_at st Wt.cA <> 0UL then begin
      Wt.pop_kinds false g st Wt.cA 1;
      assert (Wt.kind_of s1 j == Free)
    end else begin
      let i = P.find_free st.pm 0 in
      assert (i < n_pages);
      acq_pop g st i;
      assert (has_free_slot s1.pm (class_of 2) i)
    end
#pop-options
