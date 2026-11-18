/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cycle.CarriedVacuity - a run with the page invariant
/// carried, built
/// ---------------------------------------------------------------------------
///
/// The vacuity rule (plan §18) for `GC.Spec.Pages.Cycle.Carried`:
/// `run_carried g` is `Cycle.VacuityDark.run_dark` as a run of `ccycle`,
/// event for event -- root darkening, an allocation while marking, the
/// barrier write that darkens B, the hand-over, the sweep's start, a page
/// step, an allocation mid-sweep, a program write mid-sweep that stores a
/// pointer into A, a step at every unit, the end -- with only the events'
/// own hypotheses shown: none of them is the page invariant.
///
/// `run_carried_theorems` applies `ccycle_correct`: the page `Idle`
/// invariant holds at the end, A and B survive, and the heap's last word is
/// covered both ways; `run_carried_nontrivial` is what makes the run say
/// something (B reachable at the start, white when the barrier cut A's
/// pointer to it, grey after; A's field written with pointers twice).

module GC.Spec.Pages.Cycle.CarriedVacuity

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module MP = GC.Spec.MarkPhase
module GMC = GC.Gen.MarkPhase.Completeness
module MStart = GC.Gen.MarkPhase.Start
module SPC = GC.Spec.SweepPhase.Completeness
module LL = GC.Spec.FusedSweep.Lossless
module GC_ = GC.Gen.Cycle
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module SA = GC.Spec.Pages.SweepAll
module MS = GC.Spec.Pages.MidSweep
module Wt = GC.Spec.Pages.Witness
module V = GC.Spec.Pages.Cycle.Vacuity
module D = GC.Spec.Pages.Cycle.VacuityDark
module C = GC.Spec.Pages.Cycle.Carried

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// A step at every unit, from page `p` on: no hypothesis.
#push-options "--fuel 1 --ifuel 1"
let rec crest (#g0 #g: heap) (#s: pstate) (#since: obj_addr -> prop)
              (r: C.csweep g0 g s I.Sweeping since) (p: nat)
  : Ghost (C.csweep g0 (fst (SA.sweep_from g s p)) (snd (SA.sweep_from g s p)) I.Sweeping since)
          (requires True)
          (ensures fun r' -> C.cstart_st r' == C.cstart_st r)
          (decreases (if p < n_pages then n_pages - p else 0))
  = if p >= n_pages then r
    else begin
      let k = span s.pm p in
      crest (C.CSStep r p) (p + k)
    end
#pop-options

/// **`run_dark`, carried.**
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let run_carried (g: heap{V.roomy})
  : GTot (C.ccycle (D.h g) (D.rs g) (D.gf g) (D.sf g) I.Idle (D.since_d g)) =
  D.start_pre g;
  D.darkened_a g;
  D.gd_ok g;
  D.mal_ok g;
  D.gz_ok g;
  D.n1_storable g;
  D.write_ok g;
  D.gw_ok g;
  D.marks g;
  D.gh_no_grey g;
  D.alloc_ok g;
  D.swrite_ok g;
  D.rest_ends g;
  let rm0 : C.cmarking (D.h g) (D.rs g) (MStart.darkened (D.h g) (D.rs g)) (D.st g) MP.scan_none SPC.nothing_new =
    C.CStart V.m0 (D.st g) () in
  let rm1 : C.cmarking (D.h g) (D.rs g) (D.gz g) (D.sb g) MP.scan_none (D.since_m g) =
    C.CAlloc rm0 V.m0 Wt.wzS (D.gb g) (D.sb g) (D.n1 g) () (D.gz g) (D.iw g) () in
  let rm2 : C.cmarking (D.h g) (D.rs g) (D.gw g) (D.sb g) MP.scan_none (D.since_m g) =
    C.CWrite rm1 V.m0 (D.oa g) (D.oa g <: hp_addr) (D.n1 g <: U64.t) () in
  let r0 : C.csweep (D.gh g) (D.gh g) (D.s0 g) I.Sweeping SPC.nothing_new = C.CSStart (D.s0 g) in
  let r1 : C.csweep (D.gh g) (D.g1 g) (D.s1 g) I.Sweeping SPC.nothing_new = C.CSStep r0 (D.jc g) in
  let r2 : C.csweep (D.gh g) (D.g2 g) (D.s2 g) I.Sweeping (SPC.with_new SPC.nothing_new (D.oo g <: U64.t)) =
    C.CSAlloc r1 Wt.wzS (D.ga g) (D.s2 g) (D.oo g) () (D.g2 g) () in
  let r3 : C.csweep (D.gh g) (D.g3 g) (D.s2 g) I.Sweeping (SPC.with_new SPC.nothing_new (D.oo g <: U64.t)) =
    C.CSWrite r2 (D.oa g) (D.oa g <: hp_addr) (D.oo g <: U64.t) () in
  let r4 = crest r3 0 in
  let r5 : C.csweep (D.gh g) (D.gf g) (D.sf g) I.Idle (SPC.with_new SPC.nothing_new (D.oo g <: U64.t)) =
    C.CSEnd r4 () in
  assert (C.cstart_st r0 == D.s0 g);
  assert (C.cstart_st r1 == C.cstart_st r0);
  assert (C.cstart_st r2 == C.cstart_st r1);
  assert (C.cstart_st r3 == C.cstart_st r2);
  assert (C.cstart_st r5 == C.cstart_st r4);
  C.CSweep rm2 V.m0 (D.gh g) MP.scan_none () r5 ()
#pop-options

/// **It is not trivial** (the same heaps as `run_dark`): A and B are
/// reachable at the start; the barrier overwrote A's pointer to B while B
/// was white, and B was grey after; mid-sweep A's field got a pointer to
/// O, a block not in use before; N and O are handed out.
let run_carried_nontrivial (g: heap)
  : Lemma (requires V.roomy)
          (ensures GMC.reachable_at_start (D.h g) (D.rs g) (D.oa g) /\
                   GMC.reachable_at_start (D.h g) (D.rs g) (D.ob g) /\
                   read_word (D.gz g) (D.oa g <: hp_addr) == (D.ob g <: U64.t) /\
                   is_white (D.ob g) (D.gz g) /\ is_gray (D.ob g) (D.gw g) /\
                   read_word (D.gw g) (D.oa g <: hp_addr) == (D.n1 g <: U64.t) /\
                   read_word (D.g3 g) (D.oa g <: hp_addr) == (D.oo g <: U64.t) /\ is_pointer (D.oo g <: U64.t) /\
                   ~(in_use (MS.free_sw (D.s1 g).pm) (D.g1 g) (D.oo g)) /\
                   D.since_d g (D.n1 g) /\ D.since_d g (D.oo g))
  = D.run_dark_nontrivial g

/// **The theorem on it**: the run ends in the page `Idle` invariant; A and
/// B survive, at their sizes, not handed out; the heap's last word lies in
/// a block unreachable at the start exactly when it is free or new.
let run_carried_theorems (g: heap)
  : Lemma (requires V.roomy)
          (ensures PA.inv I.Idle (D.gf g) (D.sf g) /\
                   Seq.mem (D.oa g) (objects zero_addr (D.gf g)) /\ ~(is_blue (D.oa g) (D.gf g)) /\
                   Seq.mem (D.ob g) (objects zero_addr (D.gf g)) /\ ~(is_blue (D.ob g) (D.gf g)) /\
                   ~(D.since_d g (D.oa g)) /\ ~(D.since_d g (D.ob g)) /\
                   (GC_.unreachable_covered (D.h g) (D.rs g) (heap_size - 8) <==>
                    LL.blue_covered (D.gf g) (heap_size - 8) \/
                    SPC.new_covered (D.since_d g) (D.gf g) (heap_size - 8)))
  = D.reach_ab g;
    C.ccycle_correct (run_carried g)
