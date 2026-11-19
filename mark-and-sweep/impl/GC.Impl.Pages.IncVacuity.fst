/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.IncVacuity - the Pulse code of incremental mode: its
/// preconditions hold mid-sweep
/// ---------------------------------------------------------------------------
///
/// Plan §28.  At the mixed mid-sweep state of `GC.Spec.Pages.IncrVacuity`
/// (A's page swept, B's run not), the facts the Pulse code asks hold: the
/// allocator's (`AllocInc.alloc_ph`: the phase's invariant, and so
/// `Ready.heads_ready`) and the sweep's (`SweepInc.sweep_unit`,
/// `sweep_slice`: `map_ok`).  The allocation there succeeds
/// (`IncrVacuity.alloc_mixed`); its tag-0 form is the untagged allocator
/// (`AllocInc.alloc_tag_zero`, which has no hypothesis).

module GC.Impl.Pages.IncVacuity

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module I = GC.Spec.AllocIface
module MS = GC.Spec.Pages.MidSweep
module V = GC.Spec.Pages.Cycle.Vacuity
module D = GC.Spec.Pages.Cycle.VacuityDark
module IV = GC.Spec.Pages.IncrVacuity
module Inc = GC.Spec.Pages.Incr
module Rd = GC.Impl.Pages.Ready
module AI = GC.Impl.Pages.AllocInc

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let pulse_pre_mixed (g: heap)
  : Lemma (requires V.roomy)
          (ensures Inc.phase_inv I.Sweeping (D.g1 g) (D.s1 g) /\ Rd.heads_ready (D.s1 g) /\
                   map_ok (D.s1 g).pm /\
                   (entry (D.s1 g).pm (D.jc g)).swept /\ not (entry (D.s1 g).pm (V.i0 g)).swept)
  = IV.mixed_state g;
    AI.phase_ready I.Sweeping (D.g1 g) (D.s1 g);
    MS.pages_ok_sw_elim (D.g1 g) (D.s1 g)
