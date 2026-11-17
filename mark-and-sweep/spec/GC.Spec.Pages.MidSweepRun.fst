/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.MidSweepRun - allocations and sweep steps, in any order
/// ---------------------------------------------------------------------------
///
/// Plan §20.4.  `sw_run g st` is a run of an incremental sweep with the page
/// allocator: it starts where the mark leaves the heap (`sweep_ready`,
/// `mark_done`), then takes, in any order, allocations through the
/// interface in `Sweeping` (with the caller's writes to the new object's
/// fields) and sweep steps (`SweepAll.step`, a pool page or a run).
///
///   - **`sw_run_inv`**: every state of a run is in the mid-sweep invariant.
///   - **`sw_run_ends`**: from every state of a run, the rest of the sweep
///     ends in the `Idle` invariant.
///
/// **Vacuity** (plan §18): `sw_witness` is a run from the sweep's start of
/// the shared witness `W`'s mark: the pool page of the dead object C is
/// swept; then, with that page swept and B's run still unswept, an
/// allocation succeeds and its field is written; then B's run is swept.

module GC.Spec.Pages.MidSweepRun

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
open GC.Spec.Pages.MidSweep

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module SA = GC.Spec.Pages.SweepAll
module SS = GC.Spec.Pages.SweepStep
module SP = GC.Spec.Pages.SweepPage
module MA = GC.Spec.Pages.MidSweepAlloc
module MS = GC.Spec.Pages.MidSweepStep
module Th = GC.Spec.Pages.Theorems

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Runs
/// ---------------------------------------------------------------------------

/// One allocation through the interface in `Sweeping`, then the caller's
/// writes to the new object's fields, with values that are not free
/// mid-sweep; nothing on failure.
let sw_allocated (g: heap) (st: pstate) (wz: nat) (g'': heap) : prop =
  let (g', _, o) = PA.alloc I.Sweeping g st wz in
  (o == 0UL /\ g'' == g') \/
  (o =!= 0UL /\ U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
   I.fields_written_with (free_sw st.pm) g' g'' (o <: obj_addr))

let sw_alloc_state (g: heap) (st: pstate) (wz: nat) : GTot pstate =
  let (_, s, _) = PA.alloc I.Sweeping g st wz in s

noeq type sw_run : heap -> pstate -> Type =
  | SwStart : g:heap -> st:pstate -> squash (SA.sweep_ready g st /\ SA.mark_done g) -> sw_run g st
  | SwAlloc : #g:heap -> #st:pstate -> sw_run g st -> wz:nat -> g'':heap ->
              squash (sw_allocated g st wz g'') -> sw_run g'' (sw_alloc_state g st wz)
  | SwStep : #g:heap -> #st:pstate -> sw_run g st -> p:nat{p < n_pages} ->
             sw_run (fst (SA.step g st p)) (snd (SA.step g st p))

let alloc_keeps_sw (g: heap) (st: pstate) (wz: nat) (g'': heap)
  : Lemma (requires pages_ok_sw g st /\ sw_allocated g st wz g'')
          (ensures pages_ok_sw g'' (sw_alloc_state g st wz))
  = MA.alloc_sw_ok g st wz

let step_keeps_sw (g: heap) (st: pstate) (p: nat{p < n_pages})
  : Lemma (requires pages_ok_sw g st)
          (ensures pages_ok_sw (fst (SA.step g st p)) (snd (SA.step g st p)))
  = MS.step_sw g st p

/// **Every state of a run is in the mid-sweep invariant.**
let rec sw_run_inv (#g: heap) (#st: pstate) (r: sw_run g st)
  : Lemma (ensures pages_ok_sw g st) (decreases r)
  = match r with
    | SwStart g0 st0 _ -> MS.sw_start g0 st0
    | SwAlloc #g1 #st1 r1 wz g'' _ -> sw_run_inv r1; alloc_keeps_sw g1 st1 wz g''
    | SwStep #g1 #st1 r1 p -> sw_run_inv r1; step_keeps_sw g1 st1 p

/// **The sweep still ends**: from every state of a run, sweeping the rest
/// gives the `Idle` invariant.
let sw_run_ends (#g: heap) (#st: pstate) (r: sw_run g st)
  : Lemma (ensures (let (g', st') = SA.sweep_all g st in PA.inv I.Idle g' st'))
  = sw_run_inv r;
    MS.sweep_rest g st
