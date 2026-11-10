/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Vacuity - the new lemmas' hypotheses can hold
/// ---------------------------------------------------------------------------
///
/// The Pulse page allocator's functions have hypotheses-free or small
/// preconditions; the lemmas behind them have `requires` clauses.  For each
/// such clause this module either shows a state that satisfies it, or
/// checks that the solver cannot refute it (`expect_failure`), as the
/// specification's vacuity checks do.
///
///   - The run sweep's invariant `emit_ok` holds at its start (`emit_start`),
///     and so does the map's, `map_in` and `pass2`.
///   - The first-fit invariant `fit_inv_ex` holds at its start.
///   - `sweep_all`'s precondition `map_ok` holds of the empty heap of pages.
///   - The hypotheses of the step lemmas are not refutable.

module GC.Impl.Pages.Vacuity

open GC.Spec.Base
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Blk
open GC.Spec.Pages.RunList

module U64 = FStar.UInt64
module L = FStar.List.Tot
module SO = GC.Spec.Object
module Sh = GC.Spec.Pages.Shape
module SR = GC.Spec.Pages.SweepRun
module RM = GC.Spec.Pages.RunMap
module Init = GC.Spec.Pages.Init
module RL = GC.Impl.Pages.RunLemmas
module RML = GC.Impl.Pages.RunMapLemmas
module LI = GC.Impl.Pages.Large

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The invariants hold where the loops start
/// ---------------------------------------------------------------------------

let emit_ok_start (g: heap) (h: nat)
  : Lemma (RL.emit_ok g g [] (page_base h) (page_base h) 0UL 0UL)
  = page_base_aligned h;
    RL.emit_start g (page_base h)

let map_start (st: pstate) (fs: list blk) (h n: nat)
  : Lemma (RML.map_in st st [] /\ (RML.map_in st st fs ==> RML.pass2 st st st fs h n h))
  = RML.map_in_start st;
    if FStar.IndefiniteDescription.strong_excluded_middle (RML.map_in st st fs)
    then RML.pass2_start st st fs h n

let fit_start (g: heap) (fp: U64.t) (w: nat)
  : Lemma (LI.fit_inv_ex g fp w 0UL fp heap_words)
  = LI.fit_start_ex g fp w

/// `sweep_all` and `sweep` ask for `map_ok`; the empty heap of pages has it.
let sweep_pre_holds () : Lemma (map_ok Init.init_state.pm)
  = all_free_ok ()

/// ---------------------------------------------------------------------------
/// The step lemmas' hypotheses are not refutable
/// ---------------------------------------------------------------------------

[@@expect_failure [19]]
let emit_plain_hyps (g0 g: heap) (bs: list blk) (s a: nat) (first pend: U64.t) (b: blk)
  : Lemma (requires RL.emit_ok g0 g bs s a first pend /\ b.at == a /\ not (SR.listable b))
          (ensures False)
  = ()

[@@expect_failure [19]]
let emit_listed_hyps (g0 g: heap) (bs: list blk) (s a: nat) (first pend: U64.t) (b: blk)
  : Lemma (requires RL.emit_ok g0 g bs s a first pend /\ b.at == a /\ SR.listable b)
          (ensures False)
  = ()

[@@expect_failure [19]]
let fin_dead_hyps (g: heap) (a e: nat)
  : Lemma (requires RL.fits g a e /\ Sh.color_at g a <> GC.Lib.Header.Black) (ensures False)
  = ()

[@@expect_failure [19]]
let fin_live_hyps (g: heap) (a e: nat)
  : Lemma (requires RL.fits g a e /\ Sh.color_at g a == GC.Lib.Header.Black) (ensures False)
  = ()

[@@expect_failure [19]]
let run_pages_hyps (pm: page_map) (h: nat{h < n_pages}) (n: pos)
  : Lemma (requires RML.run_pages pm h n) (ensures False)
  = ()

[@@expect_failure [19]]
let pass2_head_hyps (st0 st1 st: pstate) (fs: list blk) (h: nat{h < n_pages}) (n: pos) (jj: nat{jj < n_pages})
  : Lemma (requires RML.pass2 st0 st1 st fs h n jj /\ RML.map_in st0 st1 fs /\ RML.run_pages st0.pm h n /\
                    h <= jj /\ jj < h + n /\ not (RM.freed fs jj) /\ (jj = h \/ RM.freed fs (jj - 1)))
          (ensures False)
  = ()

[@@expect_failure [19]]
let pass2_cont_hyps (st0 st1 st: pstate) (fs: list blk) (h: nat{h < n_pages}) (n: pos) (jj: nat{jj < n_pages})
  : Lemma (requires RML.pass2 st0 st1 st fs h n jj /\ RML.map_in st0 st1 fs /\ RML.run_pages st0.pm h n /\
                    h < jj /\ jj < h + n /\ not (RM.freed fs jj) /\ not (RM.freed fs (jj - 1)))
          (ensures False)
  = ()

[@@expect_failure [19]]
let pass2_done_hyps (st0 st1 st: pstate) (fs: list blk) (h: nat{h < n_pages}) (n: pos) (a: nat)
  : Lemma (requires RML.pass2 st0 st1 st fs h n (h + n) /\ RML.map_in st0 st1 fs /\
                    contig fs (page_base h) a /\ a <= page_base (h + n))
          (ensures False)
  = ()

[@@expect_failure [19]]
let fit_found_hyps (g: heap) (fp: U64.t) (w: nat) (prev cur: U64.t) (n: nat)
  : Lemma (requires LI.fit_inv_ex g fp w prev cur n /\ n > 0 /\ GC.Spec.Pages.Cells.node cur /\
                    SO.whsize g cur >= w)
          (ensures False)
  = ()
