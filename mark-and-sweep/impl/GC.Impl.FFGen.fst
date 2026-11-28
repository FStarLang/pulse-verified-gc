/// ---------------------------------------------------------------------------
/// GC.Impl.FFGen - the first-fit generational code, event by event, as runs
/// of the top-level specification
/// ---------------------------------------------------------------------------
///
/// Design doc §18, plan step 1 (first-fit mark and barrier).  The code is
/// akhil's generational collector (`GC.Gen.Impl.gen_heap_t`: the nursery,
/// the major heap, the free list's head, the phase record and the mark
/// state) with the remembered set as a table of slot addresses.
/// `crepg c sty es`: akhil's state at the configuration of the first-fit
/// collector `CodeFF.fc` after the events `es`, a run of style `sty`:
///   - `is_gen_heap`: the nursery is the configuration's, the major heap and
///     the free list's head are its;
///   - `gen_phase`: the phase record holds the configuration's phase, its
///     sweep caches derived from the heap;
///   - `mark_state`: akhil's mark cache (stack, overflow flag, the partly
///     scanned object and its next field, the rescan cursor) is sound for
///     the heap at the phase, at the model's scan (`CodeFFGen.spof`);
///   - the table: the remembered slots' addresses, with repeats
///     (`CodeFFGlue.tbl_e`, as C's table), every remembered slot a
///     scannable field of a kept block (`CodeFFMinor.rem_ok`).
/// Not akhil's `gc_state`: its `phase_shape` asks the nursery's shape
/// (`minor_guards_complete`, `minor_infix_wf`), which the model's runs do
/// not give.  The mark slice and the barrier are called through entry
/// points that take the major heap and the mark state only; the start
/// rebuilds `gc_state` with the nursery empty.
///
/// The wrappers, each ensuring the representation of the run one event
/// longer:
///   - `initg`: the start, an empty nursery and table, the mark state off;
///   - `allocg`: `EAlloc`, akhil's first-fit allocation at the phase, the
///     Fill, its young fields appended to the table;
///   - `yallocg`: `EYoungAlloc`, a bump allocation in the nursery;
///   - `writeg`: `EWrite` into a major block, akhil's barrier as he builds
///     it (`GC.Gen.Impl.Barrier.modify_at`): while marking a scannable
///     block, the old value darkened (`MarkBounded.check_and_darken_bounded`,
///     the overflow flag raised when the stack is full), then the store; the
///     slot appended to the table when akhil's barrier says to remember it;
///   - `ywriteg`: `EWrite` into a young block, the nursery word stored;
///   - `sliceg`: akhil's mark slice (`MarkSlice.mark_slice`) as one
///     `ESlice` of its moves (none when it made no move), then `EHandover`
///     when the slice reports marking over (the cache is empty only then);
///   - `sweepg`: a slice of akhil's fused sweep as `ESweep` events, then
///     `EEnd`;
///   - `rootsg`, `readg` (a major or a young block): the program's root events, ghost;
///   - `minorg`: `EMinor`, akhil's `minor_collect_with` on the program's
///     young roots then the table's young words, the table emptied;
///   - `startg`: `EMinor`, then `EStart`: akhil's `start_cycle` on the
///     rewritten young roots and the caller's major roots.
/// `minorg` and `startg` take akhil's nursery conditions
/// (`minor_guards_complete`, `minor_infix_wf`) as a trusted precondition of
/// the caller (design doc §18.5); when akhil's collection reports a failed
/// promotion the run ends with no event (`stoppedg`, §18.11).  `allocg` and
/// `writeg` do nothing when the table is full (results 1 and false).

module GC.Impl.FFGen

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Impl.Heap
open GC.Impl.Stack
open GC.Spec.Top.Run

module U64 = FStar.UInt64
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module L = FStar.List.Tot
module SB = GC.Spec.Base
module SO = GC.Spec.Object
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module W = GC.Spec.Top.Word
module Abs = GC.Spec.Top.Abs
module BF = GC.Spec.Top.ByteFacts
module FAl = GC.Spec.Top.FFAlloc
module CF = GC.Spec.Top.CodeFF
module CR = GC.Spec.Top.CodeRun
module CM = GC.Spec.Top.CodeMinor
module FG = GC.Spec.Top.CodeFFGen
module FMi = GC.Spec.Top.CodeFFMinor
module FMk = GC.Spec.Top.CodeFFMark
module FWr = GC.Spec.Top.CodeFFWrite
module Dup = GC.Spec.Top.CodeFFDup
module Gl = GC.Spec.Top.CodeFFGlue
module Ph = GC.Spec.Phase
module MP = GC.Spec.MarkPhase
module MS = GC.Gen.MarkState
module SPI = GC.Spec.SweepPhase.Intrinsic
module SL = GC.Spec.SweepPhase.Slice
module FS = GC.Spec.FusedSweep
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module AI = GC.Impl.Allocator
module FSC = GC.Impl.FusedSweepCoalesce
module GI = GC.Gen.Impl
module MSI = GC.Gen.Impl.MarkSlice
module MB = GC.Impl.MarkBounded
module GBr = GC.Gen.Barrier
module Obj = GC.Impl.Object
module Hdr = GC.Lib.Header
module PT = GC.Impl.Pages.Top
module FT = GC.Impl.FFTop
module TM = GC.Impl.Pages.TopMinor
module Fw = GC.Impl.Pages.Forward
module Y = GC.Spec.Top.Young

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The representation
/// ---------------------------------------------------------------------------

/// The code's state: akhil's record, and the table with its capacity and
/// length.
noeq type gcs = {
  gh: GI.gen_heap_t;
  tb: A.array U64.t;
  tcap: SZ.t;
  tn: R.ref SZ.t;
}

/// What the nursery and the table keep of the configuration.
let side (es: list event) (d: minor_heap) (b: U64.t) (tv: Seq.seq U64.t) (n: nat) : prop =
  let x = CF.xc es in
  Fw.mst d b == x.w.cyng /\ Gl.tbl_e tv n x.w.crem /\ FMi.rem_ok x

/// **The code's state represents the configuration after `es`.**
let crepg (c: gcs) (sty: style) (es: list event) : slprop =
  exists* (d: minor_heap) (b: U64.t) (tv: Seq.seq U64.t) (n: SZ.t).
    GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp **
    GI.gen_phase c.gh (CF.hof (CF.xc es)) (FAl.gph (CF.xc es).ph) **
    GI.mark_state c.gh (CF.hof (CF.xc es)) (FAl.gph (CF.xc es).ph) (FG.spof (scan_of (CF.xc es))) **
    A.pts_to c.tb tv ** R.pts_to c.tn n **
    pure (CF.good sty es /\ side es d b tv (SZ.v n) /\ Seq.length tv == SZ.v c.tcap)

/// ---------------------------------------------------------------------------
/// The mark state across a change
/// ---------------------------------------------------------------------------

/// Outside marking the mark state says nothing of the heap or the phase.
ghost fn ms_off (gh: GI.gen_heap_t) (g g': SB.heap) (ph ph': Ph.gc_phase) (sp: MP.scan_pos)
  requires GI.mark_state gh g ph sp ** pure (~(Ph.Marking? ph) /\ ~(Ph.Marking? ph'))
  ensures GI.mark_state gh g' ph' sp
{
  unfold GI.mark_state;
  with st ov c f r mw. assert (is_gray_stack gh.mark_stack st ** R.pts_to gh.mark_overflow ov **
    R.pts_to gh.mark_cur c ** R.pts_to gh.mark_field f ** R.pts_to gh.mark_rescan r ** R.pts_to gh.mark_words mw);
  MS.mark_cache_off g g' ph ph' st ov (MSI.pos c f r);
  fold (GI.mark_state gh g' ph' sp)
}

/// The same heap, phase and position, under other names.
ghost fn ms_eq (gh: GI.gen_heap_t) (g g': SB.heap) (ph ph': Ph.gc_phase) (sp sp': MP.scan_pos)
  requires GI.mark_state gh g ph sp ** pure (g == g' /\ ph == ph' /\ sp == sp')
  ensures GI.mark_state gh g' ph' sp'
{
  rewrite (GI.mark_state gh g ph sp) as (GI.mark_state gh g' ph' sp')
}

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

/// **The start**: a zeroed major heap, then the model's initial heap (as
/// `FFTop.initf`), the nursery and the table emptied; the mark state, set up
/// off by the caller (stack empty, flag down, no position), stays off.
fn initg (c: gcs) (sty: erased style)
  requires GI.is_gen_heap c.gh 'd 'b 'g 'f0 ** R.pts_to c.gh.GI.phase_ref 'v0 **
           GI.mark_state c.gh 'g Ph.Idle MP.scan_none ** A.pts_to c.tb 'tv ** R.pts_to c.tn 'n **
           pure (Seq.length 'tv == SZ.v c.tcap)
  ensures crepg c sty []
{
  unfold GI.is_gen_heap;
  FT.initf c.gh.GI.major c.gh.GI.fp_ref c.gh.GI.phase_ref sty;
  unfold FT.crepf;
  with x v. assert (is_heap c.gh.GI.major (CF.hof x) ** R.pts_to c.gh.GI.phase_ref v);
  Gl.init_g sty;
  minor_heap_reset c.gh.GI.minor;
  c.tn := 0sz;
  Gl.tbl_e_nil 'tv;
  rewrite (is_heap c.gh.GI.major (CF.hof x)) as (is_heap c.gh.GI.major (CF.hof (CF.xc [])));
  rewrite (R.pts_to c.gh.GI.fp_ref (CF.sof x).FAl.fp) as (R.pts_to c.gh.GI.fp_ref (CF.sof (CF.xc [])).FAl.fp);
  fold (GI.is_gen_heap c.gh (Seq.create minor_heap_size 0uy) 0UL (CF.hof (CF.xc [])) (CF.sof (CF.xc [])).FAl.fp);
  fold (AI.is_phase c.gh.GI.phase_ref (CF.hof (CF.xc [])) (FAl.gph (CF.xc []).ph));
  fold (GI.gen_phase c.gh (CF.hof (CF.xc [])) (FAl.gph (CF.xc []).ph));
  ms_off c.gh 'g (CF.hof (CF.xc [])) Ph.Idle (FAl.gph (CF.xc []).ph) MP.scan_none;
  ms_eq c.gh (CF.hof (CF.xc [])) (CF.hof (CF.xc [])) (FAl.gph (CF.xc []).ph) (FAl.gph (CF.xc []).ph)
    MP.scan_none (FG.spof (scan_of (CF.xc [])));
  fold (crepg c sty [])
}

/// ---------------------------------------------------------------------------
/// The program's root events (ghost)
/// ---------------------------------------------------------------------------

/// The configuration's parts the representation reads, unchanged.
ghost fn same_cfg (c: gcs) (sty: style) (es es': list event)
  requires crepg c sty es **
           pure (CF.good sty es' /\
                 (let x = CF.xc es in let x' = CF.xc es' in
                  CF.hof x' == CF.hof x /\ CF.sof x' == CF.sof x /\ x'.ph == x.ph /\ x'.ms == x.ms /\
                  x'.w.cyng == x.w.cyng /\ x'.w.crem == x.w.crem /\ FMi.rem_ok x'))
  ensures crepg c sty es'
{
  unfold crepg;
  with d b tv n. assert (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  rewrite (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp)
       as (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es')) (CF.sof (CF.xc es')).FAl.fp);
  rewrite (GI.gen_phase c.gh (CF.hof (CF.xc es)) (FAl.gph (CF.xc es).ph))
       as (GI.gen_phase c.gh (CF.hof (CF.xc es')) (FAl.gph (CF.xc es').ph));
  rewrite (GI.mark_state c.gh (CF.hof (CF.xc es)) (FAl.gph (CF.xc es).ph) (FG.spof (scan_of (CF.xc es))))
       as (GI.mark_state c.gh (CF.hof (CF.xc es')) (FAl.gph (CF.xc es').ph) (FG.spof (scan_of (CF.xc es'))));
  fold (crepg c sty es')
}

/// **`ERoots`**: the program's roots, replaced.
ghost fn rootsg (c: gcs) (#sty: erased style) (#es: erased (list event)) (rs: list M.value)
  requires crepg c sty es ** pure (CR.allowed CF.fc sty (CF.xc es) (ERoots rs))
  ensures crepg c sty (L.append es [ERoots rs])
{
  unfold crepg;
  with d b tv n. assert (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  fold (crepg c sty es);
  Gl.roots_g sty es (ERoots rs);
  same_cfg c sty es (L.append es [ERoots rs])
}

/// **`ERead`** of a field into a new root, from a major or a young block.
ghost fn readg (c: gcs) (#sty: erased style) (#es: erased (list event)) (p: M.ptr) (i: nat)
  requires crepg c sty es ** pure (CR.allowed CF.fc sty (CF.xc es) (ERead p i))
  ensures crepg c sty (L.append es [ERead p i])
{
  unfold crepg;
  with d b tv n. assert (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  fold (crepg c sty es);
  Gl.roots_g sty es (ERead p i);
  same_cfg c sty es (L.append es [ERead p i])
}

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

/// **A slice of the sweep**: akhil's `sweep_slice_impl` from the record's
/// cursor and caches (as `FFTop.slicef`), as `k` events `ESweep`; when the
/// cursor reaches the end, `EEnd` too, and the result is true.  The
/// nursery, the table and the mark state (off) stay.
#push-options "--z3rlimit 40"
fn sweepg (c: gcs) (budget: U64.t) (#sty: erased style) (#es: erased (list event))
  requires crepg c sty es ** pure (T.Sweeping? (CF.xc es).ph)
  returns fin: bool
  ensures crepg c sty (if fin then L.append (FT.slice_evs es (U64.v budget)) [EEnd] else FT.slice_evs es (U64.v budget))
{
  unfold crepg;
  with d b tv n. assert (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  unfold GI.is_gen_heap;
  unfold GI.gen_phase;
  unfold AI.is_phase;
  with v. assert (R.pts_to c.gh.GI.phase_ref v);
  CF.good_inv sty es;
  CF.slice_cfg sty es (U64.v budget);
  Gl.slice_side sty es (U64.v budget);
  let pv = !c.gh.GI.phase_ref;
  let fp = !c.gh.GI.fp_ref;
  FT.rec_link (CF.hof (CF.xc es)) pv (T.Sweeping?._0 (CF.xc es).ph);
  let r = FSC.sweep_slice_impl c.gh.GI.major pv.AI.ps_cursor pv.AI.ps_swept_tail pv.AI.ps_last_fragment fp budget;
  let c' = Mktuple4?._1 r;
  let t' = Mktuple4?._2 r;
  let f' = Mktuple4?._3 r;
  let fp' = Mktuple4?._4 r;
  with g'. assert (is_heap c.gh.GI.major g');
  assert (pure (U64.v c' <= SB.heap_size));
  FT.hs_small ();
  c.gh.GI.fp_ref := fp';
  if (U64.gte (U64.add c' 8UL) heap_size_u64) {
    CF.end_cfg sty (FT.slice_evs es (U64.v budget));
    Gl.end_side sty (FT.slice_evs es (U64.v budget));
    c.gh.GI.phase_ref := { AI.ps_kind = 0UL; AI.ps_cursor = c'; AI.ps_swept_tail = t'; AI.ps_last_fragment = f' };
    rewrite (is_heap c.gh.GI.major g')
         as (is_heap c.gh.GI.major (CF.hof (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd]))));
    rewrite (R.pts_to c.gh.GI.fp_ref fp')
         as (R.pts_to c.gh.GI.fp_ref (CF.sof (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd]))).FAl.fp);
    fold (AI.is_phase c.gh.GI.phase_ref (CF.hof (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd])))
            (FAl.gph (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd])).ph));
    fold (GI.gen_phase c.gh (CF.hof (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd])))
            (FAl.gph (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd])).ph));
    fold (GI.is_gen_heap c.gh d b (CF.hof (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd])))
            (CF.sof (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd]))).FAl.fp);
    ms_off c.gh (CF.hof (CF.xc es)) (CF.hof (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd])))
      (FAl.gph (CF.xc es).ph) (FAl.gph (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd])).ph)
      (FG.spof (scan_of (CF.xc es)));
    ms_eq c.gh (CF.hof (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd])))
      (CF.hof (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd])))
      (FAl.gph (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd])).ph)
      (FAl.gph (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd])).ph)
      (FG.spof (scan_of (CF.xc es))) (FG.spof (scan_of (CF.xc (L.append (FT.slice_evs es (U64.v budget)) [EEnd]))));
    fold (crepg c sty (L.append (FT.slice_evs es (U64.v budget)) [EEnd]));
    true
  } else {
    c.gh.GI.phase_ref := { AI.ps_kind = 1UL; AI.ps_cursor = c'; AI.ps_swept_tail = t'; AI.ps_last_fragment = f' };
    rewrite (is_heap c.gh.GI.major g') as (is_heap c.gh.GI.major (CF.hof (CF.xc (FT.slice_evs es (U64.v budget)))));
    rewrite (R.pts_to c.gh.GI.fp_ref fp')
         as (R.pts_to c.gh.GI.fp_ref (CF.sof (CF.xc (FT.slice_evs es (U64.v budget)))).FAl.fp);
    fold (AI.is_phase c.gh.GI.phase_ref (CF.hof (CF.xc (FT.slice_evs es (U64.v budget))))
            (FAl.gph (CF.xc (FT.slice_evs es (U64.v budget))).ph));
    fold (GI.gen_phase c.gh (CF.hof (CF.xc (FT.slice_evs es (U64.v budget))))
            (FAl.gph (CF.xc (FT.slice_evs es (U64.v budget))).ph));
    fold (GI.is_gen_heap c.gh d b (CF.hof (CF.xc (FT.slice_evs es (U64.v budget))))
            (CF.sof (CF.xc (FT.slice_evs es (U64.v budget)))).FAl.fp);
    ms_off c.gh (CF.hof (CF.xc es)) (CF.hof (CF.xc (FT.slice_evs es (U64.v budget))))
      (FAl.gph (CF.xc es).ph) (FAl.gph (CF.xc (FT.slice_evs es (U64.v budget))).ph)
      (FG.spof (scan_of (CF.xc es)));
    ms_eq c.gh (CF.hof (CF.xc (FT.slice_evs es (U64.v budget)))) (CF.hof (CF.xc (FT.slice_evs es (U64.v budget))))
      (FAl.gph (CF.xc (FT.slice_evs es (U64.v budget))).ph) (FAl.gph (CF.xc (FT.slice_evs es (U64.v budget))).ph)
      (FG.spof (scan_of (CF.xc es))) (FG.spof (scan_of (CF.xc (FT.slice_evs es (U64.v budget)))));
    fold (crepg c sty (FT.slice_evs es (U64.v budget)));
    false
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// The mark slice
/// ---------------------------------------------------------------------------

/// The events of a slice that left the heap `g2` at the position `sp2`
/// (`ESlice` of its moves, none when it made no move), then, when it ended
/// marking, the hand-over.
let slice_es (es: list event) (g2: SB.heap) (sp2: MP.scan_pos) (fin: bool) : GTot (list event) =
  if fin then L.append (Gl.slice1 es g2 sp2) [EHandover] else Gl.slice1 es g2 sp2

/// While marking the phase record holds `Marking` whatever the heap.
ghost fn phase_marking (r: R.ref AI.phase_state) (g g': SB.heap)
  requires AI.is_phase r g Ph.Marking
  ensures AI.is_phase r g' Ph.Marking
{
  unfold AI.is_phase;
  fold (AI.is_phase r g' Ph.Marking)
}

/// **A mark slice**: akhil's `mark_slice` with the budget, as the event
/// `ESlice` of the moves it made (none when it made none); when it reports
/// marking over (nothing grey, the cache empty), the hand-over to the sweep
/// (`EHandover`, the record at the sweep's start), and the result is true.
#push-options "--z3rlimit 40"
fn sliceg (c: gcs) (budget: U64.t) (#sty: erased style) (#es: erased (list event))
  requires crepg c sty es ** pure (T.Marking? (CF.xc es).ph)
  returns fin: bool
  ensures exists* (g2: SB.heap) (sp2: MP.scan_pos). crepg c sty (slice_es es g2 sp2 fin)
{
  unfold crepg;
  with d b tv n. assert (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  unfold GI.mark_state;
  with st ov cc f r mw. assert (is_gray_stack c.gh.GI.mark_stack st ** R.pts_to c.gh.GI.mark_overflow ov **
    R.pts_to c.gh.GI.mark_cur cc ** R.pts_to c.gh.GI.mark_field f ** R.pts_to c.gh.GI.mark_rescan r **
    R.pts_to c.gh.GI.mark_words mw);
  FMk.slice_heap sty es;
  FMk.cache_marking (CF.hof (CF.xc es)) st ov (MSI.pos cc f r);
  unfold GI.is_gen_heap;
  let fin = MSI.mark_slice c.gh.GI.major c.gh.GI.mark_stack c.gh.GI.mark_overflow
              c.gh.GI.mark_cur c.gh.GI.mark_field c.gh.GI.mark_rescan c.gh.GI.mark_words budget;
  with s2 st2 ov2 c2 f2 r2 m2. assert (is_heap c.gh.GI.major s2 ** is_gray_stack c.gh.GI.mark_stack st2 **
    R.pts_to c.gh.GI.mark_overflow ov2 ** R.pts_to c.gh.GI.mark_cur c2 ** R.pts_to c.gh.GI.mark_field f2 **
    R.pts_to c.gh.GI.mark_rescan r2 ** R.pts_to c.gh.GI.mark_words m2);
  Gl.slice_g sty es s2 (MS.scan_of (MSI.pos c2 f2 r2));
  FMk.cache_marking s2 st2 ov2 (MSI.pos c2 f2 r2);
  unfold GI.gen_phase;
  if fin {
    Gl.handover_g sty (Gl.slice1 es s2 (MS.scan_of (MSI.pos c2 f2 r2))) st2 ov2 (MSI.pos c2 f2 r2);
    FT.reaches_self s2 SB.zero_addr;
    unfold AI.is_phase;
    c.gh.GI.phase_ref := { AI.ps_kind = 1UL; AI.ps_cursor = SB.zero_addr; AI.ps_swept_tail = 0UL; AI.ps_last_fragment = 0UL };
    rewrite (is_heap c.gh.GI.major s2)
         as (is_heap c.gh.GI.major (CF.hof (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) true))));
    rewrite (R.pts_to c.gh.GI.fp_ref (CF.sof (CF.xc es)).FAl.fp)
         as (R.pts_to c.gh.GI.fp_ref (CF.sof (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) true))).FAl.fp);
    fold (AI.is_phase c.gh.GI.phase_ref (CF.hof (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) true)))
            (FAl.gph (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) true)).ph));
    fold (GI.gen_phase c.gh (CF.hof (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) true)))
            (FAl.gph (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) true)).ph));
    fold (GI.is_gen_heap c.gh d b (CF.hof (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) true)))
            (CF.sof (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) true))).FAl.fp);
    fold (GI.mark_state c.gh (CF.hof (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) true)))
            (FAl.gph (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) true)).ph)
            (FG.spof (scan_of (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) true)))));
    fold (crepg c sty (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) true));
    true
  } else {
    rewrite (AI.is_phase c.gh.GI.phase_ref (CF.hof (CF.xc es)) (FAl.gph (CF.xc es).ph))
         as (AI.is_phase c.gh.GI.phase_ref (CF.hof (CF.xc es)) Ph.Marking);
    phase_marking c.gh.GI.phase_ref (CF.hof (CF.xc es)) s2;
    rewrite (AI.is_phase c.gh.GI.phase_ref s2 Ph.Marking)
         as (AI.is_phase c.gh.GI.phase_ref (CF.hof (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) false)))
               (FAl.gph (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) false)).ph));
    rewrite (is_heap c.gh.GI.major s2)
         as (is_heap c.gh.GI.major (CF.hof (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) false))));
    rewrite (R.pts_to c.gh.GI.fp_ref (CF.sof (CF.xc es)).FAl.fp)
         as (R.pts_to c.gh.GI.fp_ref (CF.sof (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) false))).FAl.fp);
    fold (GI.gen_phase c.gh (CF.hof (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) false)))
            (FAl.gph (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) false)).ph));
    fold (GI.is_gen_heap c.gh d b (CF.hof (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) false)))
            (CF.sof (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) false))).FAl.fp);
    fold (GI.mark_state c.gh (CF.hof (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) false)))
            (FAl.gph (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) false)).ph)
            (FG.spof (scan_of (CF.xc (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) false)))));
    fold (crepg c sty (slice_es es s2 (MS.scan_of (MSI.pos c2 f2 r2)) false));
    false
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Allocation, its Fill, and the table
/// ---------------------------------------------------------------------------

module CP = GC.Spec.Top.CodePages

/// The table's length is within its capacity.
ghost fn tbl_room (c: gcs) (#sty: erased style) (#es: erased (list event))
  requires crepg c sty es
  returns nv: erased SZ.t
  ensures crepg c sty es
{
  unfold crepg;
  with d b tv n. assert (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  fold (crepg c sty es);
  n
}

/// **`EAlloc`**: when the table has room for the block's fields, akhil's
/// first-fit allocation at the phase (as `FFTop.allocf`), the Fill with the
/// words `ws` (the values `vs`), then the Fill's young fields of a
/// scannable block appended to the table, in order; returns the block's
/// first-field address, or 0 when there is no room in the heap (then the
/// configuration does not change).  When the table has no room, nothing is
/// done and the result is 1 (no event; a minor collection empties it).
#push-options "--z3rlimit 40"
fn allocg (c: gcs) (wz: U64.t{U64.v wz >= 1}) (tag: U64.t{U64.v tag < 256}) (fs: A.array U64.t) (#p: perm)
  (#ws: erased (Seq.seq U64.t)) (#sty: erased style) (#es: erased (list event)) (vs: erased (list M.value))
  requires crepg c sty es ** A.pts_to fs #p ws **
           pure (Seq.length ws == U64.v wz /\ L.length vs == U64.v wz /\
                 (forall (i: nat). i < U64.v wz ==> Seq.index ws i == W.concv (L.index vs i)) /\
                 CR.allowed CF.fc sty (CF.xc es) (EAlloc (U64.v wz) (U64.v tag) vs))
  returns o: U64.t
  ensures A.pts_to fs #p ws **
          (if o = 1UL then crepg c sty es else crepg c sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])) **
          pure (o == 0UL ==> CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]) == CF.xc es)
{
  unfold crepg;
  with d b tv n. assert (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  let nv = !c.tn;
  Gl.tbl_e_len tv (SZ.v nv) (CF.xc es).w.crem;
  let wzs = SZ.uint64_to_sizet wz;
  if (SZ.lte wzs (SZ.sub c.tcap nv)) {
    unfold GI.is_gen_heap;
    unfold GI.gen_phase;
    unfold AI.is_phase;
    with v. assert (R.pts_to c.gh.GI.phase_ref v);
    unfold GI.mark_state;
    with st ov cc f r mw. assert (is_gray_stack c.gh.GI.mark_stack st ** R.pts_to c.gh.GI.mark_overflow ov **
      R.pts_to c.gh.GI.mark_cur cc ** R.pts_to c.gh.GI.mark_field f ** R.pts_to c.gh.GI.mark_rescan r **
      R.pts_to c.gh.GI.mark_words mw);
    CF.alloc_ready sty es;
    FT.tg_eq tag;
    FT.alloc_side sty es (U64.v wz) (U64.v tag) vs v;
    Gl.alloc_g sty es (U64.v wz) (U64.v tag) vs ws st ov (MSI.pos cc f r);
    fold (AI.is_phase c.gh.GI.phase_ref (CF.hof (CF.xc es)) (FAl.gph (CF.xc es).ph));
    let o = AI.allocate c.gh.GI.major c.gh.GI.fp_ref c.gh.GI.phase_ref wz tag;
    unfold AI.is_phase;
    with g' v'. assert (is_heap c.gh.GI.major g' ** R.pts_to c.gh.GI.phase_ref v');
    with fp2. assert (R.pts_to c.gh.GI.fp_ref fp2);
    if (o = 0UL) {
      rewrite (is_heap c.gh.GI.major g')
           as (is_heap c.gh.GI.major (CF.hof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]))));
      rewrite (R.pts_to c.gh.GI.fp_ref fp2)
           as (R.pts_to c.gh.GI.fp_ref (CF.sof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]))).FAl.fp);
      fold (AI.is_phase c.gh.GI.phase_ref (CF.hof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])))
              (FAl.gph (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])).ph));
      fold (GI.gen_phase c.gh (CF.hof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])))
              (FAl.gph (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])).ph));
      fold (GI.is_gen_heap c.gh d b (CF.hof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])))
              (CF.sof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]))).FAl.fp);
      fold (GI.mark_state c.gh (CF.hof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])))
              (FAl.gph (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])).ph)
              (FG.spof (scan_of (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])))));
      fold (crepg c sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]));
      rewrite (crepg c sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]))
           as (if 0UL = 1UL then crepg c sty es else crepg c sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]));
      0UL
    } else {
      PT.fill c.gh.GI.major o wz fs (BF.maddr o) vs;
      rewrite (is_heap c.gh.GI.major (CP.fill_from g' (BF.maddr o) 0 vs))
           as (is_heap c.gh.GI.major (CF.hof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]))));
      rewrite (R.pts_to c.gh.GI.fp_ref fp2)
           as (R.pts_to c.gh.GI.fp_ref (CF.sof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]))).FAl.fp);
      fold (AI.is_phase c.gh.GI.phase_ref (CF.hof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])))
              (FAl.gph (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])).ph));
      fold (GI.gen_phase c.gh (CF.hof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])))
              (FAl.gph (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])).ph));
      fold (GI.is_gen_heap c.gh d b (CF.hof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])))
              (CF.sof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]))).FAl.fp);
      fold (GI.mark_state c.gh (CF.hof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])))
              (FAl.gph (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])).ph)
              (FG.spof (scan_of (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs])))));
      let sc = U64.lt tag 251UL;
      let m : erased nat = BF.maddr o;
      assert (pure (Abs.pos m + 8 == U64.v o /\ U64.v o + 8 * U64.v wz <= SB.heap_size));
      Gl.fill_start (CF.xc es).w.crem tv (SZ.v nv) m sc ws;
      let mut k = 0UL;
      while (U64.lt !k wz)
        invariant exists* vk tvk nk.
          R.pts_to k vk ** A.pts_to c.tb tvk ** R.pts_to c.tn nk ** A.pts_to fs #p ws **
          pure (U64.v vk <= U64.v wz /\ Seq.length tvk == SZ.v c.tcap /\
                Abs.pos m + 8 == U64.v o /\ U64.v o + 8 * U64.v wz <= SB.heap_size /\
                SZ.v nk <= SZ.v nv + U64.v vk /\
                Gl.tbl_e tvk (SZ.v nk) (L.append (CF.xc es).w.crem (CM.ypre m sc ws (U64.v vk))))
        decreases (U64.v wz - U64.v !k)
      {
        let vk = !k;
        with tvk nk. assert (A.pts_to c.tb tvk ** R.pts_to c.tn nk);
        let w = fs.(SZ.uint64_to_sizet vk);
        if (sc && TM.young_u64 w) {
          let nk' = !c.tn;
          TM.slot_at o m (U64.v vk) (U64.v wz);
          let a = U64.add o (U64.mul 8UL vk);
          U64.v_inj a (CM.slot_word (reveal m, U64.v vk));
          Gl.fill_step (CF.xc es).w.crem tvk (SZ.v nk') m sc ws (U64.v vk);
          c.tb.(nk') <- a;
          c.tn := SZ.add nk' 1sz;
          k := U64.add vk 1UL
        } else {
          Gl.fill_skip (CF.xc es).w.crem tvk (SZ.v nk) m sc ws (U64.v vk);
          k := U64.add vk 1UL
        }
      };
      with tvk nk. assert (A.pts_to c.tb tvk ** R.pts_to c.tn nk);
      Gl.fill_end (CF.xc es).w.crem tvk (SZ.v nk) m sc ws;
      fold (crepg c sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]));
      rewrite (crepg c sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]))
           as (if o = 1UL then crepg c sty es else crepg c sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]));
      o
    }
  } else {
    fold (crepg c sty es);
    rewrite (crepg c sty es)
         as (if 1UL = 1UL then crepg c sty es else crepg c sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]));
    1UL
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// The nursery's events
/// ---------------------------------------------------------------------------

/// The configuration's major side, unchanged under other names.
ghost fn major_same (c: gcs) (d b: erased _) (es es': list event)
  requires GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp **
           GI.gen_phase c.gh (CF.hof (CF.xc es)) (FAl.gph (CF.xc es).ph) **
           GI.mark_state c.gh (CF.hof (CF.xc es)) (FAl.gph (CF.xc es).ph) (FG.spof (scan_of (CF.xc es))) **
           pure (CF.hof (CF.xc es') == CF.hof (CF.xc es) /\ CF.sof (CF.xc es') == CF.sof (CF.xc es) /\
                 (CF.xc es').ph == (CF.xc es).ph /\ (CF.xc es').ms == (CF.xc es).ms)
  ensures GI.is_gen_heap c.gh d b (CF.hof (CF.xc es')) (CF.sof (CF.xc es')).FAl.fp **
          GI.gen_phase c.gh (CF.hof (CF.xc es')) (FAl.gph (CF.xc es').ph) **
          GI.mark_state c.gh (CF.hof (CF.xc es')) (FAl.gph (CF.xc es').ph) (FG.spof (scan_of (CF.xc es')))
{
  rewrite (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp)
       as (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es')) (CF.sof (CF.xc es')).FAl.fp);
  rewrite (GI.gen_phase c.gh (CF.hof (CF.xc es)) (FAl.gph (CF.xc es).ph))
       as (GI.gen_phase c.gh (CF.hof (CF.xc es')) (FAl.gph (CF.xc es').ph));
  rewrite (GI.mark_state c.gh (CF.hof (CF.xc es)) (FAl.gph (CF.xc es).ph) (FG.spof (scan_of (CF.xc es))))
       as (GI.mark_state c.gh (CF.hof (CF.xc es')) (FAl.gph (CF.xc es').ph) (FG.spof (scan_of (CF.xc es'))))
}

/// **`EYoungAlloc`**: a white header at the bump, the fields after it, the
/// bump past them (as `Pages.TopMinor.yalloc2`).  Returns the object's
/// address, or 0 when the object is too big or the nursery has no room:
/// then no event.
#push-options "--z3rlimit 40"
fn yallocg (c: gcs) (wz: U64.t{U64.v wz >= 1}) (tag: U64.t{U64.v tag < 256}) (fs: A.array U64.t) (#p: perm)
  (#ws: erased (Seq.seq U64.t)) (#sty: erased style) (#es: erased (list event)) (vs: erased (list M.value))
  requires crepg c sty es ** A.pts_to fs #p ws **
           pure (Seq.length ws == U64.v wz /\ L.length vs == U64.v wz /\
                 (forall (i: nat). i < U64.v wz ==> Seq.index ws i == W.concv (L.index vs i)) /\
                 style_ok sty (CF.xc es) (EYoungAlloc (U64.v wz) (U64.v tag) vs) /\
                 mutator_ok (CF.xc es) (EYoungAlloc (U64.v wz) (U64.v tag) vs))
  returns o: U64.t
  ensures A.pts_to fs #p ws **
          (if o = 0UL then crepg c sty es else crepg c sty (L.append es [EYoungAlloc (U64.v wz) (U64.v tag) vs]))
{
  unfold crepg;
  with d b tv n. assert (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  unfold GI.is_gen_heap;
  unfold is_minor;
  let bv = !c.gh.GI.minor.bump_ref;
  fold (is_minor c.gh.GI.minor d b);
  if (U64.lte wz max_young_wosize_u64) {
  TM.room_arith bv wz;
  if (U64.lte (U64.add bv (U64.mul 8UL (U64.add wz 1UL))) minor_heap_size_u64) {
    Y.msz ();
    TM.hdr_eq wz tag;
    let hdr = Obj.makeHeader wz Hdr.White tag;
    TM.mwrite_eq d bv hdr;
    minor_write c.gh.GI.minor bv hdr;
    TM.yfill c.gh.GI.minor bv wz fs vs;
    with dk. assert (is_minor c.gh.GI.minor dk b);
    let b2 = U64.add bv (U64.mul 8UL (U64.add wz 1UL));
    TM.bump_next bv wz;
    unfold is_minor;
    c.gh.GI.minor.bump_ref := b2;
    fold (is_minor c.gh.GI.minor dk b2);
    Gl.yalloc_g sty es (U64.v wz) (U64.v tag) vs;
    fold (GI.is_gen_heap c.gh dk b2 (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp);
    major_same c dk b2 es (L.append es [EYoungAlloc (U64.v wz) (U64.v tag) vs]);
    fold (crepg c sty (L.append es [EYoungAlloc (U64.v wz) (U64.v tag) vs]));
    let o = U64.add bv 8UL;
    rewrite (crepg c sty (L.append es [EYoungAlloc (U64.v wz) (U64.v tag) vs]))
         as (if o = 0UL then crepg c sty es else crepg c sty (L.append es [EYoungAlloc (U64.v wz) (U64.v tag) vs]));
    o
  } else {
    fold (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp);
    fold (crepg c sty es);
    rewrite (crepg c sty es)
         as (if 0UL = 0UL then crepg c sty es else crepg c sty (L.append es [EYoungAlloc (U64.v wz) (U64.v tag) vs]));
    0UL
  }
  } else {
    fold (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp);
    fold (crepg c sty es);
    rewrite (crepg c sty es)
         as (if 0UL = 0UL then crepg c sty es else crepg c sty (L.append es [EYoungAlloc (U64.v wz) (U64.v tag) vs]));
    0UL
  }
}
#pop-options

/// **`EWrite` into a young block**: the word stored in the nursery, at the
/// field's offset `8 * (o + 1 + i)` (no barrier: 4.14's `Is_young`
/// test in C).
#push-options "--z3rlimit 40"
fn ywriteg (c: gcs) (a: U64.t) (w: U64.t) (#sty: erased style) (#es: erased (list event))
  (o i: erased nat) (v: erased M.value)
  requires crepg c sty es **
           pure (CR.allowed CF.fc sty (CF.xc es) (EWrite (M.Young o) i v) /\
                 U64.v a == 8 * (o + 1 + i) /\ w == W.concv v)
  ensures crepg c sty (L.append es [EWrite (M.Young o) i v])
{
  unfold crepg;
  with d b tv n. assert (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  FWr.write_young sty es o i v;
  Gl.ywrite_g sty es o i v;
  unfold GI.is_gen_heap;
  TM.mwrite_eq d a w;
  minor_write c.gh.GI.minor a w;
  fold (GI.is_gen_heap c.gh (minor_write_word_t d a w) b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp);
  major_same c (minor_write_word_t d a w) b es (L.append es [EWrite (M.Young o) i v]);
  fold (crepg c sty (L.append es [EWrite (M.Young o) i v]))
}
#pop-options

/// ---------------------------------------------------------------------------
/// The barrier
/// ---------------------------------------------------------------------------

/// The record keeps its meaning across a change that keeps the walk and
/// its headers, and whatever the heap while marking.
ghost fn keep_phase (r: R.ref AI.phase_state) (g g': SB.heap) (ph: Ph.gc_phase)
  requires AI.is_phase r g ph ** pure (Ph.Marking? ph \/ SPI.same_heads g g')
  ensures AI.is_phase r g' ph
{
  unfold AI.is_phase;
  with v. assert (R.pts_to r v);
  if (Ph.Marking? ph) {
    fold (AI.is_phase r g' ph)
  } else {
    FT.phase_keep g g' v ph;
    fold (AI.is_phase r g' ph)
  }
}

/// The code's tests are the model's: marking, and the block scannable.
let dk_eq (g: SB.heap) (obj: obj_addr) (h: U64.t) (pv: AI.phase_state) (ph: T.phase U64.t)
  : Lemma (requires h == GC.Spec.Heap.read_word g (GC.Spec.Heap.hd_address obj) /\ AI.phase_rel g pv (FAl.gph ph))
          (ensures (U64.lt (Obj.getTag h) 251UL <==> GC.Spec.Fields.scannable g obj) /\
                   (U64.gte pv.AI.ps_kind 2UL <==> T.Marking? ph))
  = SO.tag_of_object_spec obj g;
    SO.is_no_scan_spec obj g;
    Obj.getTag_eq h;
    SO.no_scan_tag_val ();
    assert (GC.Spec.Fields.scannable g obj == not (SO.is_no_scan obj g))

/// The heap, stack and flag the code leaves are the barrier's.
let after_darken (dk: bool) (g s1: SB.heap) (st st1: Seq.seq obj_addr) (ov ov1: bool) (cap: nat) (a: hp_addr) (w: U64.t)
  : Lemma (requires (dk ==> (s1, st1) == MB.check_and_darken_bounded_spec g st (GC.Spec.Heap.read_word g a) cap /\
                            ov1 == (ov || Seq.length st = cap)) /\
                    (not dk ==> s1 == g /\ st1 == st /\ ov1 == ov))
          (ensures GC.Spec.Heap.write_word s1 a w == FWr.code_heap dk g st cap a w /\
                   st1 == FWr.code_stack dk g st cap a /\ ov1 == FWr.code_ov dk st ov cap)
  = ()

/// The barrier's darkening, when `dk`: the overflow flag raised when the
/// stack is full, then akhil's bounded darkening of the old value.
fn darken_if (heap: heap_t) (stk: gray_stack) (ovr: R.ref bool) (dk: bool) (old: U64.t)
  (#s: erased SB.heap) (#st: erased (Seq.seq obj_addr)) (#ov: erased bool)
  requires is_heap heap s ** is_gray_stack stk st ** R.pts_to ovr ov ** pure (Seq.length st <= stack_capacity stk)
  ensures exists* s1 st1 ov1. is_heap heap s1 ** is_gray_stack stk st1 ** R.pts_to ovr ov1 **
          pure ((dk ==> (s1, st1) == MB.check_and_darken_bounded_spec s st old (stack_capacity stk) /\
                        ov1 == (reveal ov || Seq.length st = stack_capacity stk)) /\
                (not dk ==> s1 == reveal s /\ st1 == reveal st /\ ov1 == reveal ov))
{
  if dk {
    let full = is_full stk;
    let o = !ovr;
    ovr := (o || full);
    MB.check_and_darken_bounded heap stk old (hide (stack_capacity stk))
  } else {
    ()
  }
}

/// The slot appended to the table when `rc`.
fn push_if_rc (tb: A.array U64.t) (tn: R.ref SZ.t) (cap: SZ.t) (rc: bool) (a: U64.t)
  (#tv: erased (Seq.seq U64.t)) (#n: erased SZ.t)
  requires A.pts_to tb tv ** R.pts_to tn n ** pure (SZ.v n < SZ.v cap /\ Seq.length tv == SZ.v cap)
  ensures exists* tv' n'. A.pts_to tb tv' ** R.pts_to tn n' **
          pure (SZ.v n < Seq.length tv /\ Seq.length tv' == SZ.v cap /\
                (rc ==> tv' == Seq.upd tv (SZ.v n) a /\ SZ.v n' == SZ.v n + 1) /\
                (not rc ==> tv' == reveal tv /\ n' == reveal n))
{
  if rc {
    let nv = !tn;
    tb.(nv) <- a;
    tn := SZ.add nv 1sz
  } else {
    ()
  }
}

/// **`EWrite` into a major block** (`caml_modify`), as akhil builds his
/// barrier (`GC.Gen.Impl.Barrier.modify_at`) from exported pieces: while
/// marking a scannable block, the old value darkened (the flag raised when
/// the stack is full); then the store; the slot appended to the table when
/// the block is scannable and akhil's barrier says to remember it (the new
/// value young and the old one not, `GB.modify_records`).  `obj` is the
/// block's first-field address.  When the table is full nothing is done and
/// the result is false (no event; a minor collection empties it).
#push-options "--z3rlimit 40"
fn writeg (c: gcs) (obj: obj_addr) (i: U64.t) (w: U64.t) (#sty: erased style) (#es: erased (list event))
  (o: erased nat) (v: erased M.value)
  requires crepg c sty es **
           pure (CR.allowed CF.fc sty (CF.xc es) (EWrite (M.Major o) (U64.v i) v) /\
                 U64.v obj == Abs.pos o + 8 /\ w == W.concv v)
  returns ok: bool
  ensures (if ok then crepg c sty (L.append es [EWrite (M.Major o) (U64.v i) v]) else crepg c sty es)
{
  unfold crepg;
  with d b tv n. assert (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  let nv = !c.tn;
  Gl.tbl_e_len tv (SZ.v nv) (CF.xc es).w.crem;
  if (SZ.lt nv c.tcap) {
    unfold GI.is_gen_heap;
    unfold GI.gen_phase;
    unfold GI.mark_state;
    with st ov cc f r mw. assert (is_gray_stack c.gh.GI.mark_stack st ** R.pts_to c.gh.GI.mark_overflow ov **
      R.pts_to c.gh.GI.mark_cur cc ** R.pts_to c.gh.GI.mark_field f ** R.pts_to c.gh.GI.mark_rescan r **
      R.pts_to c.gh.GI.mark_words mw);
    stack_facts c.gh.GI.mark_stack;
    Gl.write_g sty es o (U64.v i) v tv (SZ.v nv) st ov (MSI.pos cc f r) (stack_capacity c.gh.GI.mark_stack);
    BF.obj_of_v o;
    U64.v_inj obj (Abs.obj_of o);
    let a : hp_addr = U64.add obj (U64.mul 8UL i);
    U64.v_inj a (Abs.hp (o + 1 + U64.v i));
    let h = read_word c.gh.GI.major (GC.Spec.Heap.hd_address obj);
    SO.tag_of_object_spec obj (CF.hof (CF.xc es));
    Obj.getTag_eq h;
    let scn = U64.lt (Obj.getTag h) 251UL;
    unfold AI.is_phase;
    with pv0. assert (R.pts_to c.gh.GI.phase_ref pv0);
    let pv = !c.gh.GI.phase_ref;
    dk_eq (CF.hof (CF.xc es)) obj h pv (CF.xc es).ph;
    fold (AI.is_phase c.gh.GI.phase_ref (CF.hof (CF.xc es)) (FAl.gph (CF.xc es).ph));
    let marking = U64.gte pv.AI.ps_kind 2UL;
    let old = read_word c.gh.GI.major a;
    FMi.young_eq w;
    FMi.young_eq old;
    let rc = scn && TM.young_u64 w && not (TM.young_u64 old);
    darken_if c.gh.GI.major c.gh.GI.mark_stack c.gh.GI.mark_overflow (marking && scn) old;
    with s1 st1 ov1. assert (is_heap c.gh.GI.major s1 ** is_gray_stack c.gh.GI.mark_stack st1 **
      R.pts_to c.gh.GI.mark_overflow ov1);
    after_darken (marking && scn) (CF.hof (CF.xc es)) s1 st st1 ov ov1 (stack_capacity c.gh.GI.mark_stack) a w;
    write_word c.gh.GI.major a w;
    push_if_rc c.tb c.tn c.tcap rc a;
    rewrite (is_heap c.gh.GI.major (GC.Spec.Heap.write_word s1 a w))
         as (is_heap c.gh.GI.major (CF.hof (CF.xc (L.append es [EWrite (M.Major o) (U64.v i) v]))));
    rewrite (R.pts_to c.gh.GI.fp_ref (CF.sof (CF.xc es)).FAl.fp)
         as (R.pts_to c.gh.GI.fp_ref (CF.sof (CF.xc (L.append es [EWrite (M.Major o) (U64.v i) v]))).FAl.fp);
    keep_phase c.gh.GI.phase_ref (CF.hof (CF.xc es)) (CF.hof (CF.xc (L.append es [EWrite (M.Major o) (U64.v i) v])))
      (FAl.gph (CF.xc es).ph);
    rewrite (AI.is_phase c.gh.GI.phase_ref (CF.hof (CF.xc (L.append es [EWrite (M.Major o) (U64.v i) v]))) (FAl.gph (CF.xc es).ph))
         as (AI.is_phase c.gh.GI.phase_ref (CF.hof (CF.xc (L.append es [EWrite (M.Major o) (U64.v i) v])))
               (FAl.gph (CF.xc (L.append es [EWrite (M.Major o) (U64.v i) v])).ph));
    fold (GI.gen_phase c.gh (CF.hof (CF.xc (L.append es [EWrite (M.Major o) (U64.v i) v])))
            (FAl.gph (CF.xc (L.append es [EWrite (M.Major o) (U64.v i) v])).ph));
    fold (GI.is_gen_heap c.gh d b (CF.hof (CF.xc (L.append es [EWrite (M.Major o) (U64.v i) v])))
            (CF.sof (CF.xc (L.append es [EWrite (M.Major o) (U64.v i) v]))).FAl.fp);
    fold (GI.mark_state c.gh (CF.hof (CF.xc (L.append es [EWrite (M.Major o) (U64.v i) v])))
            (FAl.gph (CF.xc (L.append es [EWrite (M.Major o) (U64.v i) v])).ph)
            (FG.spof (scan_of (CF.xc (L.append es [EWrite (M.Major o) (U64.v i) v])))));
    fold (crepg c sty (L.append es [EWrite (M.Major o) (U64.v i) v]));
    rewrite (crepg c sty (L.append es [EWrite (M.Major o) (U64.v i) v]))
         as (if true then crepg c sty (L.append es [EWrite (M.Major o) (U64.v i) v]) else crepg c sty es);
    true
  } else {
    fold (crepg c sty es);
    rewrite (crepg c sty es)
         as (if false then crepg c sty (L.append es [EWrite (M.Major o) (U64.v i) v]) else crepg c sty es);
    false
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// The minor collection
/// ---------------------------------------------------------------------------

module V = Pulse.Lib.Vec
module FA = GC.Gen.ForwardingArray
module LV = GC.Spec.Top.PagesLive
module FAO = GC.Spec.Top.FFAllocOk
module C = GC.Gen.Cheney
module CB = GC.Gen.CheneyBFS
module GP = GC.Gen.Promote
module AC2 = Pulse.Lib.Array.Core

/// **The run ended**: akhil's collection reported a failed promotion.  His
/// postcondition then says only that some state from which finishing gives
/// the same end fails (`cheney_oom`, counterfactual), so no event follows
/// (design doc §18.11): the run `es` is the code's up to the call, and the
/// state is the code's.
let stoppedg (c: gcs) (sty: style) (es: list event) : slprop =
  exists* (d: minor_heap) (b: U64.t) (g: SB.heap) (fp: U64.t) (ph: Ph.gc_phase) (sp: MP.scan_pos)
          (tv: Seq.seq U64.t) (n: SZ.t).
    GI.is_gen_heap c.gh d b g fp ** GI.gen_phase c.gh g ph ** GI.mark_state c.gh g ph sp **
    A.pts_to c.tb tv ** R.pts_to c.tn n ** pure (CF.good sty es)

/// akhil's precondition, as `CodeFFMinor` restates it.
let pre_eq (ph: Ph.gc_phase) (free: GC.Spec.Fields.free_def) (ms: minor_state) (s: SB.heap) (fp: U64.t)
  (rs farr sl: Seq.seq U64.t) (nslots: nat)
  : Lemma (requires FMi.pre_with ph free ms s fp rs farr sl nslots)
          (ensures GI.minor_collect_pre_with ph free ms s fp rs farr sl nslots)
  = ()

/// **The collection on the glue's roots**: the program's young roots `yv`
/// (given by the caller, in the model's order), then the young words of the
/// table's slots (`CodeFFDup.rsd`); akhil's `minor_collect_with` at the
/// phase, with the nursery's two conditions as the caller's trusted
/// hypotheses (design doc §18.5).  When it reports success, `EMinor`, the
/// table emptied; otherwise the run ends (`stoppedg`).  Returns the
/// rewritten roots (`roots_after`: with the caller's major roots `mr`, the
/// members of the roots' major words after the collection), in a vector the
/// caller frees; the success flag in `okr`.
#push-options "--z3rlimit 40"
fn minor_run (c: gcs) (fa: A.array U64.t) (q: AC2.larray U64.t FA.queue_size) (yr: A.array U64.t) (k0: SZ.t)
  (okr: R.ref bool) (#p: perm) (#yv: erased (Seq.seq U64.t)) (#sty: erased style) (#es: erased (list event))
  (mr: erased (Seq.seq U64.t))
  requires crepg c sty es ** A.pts_to fa 'fv ** A.pts_to q 'qv ** A.pts_to yr #p yv ** R.pts_to okr 'ok0 **
           pure (Seq.length 'fv == FA.fwd_array_size /\ Seq.length yv == SZ.v k0 /\
                 yv == LV.yroots (Y.ycabs (CF.xc es).w.cyng) (CF.xc es).w.croots /\
                 SZ.fits (SZ.v k0 + SZ.v c.tcap) /\
                 minor_guards_complete (CF.xc es).w.cyng /\ minor_infix_wf (CF.xc es).w.cyng)
  returns rv: V.vec U64.t
  ensures exists* fv' qv' rs2 ok.
            A.pts_to fa fv' ** A.pts_to q qv' ** A.pts_to yr #p yv ** R.pts_to okr ok ** V.pts_to rv rs2 **
            (if ok then crepg c sty (L.append es [EMinor]) else stoppedg c sty es) **
            pure (V.is_full_vec rv /\
                  (ok ==> Gl.roots_after es mr rs2 /\ (CF.xc (L.append es [EMinor])).ph == (CF.xc es).ph /\
                          (CF.xc (L.append es [EMinor])).w.cyng == minor_reset (CF.xc es).w.cyng /\
                          (CF.xc (L.append es [EMinor])).w.crem == []))
{
  unfold crepg;
  with d b tv n. assert (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp ** A.pts_to c.tb tv ** R.pts_to c.tn n);
  unfold GI.mark_state;
  with st ov cc f r mw. assert (is_gray_stack c.gh.GI.mark_stack st ** R.pts_to c.gh.GI.mark_overflow ov **
    R.pts_to c.gh.GI.mark_cur cc ** R.pts_to c.gh.GI.mark_field f ** R.pts_to c.gh.GI.mark_rescan r **
    R.pts_to c.gh.GI.mark_words mw);
  Gl.tbl_addrs_e sty es tv (SZ.v n);
  TM.zero_fwd fa;
  with fv0. assert (A.pts_to fa fv0);
  Gl.minor_pre_e sty es tv (SZ.v n) fv0;
  let nv = !c.tn;
  unfold GI.is_gen_heap;
  let m = TM.count_young c.gh.GI.major c.tb nv;
  SZ.fits_lte (SZ.v k0 + SZ.v m) (SZ.v k0 + SZ.v c.tcap);
  let len = SZ.add k0 m;
  let rv = V.alloc 0UL len;
  V.to_array_pts_to rv;
  let ra = V.vec_to_array rv;
  rewrite (A.pts_to (V.vec_to_array rv) (Seq.create (SZ.v len) 0UL)) as (A.pts_to ra (Seq.create (SZ.v len) 0UL));
  TM.fill_roots c.gh.GI.major c.tb nv yr k0 ra;
  assert (pure (Seq.append yv (CM.ypre_tbl (CF.hof (CF.xc es)) tv (SZ.v nv)) == Dup.rsd (CF.xc es) tv (SZ.v n)));
  pre_eq (FAl.gph (CF.xc es).ph) (FAO.ffree_of (CF.xc es).ph) (CF.xc es).w.cyng (CF.hof (CF.xc es))
    (CF.sof (CF.xc es)).FAl.fp (Dup.rsd (CF.xc es) tv (SZ.v n)) fv0 tv (SZ.v n);
  fold (GI.is_gen_heap c.gh d b (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp);
  let ok = GI.minor_collect_with c.gh ra len fa q c.tb nv #(hide (FAO.ffree_of (CF.xc es).ph));
  with d2 b2 s2 fp2 rs2. assert (GI.is_gen_heap c.gh d2 b2 s2 fp2 ** A.pts_to ra rs2);
  Gl.minor_cache sty es tv (SZ.v n) st ov (MSI.pos cc f r) s2;
  rewrite (A.pts_to ra rs2) as (A.pts_to (V.vec_to_array rv) rs2);
  V.to_vec_pts_to rv;
  okr := ok;
  if ok {
    Gl.minor_post_e sty es tv (SZ.v n) s2 fp2 ({ data = d2; bump = b2 } <: minor_state);
    Gl.roots_after_e sty es tv (SZ.v n) mr rs2;
    c.tn := 0sz;
    Gl.tbl_e_nil tv;
    rewrite (GI.is_gen_heap c.gh d2 b2 s2 fp2)
         as (GI.is_gen_heap c.gh d2 b2 (CF.hof (CF.xc (L.append es [EMinor]))) (CF.sof (CF.xc (L.append es [EMinor]))).FAl.fp);
    rewrite (GI.gen_phase c.gh s2 (FAl.gph (CF.xc es).ph))
         as (GI.gen_phase c.gh (CF.hof (CF.xc (L.append es [EMinor]))) (FAl.gph (CF.xc (L.append es [EMinor])).ph));
    fold (GI.mark_state c.gh (CF.hof (CF.xc (L.append es [EMinor]))) (FAl.gph (CF.xc (L.append es [EMinor])).ph)
            (FG.spof (scan_of (CF.xc (L.append es [EMinor])))));
    fold (crepg c sty (L.append es [EMinor]));
    rewrite (crepg c sty (L.append es [EMinor]))
         as (if ok then crepg c sty (L.append es [EMinor]) else stoppedg c sty es);
    rv
  } else {
    fold (GI.mark_state c.gh s2 (FAl.gph (CF.xc es).ph) (FG.spof (scan_of (CF.xc es))));
    fold (stoppedg c sty es);
    rewrite (stoppedg c sty es)
         as (if ok then crepg c sty (L.append es [EMinor]) else stoppedg c sty es);
    rv
  }
}
#pop-options

/// **`EMinor`**: the collection on the program's young roots `yv` and the
/// table's slots, the table emptied.  Returns false when the collection
/// reported a failed promotion: the run has ended (no event).  The
/// forwarding array and the queue are scratch space.
fn minorg (c: gcs) (fa: A.array U64.t) (q: AC2.larray U64.t FA.queue_size) (yr: A.array U64.t) (k0: SZ.t)
  (#p: perm) (#yv: erased (Seq.seq U64.t)) (#sty: erased style) (#es: erased (list event))
  requires crepg c sty es ** A.pts_to fa 'fv ** A.pts_to q 'qv ** A.pts_to yr #p yv **
           pure (Seq.length 'fv == FA.fwd_array_size /\ Seq.length yv == SZ.v k0 /\
                 yv == LV.yroots (Y.ycabs (CF.xc es).w.cyng) (CF.xc es).w.croots /\
                 SZ.fits (SZ.v k0 + SZ.v c.tcap) /\
                 minor_guards_complete (CF.xc es).w.cyng /\ minor_infix_wf (CF.xc es).w.cyng)
  returns ok: bool
  ensures (exists* fv' qv'. A.pts_to fa fv' ** A.pts_to q qv') ** A.pts_to yr #p yv **
          (if ok then crepg c sty (L.append es [EMinor]) else stoppedg c sty es)
{
  let mut okr = false;
  let rv = minor_run c fa q yr k0 okr (hide Seq.empty);
  V.free rv;
  let ok = !okr;
  ok
}

/// ---------------------------------------------------------------------------
/// The start of a cycle
/// ---------------------------------------------------------------------------

/// Copy `len` words of `src` into `dst` from `off`.
fn copy_into (src dst: A.array U64.t) (off len: SZ.t) (#ps: perm) (#sv: erased (Seq.seq U64.t))
  (#dv0: erased (Seq.seq U64.t))
  requires A.pts_to src #ps sv ** A.pts_to dst dv0 **
           pure (SZ.v len <= Seq.length sv /\ SZ.v off + SZ.v len <= Seq.length dv0 /\ SZ.fits (SZ.v off + SZ.v len))
  ensures exists* dv. A.pts_to src #ps sv ** A.pts_to dst dv **
          pure (SZ.v len <= Seq.length sv /\ SZ.v off + SZ.v len <= Seq.length dv0 /\
                Seq.length dv == Seq.length dv0 /\
                (forall (j: nat). j < SZ.v off ==> Seq.index dv j == Seq.index dv0 j) /\
                (forall (j: nat). j < SZ.v len ==> Seq.index dv (SZ.v off + j) == Seq.index sv j))
{
  let mut i = 0sz;
  while (SZ.lt !i len)
    invariant exists* vi dv.
      R.pts_to i vi ** A.pts_to src #ps sv ** A.pts_to dst dv **
      pure (SZ.v vi <= SZ.v len /\ SZ.fits (SZ.v off + SZ.v len) /\ SZ.v len <= Seq.length sv /\ SZ.v off + SZ.v len <= Seq.length dv0 /\
            Seq.length dv == Seq.length dv0 /\
            (forall (j: nat). j < SZ.v off ==> Seq.index dv j == Seq.index dv0 j) /\
            (forall (j: nat). j < SZ.v vi ==> Seq.index dv (SZ.v off + j) == Seq.index sv j))
    decreases (SZ.v len - SZ.v !i)
  {
    let vi = !i;
    let w = src.(vi);
    SZ.fits_lte (SZ.v off + SZ.v vi) (SZ.v off + SZ.v len);
    dst.(SZ.add off vi) <- w;
    i := SZ.add vi 1sz
  }
}

/// The darkening array is the rewritten young roots, then the major ones.
let dark_eq (rs2 mr dv: Seq.seq U64.t) (k: nat)
  : Lemma (requires k <= Seq.length rs2 /\ Seq.length dv == k + Seq.length mr /\
                    (forall (j: nat). j < k ==> Seq.index dv j == Seq.index rs2 j) /\
                    (forall (j: nat). j < Seq.length mr ==> Seq.index dv (k + j) == Seq.index mr j))
          (ensures dv == Seq.append (Seq.slice rs2 0 k) mr)
  = assert (Seq.equal dv (Seq.append (Seq.slice rs2 0 k) mr))

/// **`EStart`, after a minor collection** (design doc §18.11, the user's
/// plan): `EMinor` as `minorg`, which empties the nursery and the remembered
/// set; then akhil's `start_cycle` darkens the roots' major words -- the
/// rewritten young roots (the first `k0` of the collection's roots) and the
/// caller's major roots `mrv` (any order, repeats allowed: `mr_ok`) -- and
/// enters marking.  Idle only.  Returns false when the collection reported a
/// failed promotion: the run has ended (no event).
#push-options "--z3rlimit 40"
fn startg (c: gcs) (fa: A.array U64.t) (q: AC2.larray U64.t FA.queue_size) (yr: A.array U64.t) (k0: SZ.t)
  (mra: A.array U64.t) (km: SZ.t)
  (#p #pm: perm) (#yv #mrv: erased (Seq.seq U64.t)) (#sty: erased style) (#es: erased (list event))
  requires crepg c sty es ** A.pts_to fa 'fv ** A.pts_to q 'qv ** A.pts_to yr #p yv ** A.pts_to mra #pm mrv **
           pure (Seq.length 'fv == FA.fwd_array_size /\ Seq.length yv == SZ.v k0 /\
                 yv == LV.yroots (Y.ycabs (CF.xc es).w.cyng) (CF.xc es).w.croots /\
                 SZ.fits (SZ.v k0 + SZ.v c.tcap) /\ SZ.fits (SZ.v k0 + SZ.v km) /\
                 Seq.length mrv == SZ.v km /\ Gl.mr_ok es mrv /\ T.Idle? (CF.xc es).ph /\
                 minor_guards_complete (CF.xc es).w.cyng /\ minor_infix_wf (CF.xc es).w.cyng)
  returns ok: bool
  ensures (exists* fv' qv'. A.pts_to fa fv' ** A.pts_to q qv') ** A.pts_to yr #p yv ** A.pts_to mra #pm mrv **
          (if ok then crepg c sty (L.append (L.append es [EMinor]) [EStart]) else stoppedg c sty es)
{
  let mut okr = false;
  let rv = minor_run c fa q yr k0 okr mrv;
  with rs2 okv. assert (V.pts_to rv rs2 ** R.pts_to okr okv);
  let ok = !okr;
  if ok {
    rewrite (if okv then crepg c sty (L.append es [EMinor]) else stoppedg c sty es)
         as (crepg c sty (L.append es [EMinor]));
    let dlen = SZ.add k0 km;
    let dv = V.alloc 0UL dlen;
    V.to_array_pts_to dv;
    let da = V.vec_to_array dv;
    rewrite (A.pts_to (V.vec_to_array dv) (Seq.create (SZ.v dlen) 0UL)) as (A.pts_to da (Seq.create (SZ.v dlen) 0UL));
    V.to_array_pts_to rv;
    copy_into (V.vec_to_array rv) da 0sz k0;
    copy_into mra da k0 km;
    with dav. assert (A.pts_to da dav);
    dark_eq rs2 mrv dav (SZ.v k0);
    unfold crepg;
    with d b tv n. assert (GI.is_gen_heap c.gh d b (CF.hof (CF.xc (L.append es [EMinor]))) (CF.sof (CF.xc (L.append es [EMinor]))).FAl.fp ** A.pts_to c.tb tv ** R.pts_to c.tn n);
    FMk.idle_shape sty (L.append es [EMinor]) ({ data = d; bump = b } <: minor_state)
      (FG.spof (scan_of (CF.xc (L.append es [EMinor]))));
    Gl.start_g sty (L.append es [EMinor]) dav;
    rewrite (GI.gen_phase c.gh (CF.hof (CF.xc (L.append es [EMinor]))) (FAl.gph (CF.xc (L.append es [EMinor])).ph))
         as (GI.gen_phase c.gh (CF.hof (CF.xc (L.append es [EMinor]))) Ph.Idle);
    rewrite (GI.mark_state c.gh (CF.hof (CF.xc (L.append es [EMinor]))) (FAl.gph (CF.xc (L.append es [EMinor])).ph)
               (FG.spof (scan_of (CF.xc (L.append es [EMinor])))))
         as (GI.mark_state c.gh (CF.hof (CF.xc (L.append es [EMinor]))) Ph.Idle
               (FG.spof (scan_of (CF.xc (L.append es [EMinor])))));
    fold (GI.gc_state c.gh d b (CF.hof (CF.xc (L.append es [EMinor]))) (CF.sof (CF.xc (L.append es [EMinor]))).FAl.fp
            Ph.Idle (FG.spof (scan_of (CF.xc (L.append es [EMinor])))));
    GI.start_cycle c.gh da dlen;
    with s3. assert (GI.gc_state c.gh d b s3 (CF.sof (CF.xc (L.append es [EMinor]))).FAl.fp Ph.Marking MP.scan_none);
    unfold GI.gc_state;
    rewrite (GI.is_gen_heap c.gh d b s3 (CF.sof (CF.xc (L.append es [EMinor]))).FAl.fp)
         as (GI.is_gen_heap c.gh d b (CF.hof (CF.xc (L.append (L.append es [EMinor]) [EStart])))
               (CF.sof (CF.xc (L.append (L.append es [EMinor]) [EStart]))).FAl.fp);
    rewrite (GI.gen_phase c.gh s3 Ph.Marking)
         as (GI.gen_phase c.gh (CF.hof (CF.xc (L.append (L.append es [EMinor]) [EStart])))
               (FAl.gph (CF.xc (L.append (L.append es [EMinor]) [EStart])).ph));
    rewrite (GI.mark_state c.gh s3 Ph.Marking MP.scan_none)
         as (GI.mark_state c.gh (CF.hof (CF.xc (L.append (L.append es [EMinor]) [EStart])))
               (FAl.gph (CF.xc (L.append (L.append es [EMinor]) [EStart])).ph)
               (FG.spof (scan_of (CF.xc (L.append (L.append es [EMinor]) [EStart])))));
    fold (crepg c sty (L.append (L.append es [EMinor]) [EStart]));
    rewrite (A.pts_to da dav) as (A.pts_to (V.vec_to_array dv) dav);
    V.to_vec_pts_to dv;
    V.free dv;
    V.to_vec_pts_to rv;
    V.free rv;
    rewrite (crepg c sty (L.append (L.append es [EMinor]) [EStart]))
         as (if ok then crepg c sty (L.append (L.append es [EMinor]) [EStart]) else stoppedg c sty es);
    ok
  } else {
    V.free rv;
    rewrite (if okv then crepg c sty (L.append es [EMinor]) else stoppedg c sty es)
         as (if ok then crepg c sty (L.append (L.append es [EMinor]) [EStart]) else stoppedg c sty es);
    ok
  }
}
#pop-options
