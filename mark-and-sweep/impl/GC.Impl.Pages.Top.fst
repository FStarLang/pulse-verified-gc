/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Top - the pages code, event by event, as runs of the
/// top-level specification
/// ---------------------------------------------------------------------------
///
/// Design doc §18, step 1.  `crep heap t pr cr sty es`: the code's state (the
/// heap, the page state, the phase and the sweep's cursor) represents the
/// configuration of the pages collector `pc` after the events `es`, a run of
/// style `sty` (`GC.Spec.Top.CodePages.good`).  Each wrapper performs one
/// event and ensures the representation of the run one event longer; so
/// whatever sequence of wrappers runs, its events are a run of `pc`, and
/// `gc_correct`, T1 and T2 apply to it.
///   - `init_top`: a zeroed heap, then the page functions' empty heap: the
///     initial configuration, no event;
///   - `alloc_top`: `EAlloc`, the phase's allocation (`AllocInc.alloc_ph`)
///     and the Fill, the fields written in order;
///   - `handover_top`: `EHandover`, the sweep's start (`Sweep.start_sweep`);
///   - `sweep_step_top`: from the cursor, the next unit; `ESweep` there
///     (`SweepInc.sweep_unit`), or `EEnd` when there is none;
///   - `roots_top`, `read_top`: the program's root events, ghost: the roots
///     are kept by the program (trusted, §18.5).
/// The roots, the remembered set and the nursery are ghost here; the mark,
/// the barrier and the minor collection are later steps (§18.7).

module GC.Impl.Pages.Top

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Impl.Heap
open GC.Impl.Pages.State
open GC.Spec.Top.Run

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module L = FStar.List.Tot
module SH = GC.Spec.Heap
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module W = GC.Spec.Top.Word
module Abs = GC.Spec.Top.Abs
module BF = GC.Spec.Top.ByteFacts
module PAl = GC.Spec.Top.PagesAlloc
module PSw = GC.Spec.Top.PagesSweep
module Inc = GC.Spec.Pages.Incr
module CP = GC.Spec.Top.CodePages
module CR = GC.Spec.Top.CodeRun
module IA = GC.Impl.Pages.AllocInc
module IS = GC.Impl.Pages.Sweep
module ISI = GC.Impl.Pages.SweepInc
module II = GC.Impl.Pages.Init
module AT = GC.Spec.Pages.AllocTag

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The representation
/// ---------------------------------------------------------------------------

/// **The code's state represents the configuration after `es`.**
let crep (heap: heap_t) (t: pstate_t) (pr: R.ref U8.t) (cr: R.ref U64.t) (sty: style) (es: list event)
  : slprop =
  exists* (x: config CP.pc) (c: U64.t).
    is_heap heap (CP.hof x) ** pages_st t (CP.sof x).ps ** R.pts_to pr (CP.phase_code x.ph) ** R.pts_to cr c **
    pure (x == CP.xc es /\ CP.good sty es /\ U64.v c == CP.cursor_of x.ph)

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

/// Zero every byte of the heap.
fn zero_heap (heap: heap_t)
  requires is_heap heap 'g
  ensures is_heap heap PAl.zero_heap
{
  let mut a = 0UL;
  while (U64.lt !a heap_size_u64)
    invariant exists* va g1.
      R.pts_to a va ** is_heap heap g1 **
      pure (U64.v va % 8 == 0 /\ U64.v va <= heap_size /\
            (forall (i: nat). i < U64.v va ==> Seq.index g1 i == 0uy))
    decreases (heap_size - U64.v !a)
  {
    let va = !a;
    with g1. assert (is_heap heap g1);
    CP.zero_word g1 va;
    write_word heap va 0UL;
    a := U64.add va 8UL
  };
  with g1. assert (is_heap heap g1);
  CP.zero_all g1;
  rewrite (is_heap heap g1) as (is_heap heap PAl.zero_heap)
}

/// **The start**: when there is a page, the initial configuration.
fn init_top (heap: heap_t) (t: pstate_t) (pr: R.ref U8.t) (cr: R.ref U64.t) (sty: erased style)
  requires is_heap heap 'g ** pages_raw t ** R.pts_to pr 'p0 ** R.pts_to cr 'c0
  returns ok: bool
  ensures (if ok then crep heap t pr cr sty []
           else is_heap heap 'g ** pages_raw t ** R.pts_to pr 'p0 ** R.pts_to cr 'c0)
{
  let np = n_pages_u64 ();
  if (U64.gt np 0UL) {
    zero_heap heap;
    II.init heap t;
    pr := 0uy;
    cr := 0UL;
    CP.init_cfg sty;
    with g' st'. assert (is_heap heap g' ** pages_st t st');
    rewrite (is_heap heap g') as (is_heap heap (CP.hof (CP.xc [])));
    rewrite (pages_st t st') as (pages_st t (CP.sof (CP.xc [])).ps);
    rewrite (R.pts_to pr 0uy) as (R.pts_to pr (CP.phase_code (CP.xc []).ph));
    fold (crep heap t pr cr sty []);
    true
  } else {
    false
  }
}

/// ---------------------------------------------------------------------------
/// Allocation and its Fill
/// ---------------------------------------------------------------------------

/// The Fill: write the words `ws` as the fields of the block whose first
/// field is at `o`, in order.
fn fill (heap: heap_t) (o: U64.t) (wz: U64.t) (fs: A.array U64.t) (#p: perm) (#ws: erased (Seq.seq U64.t))
  (m: erased nat) (vs: erased (list M.value))
  requires is_heap heap 'g ** A.pts_to fs #p ws **
           pure (Abs.pos m + 8 == U64.v o /\ U64.v o + 8 * U64.v wz <= heap_size /\
                 Seq.length ws == U64.v wz /\ L.length vs == U64.v wz /\
                 (forall (i: nat). i < U64.v wz ==> Seq.index ws i == W.concv (L.index vs i)))
  ensures is_heap heap (CP.fill_from 'g m 0 vs) ** A.pts_to fs #p ws
{
  CP.ldrop_zero (reveal vs);
  let mut k = 0UL;
  while (U64.lt !k wz)
    invariant exists* vk g1.
      R.pts_to k vk ** is_heap heap g1 ** A.pts_to fs #p ws **
      pure (U64.v vk <= U64.v wz /\
            CP.fill_from g1 m (U64.v vk) (CP.ldrop (U64.v vk) vs) == CP.fill_from 'g m 0 vs)
    decreases (U64.v wz - U64.v !k)
  {
    let vk = !k;
    with g1. assert (is_heap heap g1);
    let w = fs.(SZ.uint64_to_sizet vk);
    CP.fill_step g1 m (U64.v vk) vs;
    CP.field_addr (U64.v o) m (U64.v vk);
    let a : hp_addr = U64.add o (U64.mul 8UL vk);
    U64.v_inj a (Abs.hp (m + 1 + U64.v vk));
    write_word heap a w;
    k := U64.add vk 1UL
  };
  with g1. assert (is_heap heap g1);
  CP.fill_done g1 m vs;
  rewrite (is_heap heap g1) as (is_heap heap (CP.fill_from 'g m 0 vs))
}

/// **`EAlloc`**: the allocation of the phase, then the Fill with the words
/// `ws` (the values `vs`).  Returns the new block's first-field address, or
/// 0 when there is no room (then nothing changes).
fn alloc_top (heap: heap_t) (t: pstate_t) (pr: R.ref U8.t) (cr: R.ref U64.t)
  (wz: U64.t{U64.v wz >= 1}) (tag: U64.t{U64.v tag < 256}) (fs: A.array U64.t) (#p: perm)
  (#ws: erased (Seq.seq U64.t)) (#sty: erased style) (#es: erased (list event)) (vs: erased (list M.value))
  requires crep heap t pr cr sty es ** A.pts_to fs #p ws **
           pure (Seq.length ws == U64.v wz /\ L.length vs == U64.v wz /\
                 (forall (i: nat). i < U64.v wz ==> Seq.index ws i == W.concv (L.index vs i)) /\
                 CR.allowed CP.pc sty (CP.xc es) (EAlloc (U64.v wz) (U64.v tag) vs))
  returns o: U64.t
  ensures crep heap t pr cr sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]) ** A.pts_to fs #p ws **
          pure (o == 0UL ==> CP.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]) == CP.xc es) **
          pure (let x = CP.xc es in
                let (_, _, o') = AT.alloc_tag (PAl.iph x.ph) (CP.hof x) (CP.sof x).ps (U64.v wz) (PAl.tg (U64.v tag)) in
                o == o')
{
  unfold crep;
  with x c. assert (is_heap heap (CP.hof x) ** R.pts_to cr c);
  CP.good_inv sty es;
  CP.tg_eq tag;
  CP.marking_code x.ph;
  let phc = !pr;
  let o = IA.alloc_ph heap t wz tag (phc = 1uy) #(PAl.iph x.ph) #((CP.sof x).ps);
  with g' st'. assert (is_heap heap g' ** pages_st t st');
  if (o = 0UL) {
    CP.alloc_none sty es (U64.v wz) (U64.v tag) vs;
    CP.snoc sty es (EAlloc (U64.v wz) (U64.v tag) vs);
    rewrite (is_heap heap g') as (is_heap heap (CP.hof (CP.xc (L.append es [(EAlloc (U64.v wz) (U64.v tag) vs)]))));
    rewrite (pages_st t st') as (pages_st t (CP.sof (CP.xc (L.append es [(EAlloc (U64.v wz) (U64.v tag) vs)]))).ps);
    rewrite (R.pts_to pr (CP.phase_code x.ph)) as (R.pts_to pr (CP.phase_code (CP.xc (L.append es [(EAlloc (U64.v wz) (U64.v tag) vs)])).ph));
    fold (crep heap t pr cr sty (L.append es [(EAlloc (U64.v wz) (U64.v tag) vs)]));
    o
  } else {
    CP.alloc_some sty es (U64.v wz) (U64.v tag) vs;
    fill heap o wz fs (BF.maddr o) vs;
    CP.snoc sty es (EAlloc (U64.v wz) (U64.v tag) vs);
    rewrite (is_heap heap (CP.fill_from g' (BF.maddr o) 0 vs))
         as (is_heap heap (CP.hof (CP.xc (L.append es [(EAlloc (U64.v wz) (U64.v tag) vs)]))));
    rewrite (pages_st t st') as (pages_st t (CP.sof (CP.xc (L.append es [(EAlloc (U64.v wz) (U64.v tag) vs)]))).ps);
    rewrite (R.pts_to pr (CP.phase_code x.ph)) as (R.pts_to pr (CP.phase_code (CP.xc (L.append es [(EAlloc (U64.v wz) (U64.v tag) vs)])).ph));
    fold (crep heap t pr cr sty (L.append es [(EAlloc (U64.v wz) (U64.v tag) vs)]));
    o
  }
}

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

/// **`EHandover`**: the sweep's start, the cursor at page 0.
fn handover_top (heap: heap_t) (t: pstate_t) (pr: R.ref U8.t) (cr: R.ref U64.t)
  (#sty: erased style) (#es: erased (list event))
  requires crep heap t pr cr sty es **
           pure ((CP.xc es).stopped == false /\ T.Marking? (CP.xc es).ph /\ T.mark_done (mj (CP.xc es)) /\
                 None? (scan_of (CP.xc es)))
  ensures crep heap t pr cr sty (L.append es [EHandover]) **
          pure (CR.allowed CP.pc sty (CP.xc es) EHandover /\
                CP.xc (L.append es [EHandover]) == step CP.pc (CP.xc es) EHandover)
{
  unfold crep;
  with x c. assert (is_heap heap (CP.hof x) ** R.pts_to cr c);
  CP.handover_cfg x;
  CP.allowed_gc sty es EHandover;
  CP.snoc sty es EHandover;
  IS.start_sweep t;
  pr := 2uy;
  cr := 0UL;
  rewrite (is_heap heap (CP.hof x)) as (is_heap heap (CP.hof (CP.xc (L.append es [EHandover]))));
  rewrite (pages_st t (GC.Spec.Pages.StartSweep.start_sweep (CP.sof x).ps))
       as (pages_st t (CP.sof (CP.xc (L.append es [EHandover]))).ps);
  rewrite (R.pts_to pr 2uy) as (R.pts_to pr (CP.phase_code (CP.xc (L.append es [EHandover])).ph));
  fold (crep heap t pr cr sty (L.append es [EHandover]))
}

/// Whether the sweep visits page `q` (`Incr.sweeps`), from its record.
let sweeps_rec (r: pinfo) : bool = not r.swept && (is_pool r || is_head r)

let sweeps_rec_ok (pm: page_map) (q: nat{q < n_pages}) (r: pinfo)
  : Lemma (requires view r == entry pm q) (ensures sweeps_rec r == Inc.sweeps pm q)
  = ()

/// The next unit at or after the cursor `c`: `nextu`.
fn next_unit (t: pstate_t) (c: U64.t) (#st: erased pstate)
  requires pages_st t st
  returns q: U64.t
  ensures pages_st t st ** pure (U64.v q == PSw.nextu st.pm (U64.v c) /\ U64.v q <= n_pages)
{
  let np = n_pages_u64 ();
  let mut q = c;
  let mut found = false;
  while (U64.lt !q np && not !found)
    invariant exists* vq vf.
      R.pts_to q vq ** R.pts_to found vf ** pages_st t st **
      pure (PSw.nextu st.pm (U64.v vq) == PSw.nextu st.pm (U64.v c) /\
            (vf ==> U64.v vq < n_pages /\ Inc.sweeps st.pm (U64.v vq)))
    decreases (n_pages + 1 - U64.v !q - (if !found then 1 else 0))
  {
    let vq = !q;
    CP.nextu_unfold st.pm (U64.v vq);
    let r = read_entry t vq;
    sweeps_rec_ok st.pm (U64.v vq) r;
    if (sweeps_rec r) {
      found := true
    } else {
      q := U64.add vq 1UL
    }
  };
  let vq = !q;
  let vf = !found;
  if (vf) {
    CP.nextu_unfold st.pm (U64.v vq);
    vq
  } else {
    CP.nextu_end st.pm (U64.v vq);
    np
  }
}

/// **A sweep step**: from the cursor, the next unit; `ESweep` sweeps it
/// and returns true; when there is none the sweep is done, `EEnd`, false.
fn sweep_step_top (heap: heap_t) (t: pstate_t) (pr: R.ref U8.t) (cr: R.ref U64.t)
  (#sty: erased style) (#es: erased (list event))
  requires crep heap t pr cr sty es ** pure ((CP.xc es).stopped == false /\ T.Sweeping? (CP.xc es).ph)
  returns more: bool
  ensures crep heap t pr cr sty (L.append es [if more then ESweep else EEnd]) **
          pure (CR.allowed CP.pc sty (CP.xc es) (if more then ESweep else EEnd) /\
                CP.xc (L.append es [if more then ESweep else EEnd]) ==
                step CP.pc (CP.xc es) (if more then ESweep else EEnd))
{
  unfold crep;
  with x c. assert (is_heap heap (CP.hof x) ** R.pts_to cr c);
  CP.good_inv sty es;
  CP.done_iff sty es;
  let vc = !cr;
  let q = next_unit t vc;
  if (U64.lt q (n_pages_u64 ())) {
    CP.sweep_cfg x;
    CP.allowed_gc sty es ESweep;
    CP.snoc sty es ESweep;
    let q' = ISI.sweep_unit heap t q;
    cr := q';
    with g' st'. assert (is_heap heap g' ** pages_st t st');
    rewrite (is_heap heap g') as (is_heap heap (CP.hof (CP.xc (L.append es [ESweep]))));
    rewrite (pages_st t st') as (pages_st t (CP.sof (CP.xc (L.append es [ESweep]))).ps);
    rewrite (R.pts_to pr (CP.phase_code x.ph)) as (R.pts_to pr (CP.phase_code (CP.xc (L.append es [ESweep])).ph));
    fold (crep heap t pr cr sty (L.append es [ESweep]));
    true
  } else {
    CP.end_cfg x;
    CP.allowed_gc sty es EEnd;
    CP.snoc sty es EEnd;
    pr := 0uy;
    cr := 0UL;
    rewrite (is_heap heap (CP.hof x)) as (is_heap heap (CP.hof (CP.xc (L.append es [EEnd]))));
    rewrite (pages_st t (CP.sof x).ps) as (pages_st t (CP.sof (CP.xc (L.append es [EEnd]))).ps);
    rewrite (R.pts_to pr 0uy) as (R.pts_to pr (CP.phase_code (CP.xc (L.append es [EEnd])).ph));
    fold (crep heap t pr cr sty (L.append es [EEnd]));
    false
  }
}

/// ---------------------------------------------------------------------------
/// The program's root events (ghost)
/// ---------------------------------------------------------------------------

/// **`ERoots`**: the program's roots, replaced.
ghost fn roots_top (heap: heap_t) (t: pstate_t) (pr: R.ref U8.t) (cr: R.ref U64.t)
  (#sty: erased style) (#es: erased (list event)) (rs: list M.value)
  requires crep heap t pr cr sty es ** pure (CR.allowed CP.pc sty (CP.xc es) (ERoots rs))
  ensures crep heap t pr cr sty (L.append es [ERoots rs]) **
          pure (CP.xc (L.append es [ERoots rs]) == step CP.pc (CP.xc es) (ERoots rs))
{
  unfold crep;
  with x c. assert (is_heap heap (CP.hof x) ** R.pts_to cr c);
  CP.roots_cfg x rs;
  CP.snoc sty es (ERoots rs);
  rewrite (is_heap heap (CP.hof x)) as (is_heap heap (CP.hof (CP.xc (L.append es [ERoots rs]))));
  rewrite (pages_st t (CP.sof x).ps) as (pages_st t (CP.sof (CP.xc (L.append es [ERoots rs]))).ps);
  rewrite (R.pts_to pr (CP.phase_code x.ph)) as (R.pts_to pr (CP.phase_code (CP.xc (L.append es [ERoots rs])).ph));
  fold (crep heap t pr cr sty (L.append es [ERoots rs]))
}

/// **`ERead`** of a major block's field into a new root.
ghost fn read_top (heap: heap_t) (t: pstate_t) (pr: R.ref U8.t) (cr: R.ref U64.t)
  (#sty: erased style) (#es: erased (list event)) (o i: nat)
  requires crep heap t pr cr sty es ** pure (CR.allowed CP.pc sty (CP.xc es) (ERead (M.Major o) i))
  ensures crep heap t pr cr sty (L.append es [ERead (M.Major o) i]) **
          pure (CP.xc (L.append es [ERead (M.Major o) i]) == step CP.pc (CP.xc es) (ERead (M.Major o) i))
{
  unfold crep;
  with x c. assert (is_heap heap (CP.hof x) ** R.pts_to cr c);
  CP.read_cfg x o i;
  CP.snoc sty es (ERead (M.Major o) i);
  rewrite (is_heap heap (CP.hof x)) as (is_heap heap (CP.hof (CP.xc (L.append es [ERead (M.Major o) i]))));
  rewrite (pages_st t (CP.sof x).ps) as (pages_st t (CP.sof (CP.xc (L.append es [ERead (M.Major o) i]))).ps);
  rewrite (R.pts_to pr (CP.phase_code x.ph))
       as (R.pts_to pr (CP.phase_code (CP.xc (L.append es [ERead (M.Major o) i])).ph));
  fold (crep heap t pr cr sty (L.append es [ERead (M.Major o) i]))
}

/// An event that leaves the major heap, the page state and the phase (the
/// nursery's), once the longer run is known good.
ghost fn young_top (heap: heap_t) (t: pstate_t) (pr: R.ref U8.t) (cr: R.ref U64.t)
  (#sty: erased style) (#es: erased (list event)) (e: event)
  requires crep heap t pr cr sty es **
           pure (CP.good sty (L.append es [e]) /\
                 CP.hof (CP.xc (L.append es [e])) == CP.hof (CP.xc es) /\
                 CP.sof (CP.xc (L.append es [e])) == CP.sof (CP.xc es) /\
                 (CP.xc (L.append es [e])).ph == (CP.xc es).ph)
  ensures crep heap t pr cr sty (L.append es [e])
{
  unfold crep;
  with x c. assert (is_heap heap (CP.hof x) ** R.pts_to cr c);
  rewrite (is_heap heap (CP.hof x)) as (is_heap heap (CP.hof (CP.xc (L.append es [e]))));
  rewrite (pages_st t (CP.sof x).ps) as (pages_st t (CP.sof (CP.xc (L.append es [e]))).ps);
  rewrite (R.pts_to pr (CP.phase_code x.ph)) as (R.pts_to pr (CP.phase_code (CP.xc (L.append es [e])).ph));
  fold (crep heap t pr cr sty (L.append es [e]))
}
