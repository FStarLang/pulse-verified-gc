/// ---------------------------------------------------------------------------
/// GC.Spec.Top.CodeFF - the first-fit code's events, as the model's steps
/// ---------------------------------------------------------------------------
///
/// Design doc §18, step 3.  The first-fit wrappers (GC.Impl.FFTop) keep the
/// events they have performed, `es`, and the configuration after them,
/// `xc es`, of the first-fit collector `fc`.  Here, for each event, what
/// `step` does, in the terms of the Pulse code's postconditions:
///   - L1 (`lo_ok`): the allocator state's low bytes are the heap's;
///   - the phase record of `GC.Impl.Allocator` (`phase_rel`: the kind, and
///     while sweeping the cursor with the caches derived from the heap,
///     `SPI.state_at`) holds the configuration's phase, and keeps holding it
///     through an allocation and its Fill (the Fill writes only the new
///     block's body: `FFFill.body_heads`);
///   - L5, allocation (`alloc_none`, `alloc_some`): the model's allocation is
///     `Cursor.alloc_phase`, which `Allocator.allocate` computes; the Fill is
///     the fields written in order (`CodePages.fill_from`);
///   - the start (`init_cfg`): the model's initial heap, one blue block from
///     `zero_addr`, written on a zeroed heap;
///   - the sweep's start (`handover_cfg`), and L6, a slice of the sweep
///     (`FusedSweepCoalesce.sweep_slice_impl`) as `k` events `ESweep`
///     (`slice_cfg`: `k` is the slice's step count, `SL.slice_count`), then
///     `EEnd` when the sweep is done (`end_cfg`).

module GC.Spec.Top.CodeFF

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.Run
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module Seq = FStar.Seq
module W = GC.Spec.Walk
module Ph = GC.Spec.Phase
module SA = GC.Spec.Allocator
module AP = GC.Spec.Allocator.Phase
module AC = GC.Spec.Allocator.Cursor
module FLA = GC.Spec.FreeList.Ascending
module FS = GC.Spec.FusedSweep
module FStep = GC.Spec.FusedSweep.Step
module SPI = GC.Spec.SweepPhase.Intrinsic
module SL = GC.Spec.SweepPhase.Slice
module FSw = GC.Spec.Top.FFSweep
module FC = GC.Spec.Top.FFComps
module FAO = GC.Spec.Top.FFAllocOk
module FB = GC.Spec.Top.FFBytes
module FF = GC.Spec.Top.FFFill
module CR = GC.Spec.Top.CodeRun
module CP = GC.Spec.Top.CodePages

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The configuration the code holds
/// ---------------------------------------------------------------------------

let fc : comps = FC.fc

let hof (x: config fc) : heap = x.w.cmaj
let sof (x: config fc) : ffst = x.ast

let xc (es: list event) : GTot (config fc) = CR.cur fc msize ywords es

let lo_ok (x: config fc) : prop = (sof x).lo == low (hof x)

let good (sty: style) (es: list event) : prop =
  run_ok fc sty msize ywords es /\ lo_ok (xc es) /\ (xc es).stopped == false

/// The phase record of `GC.Impl.Allocator`: its kind, and while sweeping its
/// cursor and caches.
let kind_of (ph: T.phase U64.t) : U64.t = match ph with T.Idle -> 0UL | T.Sweeping _ -> 1UL | T.Marking -> 2UL

let gl_ok (x: config fc) : Lemma (requires lo_ok x) (ensures gl (hof x) (sof x) == hof x)
  = set_low_self (hof x)

let components () : Lemma (components_ok fc) = FC.ff_components_ok ()

/// The shape of the phase, on the heap itself.
let shape_of (ph: T.phase U64.t) (g: heap) (fp: U64.t) : prop =
  match ph with
  | T.Idle -> ishape g fp
  | T.Marking -> mshape g fp
  | T.Sweeping c -> sshape g fp c

let good_inv (sty: style) (es: list event)
  : Lemma (requires good sty es)
          (ensures (let x = xc es in
                    shape_of x.ph (hof x) (sof x).fp /\
                    (match x.ph with
                     | T.Sweeping c -> SPI.sweep_inv_incremental (hof x) (sof x).fp c /\
                                       W.reaches (hof x) zero_addr (U64.v c)
                     | _ -> True)))
  = let x = xc es in
    components ();
    CR.point fc sty msize ywords es;
    gl_ok x;
    match x.ph with
    | T.Sweeping c ->
      reveal_opaque (`%sshape) (sshape (hof x) (sof x).fp c);
      SPI.sweep_inv_incremental_elim (hof x) (sof x).fp c
    | _ -> ()

/// What `Allocator.allocate` asks: while sweeping, the free list is
/// ascending.
let alloc_ready (sty: style) (es: list event)
  : Lemma (requires good sty es)
          (ensures (let x = xc es in Ph.Sweeping? (gph x.ph) ==> FLA.fl_ascending (hof x) (sof x).fp))
  = let x = xc es in
    good_inv sty es;
    match x.ph with
    | T.Sweeping c -> SPI.sweep_inv_incremental_elim (hof x) (sof x).fp c
    | _ -> ()

/// **One more event**: when allowed, a run, whose configuration is the step.
let snoc (sty: style) (es: list event) (e: event)
  : Lemma (requires good sty es /\ CR.allowed fc sty (xc es) e /\ lo_ok (step fc (xc es) e) /\
                    (step fc (xc es) e).stopped == false)
          (ensures good sty (L.append es [e]) /\ xc (L.append es [e]) == step fc (xc es) e)
  = components ();
    CR.snoc fc sty msize ywords es e

/// A collector event that is enabled is allowed.
let allowed_gc (sty: style) (es: list event) (e: event)
  : Lemma (requires good sty es /\ ~(is_mutator_event e) /\ enabled fc (xc es) e)
          (ensures CR.allowed fc sty (xc es) e)
  = components ();
    CR.point fc sty msize ywords es

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

/// **The initial configuration**: one blue block from `zero_addr` to the
/// end, its link 0, written on a zeroed heap.
let init_cfg (sty: style)
  : Lemma (ensures good sty [] /\
                   (let x = xc [] in
                    hof x == init_heap /\ (sof x).fp == init_fp /\ x.ph == T.Idle))
  = CR.nil_run fc sty msize ywords

/// ---------------------------------------------------------------------------
/// L5: allocation and its Fill
/// ---------------------------------------------------------------------------

/// The model's allocation is the Pulse allocator's.
let ffres_eq (x: config fc) (sz: M.size_t) (tag: M.tag_t)
  : Lemma (requires lo_ok x)
          (ensures ffres x.ph (hof x) (sof x) sz tag == AC.alloc_phase (hof x) (sof x).fp (gph x.ph) sz (tg tag))
  = gl_ok x

/// **No room**: nothing changes.
let alloc_none (sty: style) (es: list event) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires good sty es /\
                    (AC.alloc_phase (hof (xc es)) (sof (xc es)).fp (gph (xc es).ph) sz (tg tag)).SA.obj_out == 0UL)
          (ensures (let x = xc es in
                    let r = AC.alloc_phase (hof x) (sof x).fp (gph x.ph) sz (tg tag) in
                    step fc x (EAlloc sz tag vs) == x /\ lo_ok (step fc x (EAlloc sz tag vs)) /\
                    r.SA.heap_out == hof x /\ r.SA.fp_out == (sof x).fp))
  = let x = xc es in
    ffres_eq x sz tag;
    AP.alloc_at_fields (gph x.ph) (hof x) (sof x).fp sz (tg tag)

/// The Fill writes only the block's body.
#push-options "--fuel 1 --z3rlimit 40"
let rec fill_body (g: heap) (m i: nat) (vs: list M.value) (a: hp_addr)
  : Lemma (requires pos m + 8 + 8 * (i + L.length vs) <= heap_size /\
                    (U64.v a < pos m + 8 + 8 * i \/ U64.v a >= pos m + 8 + 8 * (i + L.length vs)))
          (ensures read_word (CP.fill_from g m i vs) a == read_word g a)
          (decreases vs)
  = match vs with
    | [] -> ()
    | v :: tl ->
      let p = hp (m + 1 + i) in
      read_write_different g p a (concv v);
      fill_body (CP.wr_field g m i v) m (i + 1) tl a
#pop-options

/// **An allocation**: the new block's first field at `o`, of `sz` fields;
/// the Fill writes them in order, and keeps the walk and every header.
#push-options "--z3rlimit 40"
let alloc_some (sty: style) (es: list event) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires good sty es /\ L.length vs == sz /\ tag <> M.infix_tag /\
                    (AC.alloc_phase (hof (xc es)) (sof (xc es)).fp (gph (xc es).ph) sz (tg tag)).SA.obj_out =!= 0UL)
          (ensures (let x = xc es in
                    let r = AC.alloc_phase (hof x) (sof x).fp (gph x.ph) sz (tg tag) in
                    let o = r.SA.obj_out in
                    let x' = step fc x (EAlloc sz tag vs) in
                    pos (maddr o) + 8 == U64.v o /\ U64.v o + 8 * sz <= heap_size /\
                    hof x' == CP.fill_from r.SA.heap_out (maddr o) 0 vs /\ (sof x').fp == r.SA.fp_out /\
                    x'.ph == x.ph /\ lo_ok x' /\
                    SPI.same_heads r.SA.heap_out (hof x')))
  = let x = xc es in
    let g = hof x in
    let fp = (sof x).fp in
    ffres_eq x sz tag;
    good_inv sty es;
    tg_v tag;
    FAO.ready_of x.ph g fp;
    FB.alloc_bytes (gph x.ph) g fp sz (tg tag);
    let r = AC.alloc_phase g fp (gph x.ph) sz (tg tag) in
    let o : obj_addr = r.SA.obj_out in
    let g' = r.SA.heap_out in
    obj_maddr g' o;
    CP.binit_fill g' x.w.crem (maddr o) 0 vs;
    CP.fill_low g' (maddr o) 0 vs;
    let g'' = CP.fill_from g' (maddr o) 0 vs in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (fill_body g' (maddr o) 0 vs));
    wosize_of_object_spec o g';
    assert (FF.body_only g' g'' o);
    FF.body_heads g' g'' o
#pop-options

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

/// **The sweep's start**: the cursor at `zero_addr`, whose derived caches
/// are the start's.
let handover_cfg (x: config fc)
  : Lemma (requires lo_ok x /\ T.Marking? x.ph)
          (ensures (let x' = step fc x EHandover in
                    hof x' == hof x /\ sof x' == sof x /\ x'.ph == T.Sweeping FS.sweep_start.FS.cursor /\
                    lo_ok x' /\ SPI.state_at (hof x) FS.sweep_start.FS.cursor == FS.sweep_start))
  = SPI.state_at_start (hof x)

/// ESweep, repeated.
let rec sweeps (k: nat) : list event = if k = 0 then [] else ESweep :: sweeps (k - 1)

#push-options "--fuel 1"
let sweeps_cons (k: nat) : Lemma (requires k > 0) (ensures sweeps k == ESweep :: sweeps (k - 1)) = ()
let sweeps_zero (_: unit) : Lemma (sweeps 0 == []) = ()
#pop-options

#push-options "--fuel 2"
let sweeps_split (es: list event) (k: nat)
  : Lemma (requires k > 0) (ensures L.append es (sweeps k) == L.append (L.append es [ESweep]) (sweeps (k - 1)))
  = L.append_assoc es [ESweep] (sweeps (k - 1))
#pop-options

/// One sweep event: a step of the fused sweep from the derived state.
#push-options "--z3rlimit 40"
let sweep_one (sty: style) (es: list event)
  : Lemma (requires good sty es /\ T.Sweeping? (xc es).ph /\ not (SPI.sweep_done (T.Sweeping?._0 (xc es).ph)) /\
                    FS.can_sweep (hof (xc es)) (SPI.state_at (hof (xc es)) (T.Sweeping?._0 (xc es).ph)))
          (ensures (let x = xc es in
                    let c = T.Sweeping?._0 x.ph in
                    let (g', fp', st') = FS.sweep_step (hof x) (sof x).fp (SPI.state_at (hof x) c) in
                    let x' = xc (L.append es [ESweep]) in
                    good sty (L.append es [ESweep]) /\
                    hof x' == g' /\ (sof x').fp == fp' /\ x'.ph == T.Sweeping st'.FS.cursor /\
                    st' == SPI.state_at g' st'.FS.cursor))
  = let x = xc es in
    let c = T.Sweeping?._0 x.ph in
    good_inv sty es;
    gl_ok x;
    FStep.sweep_inv_incremental_step (hof x) (sof x).fp c;
    allowed_gc sty es ESweep;
    snoc sty es ESweep
#pop-options

/// **L6: a slice of the sweep is `k` events `ESweep`**: the slice from the
/// derived state is `slice_count` steps, each one enabled (the sweep is not
/// done before it).
/// The configuration a slice from `es` reaches.
let at_slice (sty: style) (es: list event) (g: heap) (fp: U64.t) (st: FS.sweep_state) : prop =
  good sty es /\ hof (xc es) == g /\ (sof (xc es)).fp == fp /\ (xc es).ph == T.Sweeping st.FS.cursor

/// One step of the slice's induction: the next event `ESweep`.
#push-options "--z3rlimit 40"
let slice_step (sty: style) (es: list event) (c: U64.t)
  : Lemma (requires good sty es /\ (xc es).ph == T.Sweeping c /\ not (SPI.sweep_done c))
          (ensures (let x = xc es in
                    let st = SPI.state_at (hof x) c in
                    FS.can_sweep (hof x) st /\
                    (let (g1, fp1, st1) = FS.sweep_step (hof x) (sof x).fp st in
                     at_slice sty (L.append es [ESweep]) g1 fp1 st1 /\ st1 == SPI.state_at g1 st1.FS.cursor /\
                     U64.v st1.FS.cursor > U64.v c)))
  = let x = xc es in
    good_inv sty es;
    FStep.sweep_inv_incremental_step (hof x) (sof x).fp c;
    sweep_one sty es
#pop-options

#push-options "--fuel 1 --z3rlimit 40"
let rec slice_go (sty: style) (es: list event) (c0: U64.t) (budget: nat) (c: U64.t)
  : Lemma (requires good sty es /\ (xc es).ph == T.Sweeping c)
          (ensures (let x = xc es in
                    let st = SPI.state_at (hof x) c in
                    let (g', fp', st') = SL.slice_from (hof x) (sof x).fp st c0 budget in
                    at_slice sty (L.append es (sweeps (SL.slice_count (hof x) (sof x).fp st c0 budget))) g' fp' st'))
          (decreases (heap_size - U64.v c))
  = let x = xc es in
    let g = hof x in
    let fp = (sof x).fp in
    let st = SPI.state_at g c in
    SL.slice_from_unfold g fp st c0 budget;
    good_inv sty es;
    SPI.sweep_inv_incremental_elim g fp c;
    if SPI.sweep_done st.FS.cursor || not (FS.can_sweep g st) || SL.swept_words c0 st >= budget then begin
      L.append_l_nil es;
      sweeps_zero ()
    end
    else begin
      slice_step sty es c;
      let es1 = L.append es [ESweep] in
      let (g1, fp1, st1) = FS.sweep_step g fp st in
      slice_go sty es1 c0 budget st1.FS.cursor;
      let k = SL.slice_count g fp st c0 budget in
      assert (k == 1 + SL.slice_count g1 fp1 st1 c0 budget);
      sweeps_split es k;
      assert (L.append es (sweeps k) == L.append es1 (sweeps (k - 1)));
      assert (SL.slice_from g fp st c0 budget == SL.slice_from g1 fp1 st1 c0 budget);
      assert (hof (xc es1) == g1 /\ SPI.state_at g1 st1.FS.cursor == st1)
    end
#pop-options

/// **A slice**, from the code's state.
let slice_cfg (sty: style) (es: list event) (budget: nat)
  : Lemma (requires good sty es /\ T.Sweeping? (xc es).ph)
          (ensures (let x = xc es in
                    let c = T.Sweeping?._0 x.ph in
                    let st = SPI.state_at (hof x) c in
                    let (g', fp', st') = SL.sweep_slice (hof x) (sof x).fp st budget in
                    let es' = L.append es (sweeps (SL.slice_count (hof x) (sof x).fp st c budget)) in
                    good sty es' /\ hof (xc es') == g' /\ (sof (xc es')).fp == fp' /\
                    (xc es').ph == T.Sweeping st'.FS.cursor /\
                    st' == SPI.state_at g' st'.FS.cursor /\ W.reaches g' zero_addr (U64.v st'.FS.cursor) /\
                    U64.v st'.FS.cursor <= heap_size))
  = let x = xc es in
    let c = T.Sweeping?._0 x.ph in
    good_inv sty es;
    slice_go sty es c budget c;
    SPI.state_at_start (hof x);
    SL.sweep_slice_phase (hof x) (sof x).fp c budget;
    let (g', fp', st') = SL.sweep_slice (hof x) (sof x).fp (SPI.state_at (hof x) c) budget in
    SPI.sweep_inv_incremental_elim g' fp' st'.FS.cursor

/// **The sweep's end**: when the cursor is done, `EEnd`, the phase only.
let end_cfg (sty: style) (es: list event)
  : Lemma (requires good sty es /\ T.Sweeping? (xc es).ph /\ SPI.sweep_done (T.Sweeping?._0 (xc es).ph))
          (ensures good sty (L.append es [EEnd]) /\
                   (let x' = xc (L.append es [EEnd]) in
                    hof x' == hof (xc es) /\ sof x' == sof (xc es) /\ x'.ph == T.Idle))
  = allowed_gc sty es EEnd;
    snoc sty es EEnd

/// ---------------------------------------------------------------------------
/// The program's root events
/// ---------------------------------------------------------------------------

let roots_cfg (x: config fc) (rs: list M.value)
  : Lemma (requires lo_ok x)
          (ensures (let x' = step fc x (ERoots rs) in hof x' == hof x /\ sof x' == sof x /\ x'.ph == x.ph /\ lo_ok x'))
  = ()

let read_cfg (x: config fc) (o i: nat)
  : Lemma (requires lo_ok x)
          (ensures (let x' = step fc x (ERead (M.Major o) i) in
                    hof x' == hof x /\ sof x' == sof x /\ x'.ph == x.ph /\ lo_ok x'))
  = ()
