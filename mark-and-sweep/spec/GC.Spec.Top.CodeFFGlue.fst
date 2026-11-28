/// ---------------------------------------------------------------------------
/// GC.Spec.Top.CodeFFGlue - what the first-fit generational glue needs
/// besides, event by event
/// ---------------------------------------------------------------------------
///
/// Design doc §18, plan step 1.  The glue `GC.Impl.FFGen` keeps, beside
/// the heap, the free list's head and the phase record: the nursery, the
/// table of remembered slots with repeats (`CodeFFDup.tbl_d`), every
/// remembered slot a scannable field of a kept block (`CodeFFMinor.rem_ok`)
/// and akhil's mark state at the model's scan (`CodeFFGen.spof`).  Here,
/// for each event the glue performs without a collection: the run one
/// event longer is the step (`snoc_eq`), and what it keeps of those:
///   - `leave_g`: the events that leave the remembered set;
///   - `sweep_side`: a slice of the sweep, `k` events `ESweep`;
///   - `alloc_g`, `fill_step`, `fill_skip`: an allocation and its Fill, the
///     Fill's young fields appended to the table, fresh slots;
///   - `write_tbl`: a major write, the slot appended to the table exactly
///     when akhil's barrier says to remember it (and the block is
///     scannable);
///   - `ywrite_g`, `yalloc_g`: the nursery's writes and allocation.

module GC.Spec.Top.CodeFFGlue

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.Run
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Ph = GC.Spec.Phase
module MS = GC.Gen.MarkState
module SPI = GC.Spec.SweepPhase.Intrinsic
module SL = GC.Spec.SweepPhase.Slice
module FS = GC.Spec.FusedSweep
module FStep = GC.Spec.FusedSweep.Step
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Y = GC.Spec.Top.Young
module BB = GC.Spec.Top.ByteBarrier
module CF = GC.Spec.Top.CodeFF
module CR = GC.Spec.Top.CodeRun
module CM = GC.Spec.Top.CodeMinor
module G = GC.Spec.Top.CodeFFGen
module FMi = GC.Spec.Top.CodeFFMinor
module Dup = GC.Spec.Top.CodeFFDup
module FWr = GC.Spec.Top.CodeFFWrite
module FMk = GC.Spec.Top.CodeFFMark
module GBr = GC.Gen.Barrier

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// One more event
/// ---------------------------------------------------------------------------

/// **The run one event longer is the step.**
let snoc_eq (sty: style) (es: list event) (e: event)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) e)
          (ensures CF.xc (L.append es [e]) == step CF.fc (CF.xc es) e)
  = CF.components ();
    CR.snoc CF.fc sty msize ywords es e

/// **An event that leaves the remembered set**, when the step keeps the low
/// bytes and does not stop the run.
let leave_g (sty: style) (es: list event) (e: event)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) e /\ FMi.rem_ok (CF.xc es) /\
                    FMi.leaves_rem e /\ CF.lo_ok (step CF.fc (CF.xc es) e) /\
                    (step CF.fc (CF.xc es) e).stopped == false)
          (ensures CF.good sty (L.append es [e]) /\ CF.xc (L.append es [e]) == step CF.fc (CF.xc es) e /\
                   FMi.rem_ok (CF.xc (L.append es [e])) /\
                   (CF.xc (L.append es [e])).w.crem == (CF.xc es).w.crem)
  = CF.snoc sty es e;
    FMi.rem_leave sty es e

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

/// One `ESweep`: the nursery, the remembered set and the mark's state stay.
#push-options "--z3rlimit 40"
let sweep_one_side (sty: style) (es: list event)
  : Lemma (requires CF.good sty es /\ T.Sweeping? (CF.xc es).ph /\
                    not (SPI.sweep_done (T.Sweeping?._0 (CF.xc es).ph)) /\ FMi.rem_ok (CF.xc es))
          (ensures (let x = CF.xc es in
                    let x' = CF.xc (L.append es [ESweep]) in
                    x'.w.cyng == x.w.cyng /\ x'.w.crem == x.w.crem /\ x'.ms == x.ms /\ FMi.rem_ok x'))
  = let x = CF.xc es in
    let c = T.Sweeping?._0 x.ph in
    CF.good_inv sty es;
    CF.gl_ok x;
    FStep.sweep_inv_incremental_step (CF.hof x) (CF.sof x).fp c;
    CF.allowed_gc sty es ESweep;
    snoc_eq sty es ESweep;
    FMi.rem_leave sty es ESweep
#pop-options

/// **A slice of the sweep** (`CodeFF.slice_go`'s induction): the nursery,
/// the remembered set and the mark's state stay.
#push-options "--fuel 1 --z3rlimit 40"
let rec sweep_side (sty: style) (es: list event) (c0: U64.t) (budget: nat) (c: U64.t)
  : Lemma (requires CF.good sty es /\ (CF.xc es).ph == T.Sweeping c /\ FMi.rem_ok (CF.xc es))
          (ensures (let x = CF.xc es in
                    let st = SPI.state_at (CF.hof x) c in
                    let x' = CF.xc (L.append es (CF.sweeps (SL.slice_count (CF.hof x) (CF.sof x).fp st c0 budget))) in
                    x'.w.cyng == x.w.cyng /\ x'.w.crem == x.w.crem /\ x'.ms == x.ms /\ FMi.rem_ok x'))
          (decreases (heap_size - U64.v c))
  = let x = CF.xc es in
    let g = CF.hof x in
    let fp = (CF.sof x).fp in
    let st = SPI.state_at g c in
    SL.slice_from_unfold g fp st c0 budget;
    CF.good_inv sty es;
    SPI.sweep_inv_incremental_elim g fp c;
    if SPI.sweep_done st.FS.cursor || not (FS.can_sweep g st) || SL.swept_words c0 st >= budget then begin
      L.append_l_nil es;
      CF.sweeps_zero ()
    end
    else begin
      CF.slice_step sty es c;
      sweep_one_side sty es;
      let es1 = L.append es [ESweep] in
      let (g1, fp1, st1) = FS.sweep_step g fp st in
      sweep_side sty es1 c0 budget st1.FS.cursor;
      let k = SL.slice_count g fp st c0 budget in
      assert (k == 1 + SL.slice_count g1 fp1 st1 c0 budget);
      CF.sweeps_split es k;
      assert (L.append es (CF.sweeps k) == L.append es1 (CF.sweeps (k - 1)));
      assert (CF.hof (CF.xc es1) == g1 /\ SPI.state_at g1 st1.FS.cursor == st1)
    end
#pop-options

/// **A slice from the code's state**, and the sweep's end.
let slice_side (sty: style) (es: list event) (budget: nat)
  : Lemma (requires CF.good sty es /\ T.Sweeping? (CF.xc es).ph /\ FMi.rem_ok (CF.xc es))
          (ensures (let x = CF.xc es in
                    let c = T.Sweeping?._0 x.ph in
                    let x' = CF.xc (L.append es (CF.sweeps (SL.slice_count (CF.hof x) (CF.sof x).fp
                                                              (SPI.state_at (CF.hof x) c) c budget))) in
                    x'.w.cyng == x.w.cyng /\ x'.w.crem == x.w.crem /\ x'.ms == x.ms /\ FMi.rem_ok x'))
  = let x = CF.xc es in
    sweep_side sty es (T.Sweeping?._0 x.ph) budget (T.Sweeping?._0 x.ph)

let end_side (sty: style) (es: list event)
  : Lemma (requires CF.good sty es /\ T.Sweeping? (CF.xc es).ph /\ SPI.sweep_done (T.Sweeping?._0 (CF.xc es).ph) /\
                    FMi.rem_ok (CF.xc es))
          (ensures (let x = CF.xc es in
                    let x' = CF.xc (L.append es [EEnd]) in
                    x'.w.cyng == x.w.cyng /\ x'.w.crem == x.w.crem /\ x'.ms == x.ms /\ FMi.rem_ok x'))
  = CF.allowed_gc sty es EEnd;
    snoc_eq sty es EEnd;
    FMi.rem_leave sty es EEnd

/// **The hand-over**: the nursery, the remembered set and the mark's state
/// stay.
let handover_side (sty: style) (es: list event)
  : Lemma (requires CF.good sty es /\ T.Marking? (CF.xc es).ph /\ T.mark_done (mj (CF.xc es)) /\
                    None? (scan_of (CF.xc es)) /\ FMi.rem_ok (CF.xc es))
          (ensures (let x = CF.xc es in
                    let x' = CF.xc (L.append es [EHandover]) in
                    CF.good sty (L.append es [EHandover]) /\
                    x'.w.cyng == x.w.cyng /\ x'.w.crem == x.w.crem /\ x'.ms == x.ms /\ FMi.rem_ok x' /\
                    CF.hof x' == CF.hof x /\ CF.sof x' == CF.sof x /\ x'.ph == T.Sweeping FS.sweep_start.FS.cursor))
  = let x = CF.xc es in
    CF.handover_cfg x;
    CF.allowed_gc sty es EHandover;
    CF.snoc sty es EHandover;
    FMi.rem_leave sty es EHandover

/// ---------------------------------------------------------------------------
/// Allocation and its Fill
/// ---------------------------------------------------------------------------

/// The slots the Fill found so far are fields of `m` below `k`.
#push-options "--fuel 2 --ifuel 1"
let rec ypre_lt (m: nat) (sc: bool) (ws: Seq.seq U64.t) (k: nat) (o j: nat)
  : Lemma (ensures L.memP (o, j) (CM.ypre m sc ws k) ==> o == m /\ j < k) (decreases k)
  = if k = 0 || k > Seq.length ws then ()
    else begin
      ypre_lt m sc ws (k - 1) o j;
      CM.ypre_step m sc ws (k - 1);
      L.append_memP (CM.ypre m sc ws (k - 1))
        (if sc && is_young_w (Seq.index ws (k - 1)) then [(m, k - 1)] else []) (o, j);
      ()
    end
#pop-options

/// No field of the new block is remembered before its Fill.
#push-options "--z3rlimit 40"
let fill_fresh (sty: style) (es: list event) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) (EAlloc sz tag vs) /\ FMi.rem_ok (CF.xc es) /\
                    (let x = CF.xc es in
                     (AC.alloc_phase (CF.hof x) (CF.sof x).fp (gph x.ph) sz (tg tag)).SA.obj_out =!= 0UL))
          (ensures (let x = CF.xc es in
                    let r = AC.alloc_phase (CF.hof x) (CF.sof x).fp (gph x.ph) sz (tg tag) in
                    forall (j: nat). ~(L.memP (maddr r.SA.obj_out, j) x.w.crem)))
  = let x = CF.xc es in
    let r = AC.alloc_phase (CF.hof x) (CF.sof x).fp (gph x.ph) sz (tg tag) in
    let m = maddr r.SA.obj_out in
    let e = EAlloc sz tag vs in
    let x' = step CF.fc x e in
    CF.components ();
    CR.step_facts CF.fc sty msize ywords es e;
    CF.ffres_eq x sz tag;
    CF.alloc_some sty es sz tag vs;
    FMi.new_block sty es sz tag;
    assert (in_use_c x m == false /\ kept x' m)
#pop-options

/// ---------------------------------------------------------------------------
/// The table, its slot list hidden
/// ---------------------------------------------------------------------------

/// **The table with repeats**, for some list of slots (the glue does not
/// name it).
let tbl_e (tv: Seq.seq U64.t) (n: nat) (rem: list M.slot) : prop =
  exists (sl: list M.slot). Dup.tbl_d tv n sl rem

let tbl_e_nil (tv: Seq.seq U64.t) : Lemma (tbl_e tv 0 []) = Dup.tbl_d_nil tv

/// The table's slots are the remembered set's, with repeats.
let tbl_e_ok (tv: Seq.seq U64.t) (n: nat) (rem: list M.slot)
  : Lemma (requires tbl_e tv n rem) (ensures exists (sl: list M.slot). Dup.tbl_d tv n sl rem)
  = ()

/// **Appending a slot**: the set grows by it unless it is there already.
let tbl_e_snoc (tv: Seq.seq U64.t) (n: nat) (rem: list M.slot) (s: M.slot)
  : Lemma (requires tbl_e tv n rem /\ n < Seq.length tv)
          (ensures tbl_e (Seq.upd tv n (CM.slot_word s)) (n + 1) (if L.mem s rem then rem else L.append rem [s]))
  = eliminate exists (sl: list M.slot). Dup.tbl_d tv n sl rem
    with Dup.tbl_d_snoc tv n sl rem s

let tbl_e_fresh (tv: Seq.seq U64.t) (n: nat) (rem: list M.slot) (s: M.slot)
  : Lemma (requires tbl_e tv n rem /\ n < Seq.length tv /\ ~(L.memP s rem))
          (ensures tbl_e (Seq.upd tv n (CM.slot_word s)) (n + 1) (L.append rem [s]))
  = eliminate exists (sl: list M.slot). Dup.tbl_d tv n sl rem
    with Dup.tbl_d_fresh tv n sl rem s

/// One field of the Fill: a young field of a scannable block is appended
/// to the table, fresh.
#push-options "--fuel 1 --z3rlimit 40"
let fill_step (rem: list M.slot) (tv: Seq.seq U64.t) (n: nat) (m: nat) (sc: bool) (ws: Seq.seq U64.t) (k: nat)
  : Lemma (requires (forall (j: nat). ~(L.memP (m, j) rem)) /\ k < Seq.length ws /\ n < Seq.length tv /\
                    tbl_e tv n (L.append rem (CM.ypre m sc ws k)) /\
                    sc /\ is_young_w (Seq.index ws k))
          (ensures tbl_e (Seq.upd tv n (CM.slot_word (m, k))) (n + 1) (L.append rem (CM.ypre m sc ws (k + 1))))
  = CM.ypre_step m sc ws k;
    ypre_lt m sc ws k m k;
    L.append_memP rem (CM.ypre m sc ws k) (m, k);
    tbl_e_fresh tv n (L.append rem (CM.ypre m sc ws k)) (m, k);
    L.append_assoc rem (CM.ypre m sc ws k) [(m, k)]

let fill_skip (rem: list M.slot) (tv: Seq.seq U64.t) (n: nat) (m: nat) (sc: bool) (ws: Seq.seq U64.t) (k: nat)
  : Lemma (requires k < Seq.length ws /\ tbl_e tv n (L.append rem (CM.ypre m sc ws k)) /\
                    ~(sc && is_young_w (Seq.index ws k)))
          (ensures tbl_e tv n (L.append rem (CM.ypre m sc ws (k + 1))))
  = CM.ypre_step m sc ws k;
    L.append_l_nil (CM.ypre m sc ws k)

let fill_start (rem: list M.slot) (tv: Seq.seq U64.t) (n: nat) (m: nat) (sc: bool) (ws: Seq.seq U64.t)
  : Lemma (requires tbl_e tv n rem)
          (ensures tbl_e tv n (L.append rem (CM.ypre m sc ws 0)))
  = L.append_l_nil rem

let fill_end (rem: list M.slot) (tv: Seq.seq U64.t) (n: nat) (m: nat) (sc: bool) (ws: Seq.seq U64.t)
  : Lemma (requires tbl_e tv n (L.append rem (CM.ypre m sc ws (Seq.length ws))))
          (ensures tbl_e tv n (L.append rem (CM.ynew_s m sc ws 0)))
  = CM.ypre_len m sc ws
#pop-options

/// **`EAlloc`**: the longer run is the step, the nursery and the mark's
/// state stay, the mark cache is kept; with room, the remembered set grows
/// by the Fill's young fields (the code's `ynew_s`), none remembered
/// before.
#push-options "--z3rlimit 40"
let alloc_g (sty: style) (es: list event) (wz: M.size_t) (tag: M.tag_t) (vs: list M.value) (ws: Seq.seq U64.t)
    (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) (EAlloc wz tag vs) /\ FMi.rem_ok (CF.xc es) /\
                    tag < 256 /\ wz >= 1 /\ Seq.length ws == wz /\
                    (forall (i: nat). i < wz ==> Seq.index ws i == concv (L.index vs i)) /\
                    MS.mark_cache_ok (CF.hof (CF.xc es)) (gph (CF.xc es).ph) st ov p)
          (ensures (let x = CF.xc es in
                    let r = AC.alloc_phase (CF.hof x) (CF.sof x).fp (gph x.ph) wz (tg tag) in
                    let es' = L.append es [EAlloc wz tag vs] in
                    let x' = CF.xc es' in
                    x' == step CF.fc x (EAlloc wz tag vs) /\
                    x'.w.cyng == x.w.cyng /\ x'.ms == x.ms /\ x'.ph == x.ph /\ FMi.rem_ok x' /\
                    MS.mark_cache_ok (CF.hof x') (gph x'.ph) st ov p /\
                    (r.SA.obj_out == 0UL ==> x'.w.crem == x.w.crem) /\
                    (r.SA.obj_out =!= 0UL ==>
                       (forall (j: nat). ~(L.memP (maddr r.SA.obj_out, j) x.w.crem)) /\
                       x'.w.crem == L.append x.w.crem (CM.ynew_s (maddr r.SA.obj_out) (tag < 251) ws 0))))
  = let x = CF.xc es in
    let e = EAlloc wz tag vs in
    let r = AC.alloc_phase (CF.hof x) (CF.sof x).fp (gph x.ph) wz (tg tag) in
    snoc_eq sty es e;
    FMk.alloc_cache sty es wz tag vs st ov p;
    if r.SA.obj_out = 0UL then CF.alloc_none sty es wz tag vs
    else begin
      CF.alloc_some sty es wz tag vs;
      fill_fresh sty es wz tag vs;
      FMi.alloc_rem sty es wz tag vs;
      CM.ynew_code r.SA.heap_out (maddr r.SA.obj_out) 0 vs ws
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The barrier's table
/// ---------------------------------------------------------------------------

/// **A major write**: the slot appended to the table exactly when the block
/// is scannable and akhil's barrier says to remember it; the table is then
/// the model's remembered set with repeats.
#push-options "--z3rlimit 40"
let write_tbl (sty: style) (es: list event) (o i: nat) (v: M.value) (tv: Seq.seq U64.t) (n: nat)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) (EWrite (M.Major o) i v) /\
                    FMi.rem_ok (CF.xc es) /\ tbl_e tv n (CF.xc es).w.crem /\ n < Seq.length tv)
          (ensures (let x = CF.xc es in
                    let g = CF.hof x in
                    pos o + 8 < heap_size /\ pos (o + 1 + i) < heap_size /\
                    (let a = hp (o + 1 + i) in
                     let x' = step CF.fc x (EWrite (M.Major o) i v) in
                     let rc = scannable g (obj_of o) && GBr.modify_records g a (concv v) in
                     CM.slot_word (o, i) == a /\ FMi.rem_ok x' /\
                     (rc ==> tbl_e (Seq.upd tv n a) (n + 1) x'.w.crem) /\
                     (not rc ==> tbl_e tv n x'.w.crem))))
  = let x = CF.xc es in
    let g = CF.hof x in
    FMi.write_block sty es o i v;
    FWr.blk_facts g o i;
    CM.slot_word_hp o i;
    FMi.write_rem sty es o i v;
    if scannable g (obj_of o) then begin
      FMi.records_agree sty es o i v;
      tbl_e_snoc tv n x.w.crem (o, i)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The nursery's events
/// ---------------------------------------------------------------------------

/// **A young write**: the run one event longer is the step; the remembered
/// set stays.
let ywrite_g (sty: style) (es: list event) (o i: nat) (v: M.value)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) (EWrite (M.Young o) i v) /\ FMi.rem_ok (CF.xc es))
          (ensures FMi.rem_ok (CF.xc (L.append es [EWrite (M.Young o) i v])))
  = snoc_eq sty es (EWrite (M.Young o) i v);
    FMi.rem_leave sty es (EWrite (M.Young o) i v)

/// **A young allocation**: a bump allocation in the nursery; everything else
/// stays.
#push-options "--z3rlimit 40"
let yalloc_g (sty: style) (es: list event) (wz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\
                    style_ok sty (CF.xc es) (EYoungAlloc wz tag vs) /\ mutator_ok (CF.xc es) (EYoungAlloc wz tag vs) /\
                    wz <= GC.Gen.Base.max_young_wosize /\ U64.v (CF.xc es).w.cyng.bump % 8 == 0 /\
                    U64.v (CF.xc es).w.cyng.bump + 8 * (wz + 1) <= GC.Gen.Base.minor_heap_size)
          (ensures (Y.msz ();
                    let x = CF.xc es in
                    let b = x.w.cyng.bump in
                    let d1 = Y.mwrite x.w.cyng.data (U64.v b) (enc_hdr (Y.white_hdr wz tag)) in
                    let d2 = Y.write_fields d1 (U64.v b + 8) vs in
                    let b2 = U64.uint_to_t (U64.v b + 8 * (wz + 1)) in
                    let es' = L.append es [EYoungAlloc wz tag vs] in
                    let x' = CF.xc es' in
                    CF.good sty es' /\ x'.w.cyng == ({ data = d2; bump = b2 } <: minor_state) /\
                    x'.w.crem == x.w.crem /\ FMi.rem_ok x' /\ x'.ms == x.ms /\
                    CF.hof x' == CF.hof x /\ CF.sof x' == CF.sof x /\ x'.ph == x.ph))
  = let x = CF.xc es in
    let e = EYoungAlloc wz tag vs in
    assert (Some? (Y.yalloc x.w.cyng wz tag vs));
    assert (CR.allowed CF.fc sty x e);
    CF.snoc sty es e;
    FMi.rem_leave sty es e
#pop-options

/// **The program's roots and reads**: everything but the roots stays.
let roots_g (sty: style) (es: list event) (e: event)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) e /\ FMi.rem_ok (CF.xc es) /\
                    (ERoots? e \/ ERead? e))
          (ensures (let x = CF.xc es in
                    let x' = CF.xc (L.append es [e]) in
                    CF.good sty (L.append es [e]) /\ FMi.rem_ok x' /\
                    CF.hof x' == CF.hof x /\ CF.sof x' == CF.sof x /\ x'.ph == x.ph /\ x'.ms == x.ms /\
                    x'.w.cyng == x.w.cyng /\ x'.w.crem == x.w.crem))
  = let x = CF.xc es in
    CF.gl_ok x;
    leave_g sty es e

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

/// **The initial configuration**: the empty nursery, no slot remembered,
/// nothing being scanned.
#push-options "--fuel 1"
let init_g (sty: style)
  : Lemma (CF.good sty [] /\
           (let x = CF.xc [] in
            CF.hof x == init_heap /\ (CF.sof x).fp == init_fp /\ x.ph == T.Idle /\
            x.w.cyng == ({ data = Seq.create GC.Gen.Base.minor_heap_size 0uy; bump = 0UL } <: minor_state) /\
            x.w.crem == [] /\ scan_of x == None /\ FMi.rem_ok x))
  = CF.init_cfg sty;
    CF.components ();
    CR.nil_run CF.fc sty msize ywords;
    let x = CF.xc [] in
    assert (x == init_config CF.fc msize ywords);
    assert (x.w.cyng == Y.yinit ywords);
    let ms = minor_init (Seq.create GC.Gen.Base.minor_heap_size 0uy) in
    U64.v_inj ms.bump 0UL;
    assert (ms == ({ data = ms.data; bump = ms.bump } <: minor_state));
    FMk.bmark_fc ();
    FMi.rem_nil x
#pop-options

/// ---------------------------------------------------------------------------
/// The mark slice
/// ---------------------------------------------------------------------------

module S = GC.Spec.MarkPhase.Slice
module MP = GC.Spec.MarkPhase

/// The events of a slice that left the heap `g2` at the position `sp2`:
/// `ESlice` of its moves, none when it made no move.
let slice1 (es: list event) (g2: heap) (sp2: MP.scan_pos) : GTot (list event) =
  let mvs = FMk.slice_mvs es g2 sp2 in
  if Cons? mvs then L.append es [ESlice mvs] else es

/// **A slice of akhil's mark**: the run, its heap and position the slice's;
/// the nursery and the remembered set stay.
#push-options "--z3rlimit 40"
let slice_g (sty: style) (es: list event) (g2: heap) (sp2: MP.scan_pos)
  : Lemma (requires CF.good sty es /\ T.Marking? (CF.xc es).ph /\ FMi.rem_ok (CF.xc es) /\
                    S.mark_steps (CF.hof (CF.xc es)) (G.spof (scan_of (CF.xc es))) g2 sp2)
          (ensures (let x = CF.xc es in
                    let x1 = CF.xc (slice1 es g2 sp2) in
                    CF.good sty (slice1 es g2 sp2) /\ CF.hof x1 == g2 /\ G.spof (scan_of x1) == sp2 /\
                    x1.ph == x.ph /\ CF.sof x1 == CF.sof x /\ x1.w.cyng == x.w.cyng /\
                    x1.w.crem == x.w.crem /\ FMi.rem_ok x1))
  = FMk.slice_cfg sty es g2 sp2;
    let mvs = FMk.slice_mvs es g2 sp2 in
    if Cons? mvs then begin
      snoc_eq sty es (ESlice mvs);
      FMi.rem_leave sty es (ESlice mvs)
    end
#pop-options

/// **The hand-over after a slice that ended marking**: the cache off, nothing
/// grey.
let handover_g (sty: style) (es: list event) (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos)
  : Lemma (requires CF.good sty es /\ T.Marking? (CF.xc es).ph /\ FMi.rem_ok (CF.xc es) /\ MS.cache_off st ov p /\
                    GC.Spec.Mark.noGreyObjects (CF.hof (CF.xc es)) /\ MS.scan_of p == G.spof (scan_of (CF.xc es)))
          (ensures (let x = CF.xc es in
                    let x' = CF.xc (L.append es [EHandover]) in
                    CF.good sty (L.append es [EHandover]) /\
                    x'.w.cyng == x.w.cyng /\ x'.w.crem == x.w.crem /\ FMi.rem_ok x' /\
                    CF.hof x' == CF.hof x /\ CF.sof x' == CF.sof x /\ x'.ph == T.Sweeping FS.sweep_start.FS.cursor /\
                    G.spof (scan_of x') == MP.scan_none /\
                    MS.mark_cache_ok (CF.hof x') (gph x'.ph) st ov p /\ MS.scan_of p == MP.scan_none /\
                    SPI.state_at (CF.hof x) FS.sweep_start.FS.cursor == FS.sweep_start))
  = let x = CF.xc es in
    FMk.handover_ready sty es st ov p;
    handover_side sty es;
    CF.handover_cfg x;
    FMk.bmark_fc ();
    FMk.handover_cache (CF.hof x) FS.sweep_start.FS.cursor st ov p

/// The table's length is within the array.
let tbl_e_len (tv: Seq.seq U64.t) (n: nat) (rem: list M.slot)
  : Lemma (requires tbl_e tv n rem) (ensures n <= Seq.length tv)
  = ()

/// ---------------------------------------------------------------------------
/// The barrier
/// ---------------------------------------------------------------------------

/// **A major write, as the code's barrier performs it**: the heap, the mark
/// cache with the stack and flag the code leaves, the table (the slot
/// appended exactly when the block is scannable and akhil's barrier says to
/// remember it), and the rest unchanged.
#push-options "--z3rlimit 40"
let write_g (sty: style) (es: list event) (o i: nat) (v: M.value) (tv: Seq.seq U64.t) (n: nat)
    (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos) (cap: nat)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) (EWrite (M.Major o) i v) /\
                    FMi.rem_ok (CF.xc es) /\ tbl_e tv n (CF.xc es).w.crem /\ n < Seq.length tv /\
                    MS.mark_cache_ok (CF.hof (CF.xc es)) (gph (CF.xc es).ph) st ov p /\ Seq.length st <= cap)
          (ensures (let x = CF.xc es in
                    let g = CF.hof x in
                    pos o + 8 < heap_size /\ pos (o + 1 + i) < heap_size /\
                    (let a = hp (o + 1 + i) in
                     let dk = T.Marking? x.ph && scannable g (obj_of o) in
                     let es' = L.append es [EWrite (M.Major o) i v] in
                     let x' = CF.xc es' in
                     let rc = scannable g (obj_of o) && GBr.modify_records g a (concv v) in
                     U64.v a == U64.v (obj_of o) + 8 * i /\ CF.good sty es' /\
                     CF.hof x' == FWr.code_heap dk g st cap a (concv v) /\
                     CF.sof x' == CF.sof x /\ x'.ph == x.ph /\ x'.ms == x.ms /\ x'.w.cyng == x.w.cyng /\
                     FMi.rem_ok x' /\
                     MS.mark_cache_ok (CF.hof x') (gph x.ph) (FWr.code_stack dk g st cap a) (FWr.code_ov dk st ov cap) p /\
                     (~(T.Marking? x.ph) ==> SPI.same_heads g (CF.hof x')) /\
                     (rc ==> tbl_e (Seq.upd tv n a) (n + 1) x'.w.crem) /\
                     (not rc ==> tbl_e tv n x'.w.crem))))
  = FWr.write_major sty es o i v st ov p cap;
    write_tbl sty es o i v tv n;
    snoc_eq sty es (EWrite (M.Major o) i v)
#pop-options

/// ---------------------------------------------------------------------------
/// The minor collection, on the table with its slot list hidden
/// ---------------------------------------------------------------------------

module C = GC.Gen.Cheney
module CB = GC.Gen.CheneyBFS
module GP = GC.Gen.Promote
module FAO = GC.Spec.Top.FFAllocOk
module FA = GC.Gen.ForwardingArray
module LV = GC.Spec.Top.PagesLive
module BM = GC.Spec.Top.ByteMark

/// akhil's precondition on the glue's roots (`CodeFFDup.minor_pre_d`).
let minor_pre_e (sty: style) (es: list event) (tv: Seq.seq U64.t) (n: nat) (farr: Seq.seq U64.t)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_e tv n (CF.xc es).w.crem /\
                    Seq.length farr == FA.fwd_array_size /\
                    (forall (i: nat). i < Seq.length farr ==> Seq.index farr i == 0UL) /\
                    minor_guards_complete (CF.xc es).w.cyng /\ minor_infix_wf (CF.xc es).w.cyng)
          (ensures (let x = CF.xc es in
                    FMi.pre_with (gph x.ph) (FAO.ffree_of x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp
                      (Dup.rsd x tv n) farr tv n))
  = eliminate exists (sl: list M.slot). Dup.tbl_d tv n sl (CF.xc es).w.crem
    with Dup.minor_pre_d sty es tv n sl farr

/// akhil's postcondition, as the model's next configuration
/// (`CodeFFDup.minor_post_d`).
#push-options "--z3rlimit 40"
let minor_post_e (sty: style) (es: list event) (tv: Seq.seq U64.t) (n: nat) (s2: heap) (fp2: U64.t) (ms2: minor_state)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_e tv n (CF.xc es).w.crem /\
                    minor_infix_wf (CF.xc es).w.cyng /\
                    (let x = CF.xc es in
                     let ms = x.w.cyng in
                     let rs = Dup.rsd x tv n in
                     s2 == (C.cheney_collect_spec_with (gph x.ph) (FAO.ffree_of x.ph) ms (CF.hof x) (CF.sof x).fp rs).GP.mc_major /\
                     fp2 == (C.cheney_promote (gph x.ph) ms (CF.hof x) (CF.sof x).fp rs).GP.fp_final /\
                     ms2 == minor_reset ms /\
                     CB.cheney_no_oom (gph x.ph) ms (CF.hof x) (CF.sof x).fp rs))
          (ensures (let x = CF.xc es in
                    let x' = CF.xc (L.append es [EMinor]) in
                    CF.good sty (L.append es [EMinor]) /\
                    CF.hof x' == s2 /\ (CF.sof x').fp == fp2 /\ x'.w.cyng == ms2 /\ x'.w.crem == [] /\
                    x'.ph == x.ph /\ x'.ms == x.ms /\ FMi.rem_ok x'))
  = eliminate exists (sl: list M.slot). Dup.tbl_d tv n sl (CF.xc es).w.crem
    with Dup.minor_post_d sty es tv n sl s2 fp2 ms2
#pop-options

/// The start's roots, from akhil's rewritten roots and the caller's major
/// roots (`CodeFFDup.start_roots_d`).
#push-options "--z3rlimit 40"
let start_roots_e (sty: style) (es: list event) (tv: Seq.seq U64.t) (n: nat) (mr: Seq.seq U64.t) (u: U64.t)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_e tv n (CF.xc es).w.crem /\
                    minor_infix_wf (CF.xc es).w.cyng /\
                    (let x = CF.xc es in
                     CB.cheney_no_oom (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp (Dup.rsd x tv n) /\
                     (forall (u: U64.t). Seq.mem u mr <==>
                        (exists (a: nat). L.memP (M.VPtr (M.Major a)) x.w.croots /\ u == concv (M.VPtr (M.Major a))))))
          (ensures (let x = CF.xc es in
                    let x' = CF.xc (L.append es [EMinor]) in
                    let rs = Dup.rsd x tv n in
                    let rs2 = GP.rewrite_roots rs
                                (C.cheney_promote (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp rs).GP.fwd_map in
                    let k = Seq.length (LV.yroots (Y.ycabs x.w.cyng) x.w.croots) in
                    k <= Seq.length rs2 /\
                    (Seq.mem u (Seq.append (Seq.slice rs2 0 k) mr) <==>
                     Seq.mem u (BM.root_ws (cabs (CF.hof x')) x'.w.croots))))
  = eliminate exists (sl: list M.slot). Dup.tbl_d tv n sl (CF.xc es).w.crem
    with Dup.start_roots_d sty es tv n sl mr u
#pop-options

/// **The mark cache across the collection**: while marking akhil's
/// `mark_cache_minor` (the collection keeps every grey object and every
/// block that was not free); otherwise it is off.
let minor_cache (sty: style) (es: list event) (tv: Seq.seq U64.t) (n: nat) (st: Seq.seq obj_addr) (ov: bool)
    (p: MS.mark_pos) (s2: heap)
  : Lemma (requires CF.good sty es /\ minor_guards_complete (CF.xc es).w.cyng /\ minor_infix_wf (CF.xc es).w.cyng /\
                    MS.mark_cache_ok (CF.hof (CF.xc es)) (gph (CF.xc es).ph) st ov p /\
                    (let x = CF.xc es in
                     s2 == (C.cheney_collect_spec_with (gph x.ph) (FAO.ffree_of x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp
                              (Dup.rsd x tv n)).GP.mc_major))
          (ensures MS.mark_cache_ok s2 (gph (CF.xc es).ph) st ov p)
  = let x = CF.xc es in
    if T.Marking? x.ph then begin
      FMi.shape_ff sty es;
      FMi.marking_collect x.w.cyng (CF.hof x) (CF.sof x).fp (Dup.rsd x tv n);
      MS.mark_cache_minor x.w.cyng (CF.hof x) (CF.sof x).fp (Dup.rsd x tv n) st ov p
    end
    else MS.mark_cache_off (CF.hof x) s2 (gph x.ph) (gph x.ph) st ov p

/// ---------------------------------------------------------------------------
/// The start of a cycle
/// ---------------------------------------------------------------------------

/// **With the nursery empty, `EStart` is akhil's `start_cycle`** on any
/// array with the members of the roots' major words; the nursery and the
/// (empty) remembered set stay, nothing is being scanned.
#push-options "--z3rlimit 40"
let start_g (sty: style) (es: list event) (rs: Seq.seq U64.t)
  : Lemma (requires CF.good sty es /\ T.Idle? (CF.xc es).ph /\ U64.v (CF.xc es).w.cyng.bump == 0 /\
                    (CF.xc es).w.crem == [] /\
                    (forall (u: U64.t). Seq.mem u rs <==> Seq.mem u (BM.root_ws (cabs (CF.hof (CF.xc es))) (CF.xc es).w.croots)))
          (ensures (let x = CF.xc es in
                    let x' = CF.xc (L.append es [EStart]) in
                    (forall (i: nat). i < Seq.length rs ==>
                       GC.Impl.MarkBoundedPrecondition.root_valid_for_darkening (CF.hof x) (Seq.index rs i)) /\
                    CF.good sty (L.append es [EStart]) /\
                    CF.hof x' == GC.Gen.MarkPhase.Start.darkened (CF.hof x) rs /\ x'.ph == T.Marking /\
                    scan_of x' == None /\ CF.sof x' == CF.sof x /\
                    x'.w.cyng == x.w.cyng /\ x'.w.crem == [] /\ FMi.rem_ok x'))
  = let x = CF.xc es in
    let g = CF.hof x in
    let one (u: U64.t)
      : Lemma (Seq.mem u (BM.start_ws (BM.cview x.w)) <==> Seq.mem u (BM.root_ws (cabs g) x.w.croots))
      = FStar.Classical.forall_intro (FStar.Classical.move_requires (FMk.empty_young x.w.cyng));
        FMk.start_ws_roots g (BM.cview x.w) u in
    FStar.Classical.forall_intro one;
    FMk.start_cfg sty es rs;
    snoc_eq sty es EStart;
    FMi.rem_start sty es
#pop-options

/// The table's entries are field addresses.
let tbl_addrs_e (sty: style) (es: list event) (tv: Seq.seq U64.t) (n: nat)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_e tv n (CF.xc es).w.crem)
          (ensures n <= Seq.length tv /\
                   (forall (k: nat). k < n ==> U64.v (Seq.index tv k) % 8 == 0 /\ U64.v (Seq.index tv k) < heap_size))
  = eliminate exists (sl: list M.slot). Dup.tbl_d tv n sl (CF.xc es).w.crem
    with begin
      let one (k: nat) : Lemma (k < n ==> U64.v (Seq.index tv k) % 8 == 0 /\ U64.v (Seq.index tv k) < heap_size)
        = if k < n then Dup.entry_facts sty es tv n sl k in
      FStar.Classical.forall_intro one
    end

/// The caller's major roots: exactly the words of the major roots.
let mr_ok (es: list event) (mr: Seq.seq U64.t) : prop =
  forall (u: U64.t). Seq.mem u mr <==>
    (exists (a: nat). L.memP (M.VPtr (M.Major a)) (CF.xc es).w.croots /\ u == concv (M.VPtr (M.Major a)))

/// The number of the program's young roots.
let kof (es: list event) : GTot nat = Seq.length (LV.yroots (Y.ycabs (CF.xc es).w.cyng) (CF.xc es).w.croots)

/// **After the collection**: the rewritten young roots and the caller's
/// major roots have the members of the roots' major words.
let roots_after (es: list event) (mr rs2: Seq.seq U64.t) : prop =
  kof es <= Seq.length rs2 /\
  (mr_ok es mr ==>
     (forall (u: U64.t). Seq.mem u (Seq.append (Seq.slice rs2 0 (kof es)) mr) <==>
        Seq.mem u (BM.root_ws (cabs (CF.hof (CF.xc (L.append es [EMinor])))) (CF.xc (L.append es [EMinor])).w.croots)))

#push-options "--z3rlimit 40"
let roots_after_e (sty: style) (es: list event) (tv: Seq.seq U64.t) (n: nat) (mr rs2: Seq.seq U64.t)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_e tv n (CF.xc es).w.crem /\
                    minor_infix_wf (CF.xc es).w.cyng /\
                    (let x = CF.xc es in
                     let rs = Dup.rsd x tv n in
                     CB.cheney_no_oom (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp rs /\
                     rs2 == GP.rewrite_roots rs (C.cheney_promote (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp rs).GP.fwd_map))
          (ensures roots_after es mr rs2)
  = let x = CF.xc es in
    let rs = Dup.rsd x tv n in
    assert (Seq.length rs == kof es + Seq.length (CM.ypre_tbl (CF.hof x) tv n));
    let k (_: squash (mr_ok es mr))
      : Lemma (forall (u: U64.t). Seq.mem u (Seq.append (Seq.slice rs2 0 (kof es)) mr) <==>
                 Seq.mem u (BM.root_ws (cabs (CF.hof (CF.xc (L.append es [EMinor])))) (CF.xc (L.append es [EMinor])).w.croots))
      = FStar.Classical.forall_intro (start_roots_e sty es tv n mr) in
    FStar.Classical.impl_intro k
#pop-options
