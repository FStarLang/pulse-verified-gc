/// ---------------------------------------------------------------------------
/// GC.Impl.FFTop - the first-fit code, event by event, as runs of the
/// top-level specification
/// ---------------------------------------------------------------------------
///
/// Design doc §18, step 3.  `crepf heap fp_ref phase sty es`: the heap, the
/// free list's head and the phase record of `GC.Impl.Allocator` represent
/// the configuration of the first-fit collector `fc` after the events `es`,
/// a run of style `sty` (`CodeFF.good`); the record holds the phase, with
/// the sweep's caches derived from the heap (`Allocator.phase_rel`).  Each
/// wrapper performs its events and ensures the representation of the longer
/// run:
///   - `initf`: a zeroed heap, then the model's initial heap (one blue block
///     from `zero_addr`), the record idle;
///   - `allocf`: `EAlloc`, akhil's `Allocator.allocate` (L5) and the Fill;
///   - `handoverf`: `EHandover`, the record at the sweep's start;
///   - `slicef`: a slice of akhil's fused sweep (`sweep_slice_impl`) as `k`
///     events `ESweep` (L6), then `EEnd` when the sweep is done;
///   - `rootsf`, `readf`: the program's root events, ghost.
/// The nursery, the minor collection, the mark and the barrier are later
/// steps (§18.7: 4, 5).

module GC.Impl.FFTop

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Spec.Top.Run

module U64 = FStar.UInt64
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module L = FStar.List.Tot
module SB = GC.Spec.Base
module SH = GC.Spec.Heap
module SO = GC.Spec.Object
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module W = GC.Spec.Top.Word
module Abs = GC.Spec.Top.Abs
module BF = GC.Spec.Top.ByteFacts
module FAl = GC.Spec.Top.FFAlloc
module CF = GC.Spec.Top.CodeFF
module CP = GC.Spec.Top.CodePages
module CR = GC.Spec.Top.CodeRun
module Ph = GC.Spec.Phase
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module FS = GC.Spec.FusedSweep
module SPI = GC.Spec.SweepPhase.Intrinsic
module SL = GC.Spec.SweepPhase.Slice
module Wk = GC.Spec.Walk
module AI = GC.Impl.Allocator
module FSC = GC.Impl.FusedSweepCoalesce
module Obj = GC.Impl.Object
module Hdr = GC.Lib.Header
module PT = GC.Impl.Pages.Top

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The representation
/// ---------------------------------------------------------------------------

/// **The code's state represents the configuration after `es`.**
let crepf (heap: heap_t) (fp_ref: R.ref U64.t) (phase: R.ref AI.phase_state) (sty: style) (es: list event)
  : slprop =
  exists* (x: config CF.fc) (v: AI.phase_state).
    is_heap heap (CF.hof x) ** R.pts_to fp_ref (CF.sof x).FAl.fp ** R.pts_to phase v **
    pure (x == CF.xc es /\ CF.good sty es /\ AI.phase_rel (CF.hof x) v (FAl.gph x.ph))

/// A change that keeps the walk and its headers keeps the record's meaning.
let phase_keep (g g': SB.heap) (v: AI.phase_state) (ph: Ph.gc_phase)
  : Lemma (requires SPI.same_heads g g' /\ AI.phase_rel g v ph)
          (ensures AI.phase_rel g' v ph)
  = if v.AI.ps_kind = 1UL then SPI.state_at_heads g g' v.AI.ps_cursor

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

/// The initial block's header, as the code builds it.
let init_hdr (w: U64.t)
  : Lemma (requires U64.v w == FAl.init_wz /\ U64.v w < pow2 54)
          (ensures Obj.makeHeader w Hdr.Blue 0UL == FS.free_header FAl.init_wz)
  = Obj.makeHeader_eq_pack_header w Hdr.Blue 0UL;
    U64.uv_inv w;
    assert (U64.uint_to_t FAl.init_wz == w);
    assert (FS.free_header FAl.init_wz == SO.makeHeader w Hdr.Blue 0UL);
    SO.makeHeader_is_pack_header64 w Hdr.Blue 0UL;
    U64.v_inj (Obj.makeHeader w Hdr.Blue 0UL) (FS.free_header FAl.init_wz)

let init_words (_: unit)
  : Lemma (U64.v SB.zero_addr + 8 < SB.heap_size /\ (U64.v SB.zero_addr + 8) % 8 == 0 /\
           (SB.heap_size - U64.v SB.zero_addr) / 8 - 1 == FAl.init_wz /\ FAl.init_wz < pow2 54 /\
           FAl.init_fp == U64.uint_to_t (U64.v SB.zero_addr + 8))
  = FAl.init_facts ()

/// **The start**: a zeroed heap, then the model's initial heap.
fn initf (heap: heap_t) (fp_ref: R.ref U64.t) (phase: R.ref AI.phase_state) (sty: erased style)
  requires is_heap heap 'g ** R.pts_to fp_ref 'f0 ** R.pts_to phase 'v0
  ensures crepf heap fp_ref phase sty []
{
  PT.zero_heap heap;
  init_words ();
  let w = U64.sub (U64.div (U64.sub heap_size_u64 SB.zero_addr) 8UL) 1UL;
  init_hdr w;
  let hdr = Obj.makeHeader w Hdr.Blue 0UL;
  write_word heap SB.zero_addr hdr;
  let a1 : hp_addr = U64.add SB.zero_addr 8UL;
  write_word heap a1 0UL;
  fp_ref := a1;
  phase := { AI.ps_kind = 0UL; AI.ps_cursor = 0UL; AI.ps_swept_tail = 0UL; AI.ps_last_fragment = 0UL };
  CF.init_cfg sty;
  with g'. assert (is_heap heap g');
  assert (pure (g' == FAl.init_heap));
  rewrite (is_heap heap g') as (is_heap heap (CF.hof (CF.xc [])));
  rewrite (R.pts_to fp_ref a1) as (R.pts_to fp_ref (CF.sof (CF.xc [])).FAl.fp);
  fold (crepf heap fp_ref phase sty [])
}

/// ---------------------------------------------------------------------------
/// L5: allocation and its Fill
/// ---------------------------------------------------------------------------

/// The tag, as the Pulse allocator takes it.
let tg_eq (t: U64.t) : Lemma (requires U64.v t < 256) (ensures FAl.tg (U64.v t) == t)
  = FAl.tg_v (U64.v t); U64.v_inj (FAl.tg (U64.v t)) t

/// What the allocation and its Fill do to the run, on the code's terms.
#push-options "--z3rlimit 40"
let alloc_side (sty: style) (es: list event) (wz: M.size_t) (tag: M.tag_t) (vs: list M.value) (v: AI.phase_state)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) (EAlloc wz tag vs) /\
                    AI.phase_rel (CF.hof (CF.xc es)) v (FAl.gph (CF.xc es).ph))
          (ensures (let x = CF.xc es in
                    let r = AC.alloc_phase (CF.hof x) (CF.sof x).FAl.fp (FAl.gph x.ph) wz (FAl.tg tag) in
                    let es' = L.append es [EAlloc wz tag vs] in
                    let x' = CF.xc es' in
                    CF.good sty es' /\ x'.ph == x.ph /\
                    (r.SA.obj_out == 0UL ==>
                       x' == x /\ r.SA.heap_out == CF.hof x /\ r.SA.fp_out == (CF.sof x).FAl.fp) /\
                    (r.SA.obj_out =!= 0UL ==>
                       Abs.pos (BF.maddr r.SA.obj_out) + 8 == U64.v r.SA.obj_out /\
                       U64.v r.SA.obj_out + 8 * wz <= SB.heap_size /\
                       CF.hof x' == CP.fill_from r.SA.heap_out (BF.maddr r.SA.obj_out) 0 vs /\
                       (CF.sof x').FAl.fp == r.SA.fp_out /\
                       (forall (v1: AI.phase_state). AI.phase_rel r.SA.heap_out v1 (FAl.gph x.ph) ==>
                                                    AI.phase_rel (CF.hof x') v1 (FAl.gph x.ph)))))
  = let x = CF.xc es in
    let e = EAlloc wz tag vs in
    let r = AC.alloc_phase (CF.hof x) (CF.sof x).FAl.fp (FAl.gph x.ph) wz (FAl.tg tag) in
    if r.SA.obj_out = 0UL then begin
      CF.alloc_none sty es wz tag vs;
      CF.snoc sty es e
    end
    else begin
      CF.alloc_some sty es wz tag vs;
      CF.snoc sty es e;
      let x' = step CF.fc x e in
      let k (v1: AI.phase_state)
        : Lemma (AI.phase_rel r.SA.heap_out v1 (FAl.gph x.ph) ==> AI.phase_rel (CF.hof x') v1 (FAl.gph x.ph))
        = FStar.Classical.move_requires (phase_keep r.SA.heap_out (CF.hof x') v1) (FAl.gph x.ph) in
      FStar.Classical.forall_intro k
    end
#pop-options

/// **`EAlloc`**: akhil's first-fit allocation at the phase, then the Fill
/// with the words `ws` (the values `vs`).  Returns the new block's
/// first-field address, or 0 when there is no room (then nothing changes).
#push-options "--z3rlimit 40"
fn allocf (heap: heap_t) (fp_ref: R.ref U64.t) (phase: R.ref AI.phase_state)
  (wz: U64.t{U64.v wz >= 1}) (tag: U64.t{U64.v tag < 256}) (fs: A.array U64.t) (#p: perm)
  (#ws: erased (Seq.seq U64.t)) (#sty: erased style) (#es: erased (list event)) (vs: erased (list M.value))
  requires crepf heap fp_ref phase sty es ** A.pts_to fs #p ws **
           pure (Seq.length ws == U64.v wz /\ L.length vs == U64.v wz /\
                 (forall (i: nat). i < U64.v wz ==> Seq.index ws i == W.concv (L.index vs i)) /\
                 CR.allowed CF.fc sty (CF.xc es) (EAlloc (U64.v wz) (U64.v tag) vs))
  returns o: U64.t
  ensures crepf heap fp_ref phase sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]) ** A.pts_to fs #p ws **
          pure (o == 0UL ==> CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]) == CF.xc es)
{
  unfold crepf;
  with x v. assert (is_heap heap (CF.hof x) ** R.pts_to phase v);
  CF.alloc_ready sty es;
  tg_eq tag;
  alloc_side sty es (U64.v wz) (U64.v tag) vs v;
  fold (AI.is_phase phase (CF.hof x) (FAl.gph x.ph));
  let o = AI.allocate heap fp_ref phase wz tag;
  unfold (AI.is_phase phase);
  with g' v'. assert (is_heap heap g' ** R.pts_to phase v');
  if (o = 0UL) {
    rewrite (is_heap heap g') as (is_heap heap (CF.hof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]))));
    fold (crepf heap fp_ref phase sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]));
    o
  } else {
    PT.fill heap o wz fs (BF.maddr o) vs;
    rewrite (is_heap heap (CP.fill_from g' (BF.maddr o) 0 vs))
         as (is_heap heap (CF.hof (CF.xc (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]))));
    fold (crepf heap fp_ref phase sty (L.append es [EAlloc (U64.v wz) (U64.v tag) vs]));
    o
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let reaches_self (g: SB.heap) (a: hp_addr) : Lemma (Wk.reaches g a (U64.v a)) = ()
#pop-options

/// **`EHandover`**: the record at the sweep's start, the cursor at
/// `zero_addr`.
fn handoverf (heap: heap_t) (fp_ref: R.ref U64.t) (phase: R.ref AI.phase_state)
  (#sty: erased style) (#es: erased (list event))
  requires crepf heap fp_ref phase sty es **
           pure (T.Marking? (CF.xc es).ph /\ T.mark_done (mj (CF.xc es)))
  ensures crepf heap fp_ref phase sty (L.append es [EHandover])
{
  unfold crepf;
  with x v. assert (is_heap heap (CF.hof x) ** R.pts_to phase v);
  CF.handover_cfg x;
  CF.allowed_gc sty es EHandover;
  CF.snoc sty es EHandover;
  reaches_self (CF.hof x) SB.zero_addr;
  phase := { AI.ps_kind = 1UL; AI.ps_cursor = SB.zero_addr; AI.ps_swept_tail = 0UL; AI.ps_last_fragment = 0UL };
  rewrite (is_heap heap (CF.hof x)) as (is_heap heap (CF.hof (CF.xc (L.append es [EHandover]))));
  rewrite (R.pts_to fp_ref (CF.sof x).FAl.fp) as (R.pts_to fp_ref (CF.sof (CF.xc (L.append es [EHandover]))).FAl.fp);
  fold (crepf heap fp_ref phase sty (L.append es [EHandover]))
}

let hs_small (_: unit) : Lemma (SB.heap_size + 8 < pow2 64) = assert_norm (pow2 57 + 8 < pow2 64)

/// The record of a sweep at `c`: its cursor and caches.
let rec_link (g: SB.heap) (v: AI.phase_state) (c: U64.t)
  : Lemma (requires AI.phase_rel g v (Ph.Sweeping c))
          (ensures v.AI.ps_kind == 1UL /\ v.AI.ps_cursor == c /\
                   FSC.mk_st v.AI.ps_cursor v.AI.ps_swept_tail v.AI.ps_last_fragment == SPI.state_at g c)
  = ()

/// The events of a slice with budget `budget` from `es`: one `ESweep` per
/// step of the fused sweep.
let slice_evs (es: list event) (budget: nat) : GTot (list event) =
  let x = CF.xc es in
  match x.ph with
  | T.Sweeping c ->
    L.append es (CF.sweeps (SL.slice_count (CF.hof x) (CF.sof x).FAl.fp (SPI.state_at (CF.hof x) c) c budget))
  | _ -> es

/// **A slice of the sweep**: akhil's `sweep_slice_impl` from the record's
/// cursor and caches, as `k` events `ESweep` (L6); when the cursor reaches
/// the end, `EEnd` too, and the result is true.
#push-options "--z3rlimit 40"
fn slicef (heap: heap_t) (fp_ref: R.ref U64.t) (phase: R.ref AI.phase_state) (budget: U64.t)
  (#sty: erased style) (#es: erased (list event))
  requires crepf heap fp_ref phase sty es ** pure (T.Sweeping? (CF.xc es).ph)
  returns fin: bool
  ensures crepf heap fp_ref phase sty
            (if fin then L.append (slice_evs es (U64.v budget)) [EEnd] else slice_evs es (U64.v budget))
{
  unfold crepf;
  with x v. assert (is_heap heap (CF.hof x) ** R.pts_to phase v);
  CF.good_inv sty es;
  CF.slice_cfg sty es (U64.v budget);
  let pv = !phase;
  let fp = !fp_ref;
  rec_link (CF.hof x) pv (T.Sweeping?._0 x.ph);
  let r = FSC.sweep_slice_impl heap pv.AI.ps_cursor pv.AI.ps_swept_tail pv.AI.ps_last_fragment fp budget;
  let c' = Mktuple4?._1 r;
  let t' = Mktuple4?._2 r;
  let f' = Mktuple4?._3 r;
  let fp' = Mktuple4?._4 r;
  with g'. assert (is_heap heap g');
  assert (pure (U64.v c' <= SB.heap_size));
  hs_small ();
  fp_ref := fp';
  if (U64.gte (U64.add c' 8UL) heap_size_u64) {
    CF.end_cfg sty (slice_evs es (U64.v budget));
    phase := { AI.ps_kind = 0UL; AI.ps_cursor = c'; AI.ps_swept_tail = t'; AI.ps_last_fragment = f' };
    rewrite (is_heap heap g')
         as (is_heap heap (CF.hof (CF.xc (L.append (slice_evs es (U64.v budget)) [EEnd]))));
    rewrite (R.pts_to fp_ref fp')
         as (R.pts_to fp_ref (CF.sof (CF.xc (L.append (slice_evs es (U64.v budget)) [EEnd]))).FAl.fp);
    fold (crepf heap fp_ref phase sty (L.append (slice_evs es (U64.v budget)) [EEnd]));
    true
  } else {
    phase := { AI.ps_kind = 1UL; AI.ps_cursor = c'; AI.ps_swept_tail = t'; AI.ps_last_fragment = f' };
    rewrite (is_heap heap g') as (is_heap heap (CF.hof (CF.xc (slice_evs es (U64.v budget)))));
    rewrite (R.pts_to fp_ref fp') as (R.pts_to fp_ref (CF.sof (CF.xc (slice_evs es (U64.v budget)))).FAl.fp);
    fold (crepf heap fp_ref phase sty (slice_evs es (U64.v budget)));
    false
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// The program's root events (ghost)
/// ---------------------------------------------------------------------------

/// **`ERoots`**: the program's roots, replaced.
ghost fn rootsf (heap: heap_t) (fp_ref: R.ref U64.t) (phase: R.ref AI.phase_state)
  (#sty: erased style) (#es: erased (list event)) (rs: list M.value)
  requires crepf heap fp_ref phase sty es ** pure (CR.allowed CF.fc sty (CF.xc es) (ERoots rs))
  ensures crepf heap fp_ref phase sty (L.append es [ERoots rs])
{
  unfold crepf;
  with x v. assert (is_heap heap (CF.hof x) ** R.pts_to phase v);
  CF.roots_cfg x rs;
  CF.snoc sty es (ERoots rs);
  rewrite (is_heap heap (CF.hof x)) as (is_heap heap (CF.hof (CF.xc (L.append es [ERoots rs]))));
  rewrite (R.pts_to fp_ref (CF.sof x).FAl.fp) as (R.pts_to fp_ref (CF.sof (CF.xc (L.append es [ERoots rs]))).FAl.fp);
  fold (crepf heap fp_ref phase sty (L.append es [ERoots rs]))
}

/// **`ERead`** of a major block's field into a new root.
ghost fn readf (heap: heap_t) (fp_ref: R.ref U64.t) (phase: R.ref AI.phase_state)
  (#sty: erased style) (#es: erased (list event)) (o i: nat)
  requires crepf heap fp_ref phase sty es ** pure (CR.allowed CF.fc sty (CF.xc es) (ERead (M.Major o) i))
  ensures crepf heap fp_ref phase sty (L.append es [ERead (M.Major o) i])
{
  unfold crepf;
  with x v. assert (is_heap heap (CF.hof x) ** R.pts_to phase v);
  CF.read_cfg x o i;
  CF.snoc sty es (ERead (M.Major o) i);
  rewrite (is_heap heap (CF.hof x)) as (is_heap heap (CF.hof (CF.xc (L.append es [ERead (M.Major o) i]))));
  rewrite (R.pts_to fp_ref (CF.sof x).FAl.fp)
       as (R.pts_to fp_ref (CF.sof (CF.xc (L.append es [ERead (M.Major o) i]))).FAl.fp);
  fold (crepf heap fp_ref phase sty (L.append es [ERead (M.Major o) i]))
}
