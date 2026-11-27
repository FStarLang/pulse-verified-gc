/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWMark - the mark in a pages witness run
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  On a described configuration (GC.Spec.Top.PWDesc), the
/// byte mark computed on the model:
///   - `step_start`: the start greys the white blocks the roots and the
///     nursery point to (`ByteMark.bstart_cabs`, the toy start);
///   - `step_slice`: a slice scans the lowest grey block `fg x` whole, as
///     moves (`slm x`, `ByteMark.obj_moves_bytes`, the toy slice): it turns
///     black, its white targets grey.
/// Both are changes the allocator's invariant does not read
/// (`inv_frame_at`): colours of blocks in use, while marking, darkened.

module GC.Spec.Top.PWMark

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.Run
open GC.Spec.Top.PWDesc
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module BM = GC.Spec.Top.ByteMark
module TM = GC.Spec.Top.ToyMark
module PIn = GC.Spec.Top.PagesInst
module PWP = GC.Spec.Top.PWPages

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let recol (d: dsc) (f: nat -> bd -> GTot bd) : nat -> GTot (option bd) =
  fun (y: nat) -> match d.db y with Some b -> Some (f y b) | None -> None

/// Recolouring keeps the shape; in use is read from the headers.
let recol_iu (x x': config pc) (y: nat)
  : Lemma (requires stx x' == stx x /\ M.is_block (mx x') y == M.is_block (mx x) y /\
                    (M.col_of (mx x') y == M.Blue <==> M.col_of (mx x) y == M.Blue))
          (ensures iu x' y == iu x y)
  = iu_def x y; iu_def x' y

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

let gstart (x: config pc) (d: dsc) (y: nat) (b: bd) : GTot bd =
  if TM.outside_b (wd x d) y then { b with bc = M.Grey } else b

let dstart (x: config pc) (d: dsc) : GTot dsc = { d with dk = DM; db = recol d (gstart x d) }

let spre (x: config pc) (d: dsc) : prop =
  cok /\ holds x d /\ d.dk == DI /\
  (forall (y: nat). Some? (d.db y) ==> (Some?.v (d.db y)).bc == M.White) /\
  (forall (y: nat). M.outside_ref (wd x d) y ==> iu x y == true) /\
  (forall (y: nat). M.reachable (wd x d) y ==> iu x y == true)

let start_pre (x: config pc) (d: dsc)
  : Lemma (requires spre x d) (ensures T.mark_start_pre (wd x d))
  = holds_elim x d;
    let nd (y: nat) : Lemma (M.is_block (mx x) y ==> not (M.dark (M.col_of (mx x) y)))
      = iu_def x y; if iu x y then (holds_iu x d y; holds_blk x d y) in
    FStar.Classical.forall_intro nd;
    let rw (y: nat) : Lemma (M.reachable (wd x d) y ==> M.col_of (mx x) y == M.White)
      = if FStar.IndefiniteDescription.strong_excluded_middle (M.reachable (wd x d) y) then begin
          iu_def x y;
          holds_iu x d y; holds_blk x d y
        end in
    FStar.Classical.forall_intro rw

/// Recolouring keeps the walk.
let wf_cols (m m': M.mheap) : Lemma (requires M.colours_only m m' /\ M.well_formed m) (ensures M.well_formed m')
  = assert (forall (o w: nat). M.covers m' o w == M.covers m o w)

/// The heap after a recolouring the invariant does not read.
let recol_after (x x': config pc) (d: dsc) (m': M.mheap)
  : Lemma (requires T.inv_frame_at byte_rep pa T.Marking x.w.cmaj (stx x) x'.w.cmaj /\ holds x d /\ R.heq (mx x') m' /\ M.colours_only (mx x) m' /\
                    x'.ph == T.Marking /\ stx x' == stx x /\ pa.T.inv T.Marking x.w.cmaj (stx x) /\
                    (forall (y: nat). M.col_of m' y =!= M.col_of (mx x) y ==> iu x y == true /\ M.dark (M.col_of m' y)) /\
                    (forall (y: nat). (M.col_of m' y == M.Blue <==> M.col_of (mx x) y == M.Blue)))
          (ensures pa.T.inv T.Marking x'.w.cmaj (stx x') /\ M.well_formed (mx x') /\
                   (forall (y: nat). iu x' y == iu x y))
  = holds_elim x d;
    wf_cols (mx x) m';
    R.heq_sym (mx x') m';
    PIn.wf_heq m' (mx x');
    assert (T.inv_frame_rel pa T.Marking (stx x) x.w.cmaj (mx x) m');
    brepr_cabs x.w.cmaj;
    assert (T.inv_frame_m pa T.Marking x.w.cmaj (stx x) x'.w.cmaj (mx x) m');
    let iux (y: nat) : Lemma (iu x' y == iu x y) = recol_iu x x' y in
    FStar.Classical.forall_intro iux

let mk_intro (x x': config pc) (d d': dsc)
  : Lemma (requires holds x d /\ x'.stopped == x.stopped /\ x'.w.cyng == x.w.cyng /\ x'.w.croots == x.w.croots /\
                    x'.w.crem == x.w.crem /\ x'.ms == None /\ d'.dys == d.dys /\ d'.dym == d.dym /\ d'.drt == d.drt /\ d'.dj == d.dj /\
                    kph x' d'.dk /\ stx x' == stx x /\
                    pa.T.inv x'.ph x'.w.cmaj (stx x') /\ M.well_formed (mx x') /\
                    (forall (y: nat). Some? (d'.db y) ==> bk x' d' y (Some?.v (d'.db y))) /\
                    (forall (y: nat). iu x' y == true ==> Some? (d'.db y)))
          (ensures holds x' d')
  = holds_elim x d;
    holds_intro x' d'

let start_facts (x: config pc) (d: dsc)
  : Lemma (requires spre x d)
          (ensures (let x' = step pc x EStart in
                    let m' = TM.tmstart (wd x d) in
                    R.heq (mx x') m' /\ M.colours_only (mx x) m' /\ x'.ph == T.Marking /\ stx x' == stx x /\
                    x'.ms == None /\
                    pa.T.inv T.Marking x.w.cmaj (stx x) /\ T.inv_frame_at byte_rep pa T.Marking x.w.cmaj (stx x) x'.w.cmaj /\
                    (forall (y: nat). M.col_of m' y =!= M.col_of (mx x) y ==> iu x y == true /\ M.dark (M.col_of m' y)) /\
                    (forall (y: nat). (M.col_of m' y == M.Blue <==> M.col_of (mx x) y == M.Blue))))
  = holds_elim x d;
    start_pre x d;
    views_wd x d;
    BM.bstart_cabs x.w (wd x d);
    let m' = TM.tmstart (wd x d) in
    R.heq_sym m' (mx (step pc x EStart));
    TM.tmstart_colours_only (wd x d);
    let col (y: nat) : Lemma (M.col_of m' y =!= M.col_of (mx x) y ==> iu x y == true /\ M.dark (M.col_of m' y))
      = TM.outside_b_iff (wd x d) y in
    FStar.Classical.forall_intro col;
    cok_hyps x EStart;
    assert (T.inv_start_at pa x.w.cmaj (stx x))

let start_blk (x: config pc) (d: dsc) (y: nat)
  : Lemma (requires spre x d /\ Some? (d.db y) /\ R.heq (mx (step pc x EStart)) (TM.tmstart (wd x d)) /\
                    iu (step pc x EStart) y == iu x y)
          (ensures bk (step pc x EStart) (dstart x d) y (Some?.v ((dstart x d).db y)))
  = holds_elim x d;
    holds_blk x d y;
    TM.tmstart_colours_only (wd x d);
    let b = Some?.v (d.db y) in
    assert (b.bc == M.White);
    let x' = step pc x EStart in
    let b' = gstart x d y b in
    let og = TM.outside_b (wd x d) y in
    assert (iu x y == true);
    assert ((mx x).M.hd y == Some ({ M.wz = b.bw; M.tag = b.bt; M.col = M.White }));
    assert ((TM.tmstart (wd x d)).M.hd y == Some ({ M.wz = b.bw; M.tag = b.bt; M.col = (if og then M.Grey else M.White) }));
    assert ((mx x').M.hd y == (TM.tmstart (wd x d)).M.hd y);
    assert (x'.ph == T.Marking);
    assert (b'.bc == (if og then M.Grey else M.White));
    assert (hcol x' b' y == b'.bc);
    assert (forall (i: nat). M.field (mx x') y i == M.field (mx x) y i);
    assert ((dstart x d).db y == Some b');
    let d' = dstart x d in
    let m1 = mx x' in
    assert (usable d' b' ==> iu x' y == true);
    assert (iu x' y == true ==> m1.M.hd y == Some ({ M.wz = b'.bw; M.tag = b'.bt; M.col = hcol x' b' y }));
    assert (iu x' y == true /\ DS? d'.dk /\ not b'.blv ==> unsw x' y == true);
    assert (usable d' b' ==> L.length b'.bf == b'.bw /\ (forall (i: nat). i < b'.bw ==> M.field m1 y i == vi b'.bf i))

/// **EStart**.
let step_start (x: config pc) (d: dsc)
  : Lemma (requires spre x d) (ensures holds (step pc x EStart) (dstart x d))
  = start_facts x d;
    let x' = step pc x EStart in
    let d' = dstart x d in
    recol_after x x' d (TM.tmstart (wd x d));
    let bl (y: nat) : Lemma (Some? (d'.db y) ==> bk x' d' y (Some?.v (d'.db y)))
      = if Some? (d.db y) then start_blk x d y in
    FStar.Classical.forall_intro bl;
    let des (y: nat) : Lemma (iu x' y == true ==> Some? (d'.db y))
      = if iu x y then holds_iu x d y in
    FStar.Classical.forall_intro des;
    mk_intro x x' d d'

/// ---------------------------------------------------------------------------
/// A slice
/// ---------------------------------------------------------------------------

/// The grey block a slice scans.
let fg (x: config pc) : GTot nat =
  match TM.find_grey (mx x) msize with Some t -> t | None -> 0

/// Its moves: the block scanned whole (`ByteMark.obj_mv`).
let slm (x: config pc) : GTot (list T.move) = BM.obj_mv (mx x) (fg x)

/// The slice event at `x`.
let esl (x: config pc) : GTot event = ESlice (slm x)

let gslice (x: config pc) (t: nat) (y: nat) (b: bd) : GTot bd =
  if y = t then { b with bc = M.Black }
  else if TM.edge_b (mx x) t y && b.bc = M.White then { b with bc = M.Grey }
  else b

let dslice (x: config pc) (d: dsc) : GTot dsc = { d with db = recol d (gslice x (fg x)) }

/// What a slice needs: a grey block; each grey block's pointer fields
/// resolve, to blocks in use.
let slpre (x: config pc) (d: dsc) : prop =
  cok /\ holds x d /\ d.dk == DM /\ ~(T.no_grey (mx x)) /\
  (forall (t: nat). M.is_block (mx x) t /\ M.col_of (mx x) t == M.Grey ==>
     (forall (i a: nat). M.ptr_field (mx x) t i /\ M.field (mx x) t i == M.VPtr (M.Major a) ==>
        Some? (M.resolve (mx x) a)) /\
     (forall (y: nat). M.major_edge (mx x) t y ==> iu x y == true))

let grey_found (x: config pc) (d: dsc)
  : Lemma (requires slpre x d)
          (ensures TM.find_grey (mx x) msize == Some (fg x) /\ M.is_block (mx x) (fg x) /\
                   M.col_of (mx x) (fg x) == M.Grey /\ iu x (fg x) == true /\ Some? (d.db (fg x)))
  = holds_elim x d;
    BM.some_grey (mx x) x.w.cmaj;
    iu_def x (fg x);
    holds_iu x d (fg x)

let slice_cols (m: M.mheap) (t: nat)
  : Lemma (requires M.is_block m t) (ensures M.colours_only m (TM.tmslice_with m t))
  = ()

let slice_facts (x: config pc) (d: dsc)
  : Lemma (requires slpre x d)
          (ensures (let x' = step pc x (ESlice (slm x)) in
                    let m' = TM.tmslice_with (mx x) (fg x) in
                    R.heq (mx x') m' /\ M.colours_only (mx x) m' /\ x'.ph == T.Marking /\ stx x' == stx x /\
                    x'.ms == None /\
                    pa.T.inv T.Marking x.w.cmaj (stx x) /\ T.inv_frame_at byte_rep pa T.Marking x.w.cmaj (stx x) x'.w.cmaj /\
                    (forall (y: nat). M.col_of m' y =!= M.col_of (mx x) y ==> iu x y == true /\ M.dark (M.col_of m' y)) /\
                    (forall (y: nat). (M.col_of m' y == M.Blue <==> M.col_of (mx x) y == M.Blue))))
  = holds_elim x d;
    grey_found x d;
    let t = fg x in
    let x' = step pc x (ESlice (slm x)) in
    BM.obj_moves_bytes x.w.cmaj (mx x) t;
    assert (pc.m == BM.bmark);
    assert (x'.w.cmaj == fst (T.mmoves BM.bmark x.w.cmaj None (slm x)));
    let m' = TM.tmslice_with (mx x) t in
    R.heq_sym m' (mx x');
    slice_cols (mx x) t;
    let col (y: nat) : Lemma (M.col_of m' y =!= M.col_of (mx x) y ==> iu x y == true /\ M.dark (M.col_of m' y))
      = TM.edge_b_iff (mx x) t y in
    FStar.Classical.forall_intro col;
    cok_hyps x (ESlice (slm x))

let slice_blk (x: config pc) (d: dsc) (y: nat)
  : Lemma (requires slpre x d /\ Some? (d.db y) /\ R.heq (mx (step pc x (ESlice (slm x)))) (TM.tmslice_with (mx x) (fg x)) /\
                    iu (step pc x (ESlice (slm x))) y == iu x y)
          (ensures bk (step pc x (ESlice (slm x))) (dslice x d) y (Some?.v ((dslice x d).db y)))
  = holds_elim x d;
    holds_blk x d y;
    let b = Some?.v (d.db y) in
    let x' = step pc x (ESlice (slm x)) in
    let t = fg x in
    let b' = gslice x t y b in
    let d' = dslice x d in
    let m1 = mx x' in
    assert (iu x y == true);
    assert ((mx x).M.hd y == Some ({ M.wz = b.bw; M.tag = b.bt; M.col = b.bc }));
    assert (m1.M.hd y == (TM.tmslice_with (mx x) t).M.hd y);
    assert ((TM.tmslice_with (mx x) t).M.hd y == Some ({ M.wz = b.bw; M.tag = b.bt; M.col = b'.bc }));
    assert (x'.ph == x.ph);
    assert (hcol x' b' y == b'.bc);
    assert (forall (i: nat). M.field m1 y i == M.field (mx x) y i);
    assert (d'.db y == Some b');
    assert (usable d' b' ==> iu x' y == true);
    assert (iu x' y == true ==> m1.M.hd y == Some ({ M.wz = b'.bw; M.tag = b'.bt; M.col = hcol x' b' y }));
    assert (usable d' b' ==> L.length b'.bf == b'.bw /\ (forall (i: nat). i < b'.bw ==> M.field m1 y i == vi b'.bf i))

/// **ESlice**: the grey block `fg x` scanned.
let step_slice (x: config pc) (d: dsc)
  : Lemma (requires slpre x d)
          (ensures M.col_of (mx x) (fg x) == M.Grey /\ Some? (d.db (fg x)) /\
                   holds (step pc x (ESlice (slm x))) (dslice x d))
  = grey_found x d;
    slice_facts x d;
    let x' = step pc x (ESlice (slm x)) in
    let d' = dslice x d in
    recol_after x x' d (TM.tmslice_with (mx x) (fg x));
    let bl (y: nat) : Lemma (Some? (d'.db y) ==> bk x' d' y (Some?.v (d'.db y)))
      = if Some? (d.db y) then slice_blk x d y in
    FStar.Classical.forall_intro bl;
    let des (y: nat) : Lemma (iu x' y == true ==> Some? (d'.db y))
      = if iu x y then holds_iu x d y in
    FStar.Classical.forall_intro des;
    holds_elim x d;
    mk_intro x x' d d'
