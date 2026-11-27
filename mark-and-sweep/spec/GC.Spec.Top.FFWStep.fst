/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWStep - one event of a first-fit witness run
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  A configuration of the first-fit collector (`FFComps.fc`)
/// is described by `holds x d`: not stopped, its phase, the free list's head
/// at the bottom block, its major heap representing `mk d.dst`, its nursery
/// and the model nursery it represents, its roots, an empty remembered set.
/// `wd d` is then a world that represents it, and every world that does reads
/// the same (`views_wd`), so the program's obligations and the phase checks
/// are statements about `wd d`.
///
/// One lemma per event: from `holds x d`, the configuration after the event
/// is described by the next description, given the model heap's update as a
/// hypothesis on the closed forms (`R.heq (update (mk st)) (mk st')`), which
/// each run proves by computation.

module GC.Spec.Top.FFWStep

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteRep
open GC.Spec.Top.Run
open GC.Spec.Top.RunFacts
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.FFWModel
open GC.Spec.Top.FFWState
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module FC = GC.Spec.Top.FFComps
module FWA = GC.Spec.Top.FFWAlloc
module FWS = GC.Spec.Top.FFWSweep
module FM0 = GC.Spec.Top.FFWMinor0
module FSw = GC.Spec.Top.FFSweep
module FM = GC.Spec.Top.FFMinor
module BB = GC.Spec.Top.ByteBarrier
module BM = GC.Spec.Top.ByteMark
module TM = GC.Spec.Top.ToyMark
module Y = GC.Spec.Top.Young
module FS = GC.Spec.FusedSweep
module GMH = GC.Gen.MinorHeap

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let fc : comps = FC.fc

/// ---------------------------------------------------------------------------
/// Descriptions
/// ---------------------------------------------------------------------------

noeq type dsc = {
  dph : T.phase U64.t;
  dst : wst;
  dys : GMH.minor_state;
  dym : M.mheap;
  drt : list M.value;
}

[@@"opaque_to_smt"]
let holds (x: config fc) (d: dsc) : prop =
  x.stopped == false /\ x.ph == d.dph /\ U64.v (x.ast <: ffst).fp == base + 8 /\
  brepr (mk d.dst) x.w.cmaj /\ x.w.cyng == d.dys /\ Y.yrepr d.dym d.dys /\
  x.w.croots == d.drt /\ x.w.crem == [] /\ x.ms == None /\
  brep_ok (mk d.dst) /\ R.canonical (mk d.dst)

let holds_def (x: config fc) (d: dsc)
  : Lemma (holds x d <==>
           (x.stopped == false /\ x.ph == d.dph /\ U64.v (x.ast <: ffst).fp == base + 8 /\
            brepr (mk d.dst) x.w.cmaj /\ x.w.cyng == d.dys /\ Y.yrepr d.dym d.dys /\
            x.w.croots == d.drt /\ x.w.crem == [] /\ x.ms == None /\
            brep_ok (mk d.dst) /\ R.canonical (mk d.dst)))
  = reveal_opaque (`%holds) (holds x d)

let reveal_holds (_: unit)
  : Lemma (forall (x: config fc) (d: dsc). holds x d <==>
           (x.stopped == false /\ x.ph == d.dph /\ U64.v (x.ast <: ffst).fp == base + 8 /\
            brepr (mk d.dst) x.w.cmaj /\ x.w.cyng == d.dys /\ Y.yrepr d.dym d.dys /\
            x.w.croots == d.drt /\ x.w.crem == [] /\ x.ms == None /\
            brep_ok (mk d.dst) /\ R.canonical (mk d.dst)))
  = FStar.Classical.forall_intro_2 holds_def

let wd (d: dsc) : M.world = { M.maj = mk d.dst; M.yng = d.dym; M.roots = d.drt; M.rem = [] }

let yrepr_heq (m1 m2: M.mheap) (ms: GMH.minor_state)
  : Lemma (requires Y.yrepr m1 ms /\ Y.yrepr m2 ms) (ensures R.heq m1 m2)
  = BM.yrepr_heq m1 ms; BM.yrepr_heq m2 ms

let views_two (x: config fc) (w1 w2: M.world)
  : Lemma (requires views x w1 /\ views x w2) (ensures wheq w1 w2)
  = yrepr_heq w1.M.yng w2.M.yng x.w.cyng

let views_d (x: config fc) (d: dsc) : Lemma (requires holds x d) (ensures views x (wd d)) = reveal_holds ()

/// **The description's world represents the configuration, and so does
/// `vw x`, with the same reading.**
/// `wheq`, the other way round.
let wheq_sym (w1 w2: M.world) : Lemma (requires wheq w1 w2) (ensures wheq w2 w1)
  = R.heq_sym w1.M.maj w2.M.maj;
    R.heq_sym w1.M.yng w2.M.yng

let views_wd (x: config fc) (d: dsc)
  : Lemma (requires holds x d)
          (ensures views x (wd d) /\ has_view x /\ wheq (vw x) (wd d) /\
                   (forall (w1 w2: M.world). views x w1 /\ views x w2 ==> wheq w1 w2))
  = reveal_holds ();
    FStar.Classical.forall_intro_2 (fun w1 w2 -> FStar.Classical.move_requires (views_two x w1) w2);
    views_d x d;
    assert (has_view x);
    vw_views x

/// The program's obligations, on the description's world.
let mutator_wd (x: config fc) (d: dsc) (e: event)
  : Lemma (requires holds x d /\ mutator_ok_w fc (wd d) e) (ensures mutator_ok x e)
  = reveal_holds ();
    views_wd x d;
    mutator_of_view x (wd d) e

/// The model heap a configuration reads is `mk d.dst`.
let mj_wd (x: config fc) (d: dsc)
  : Lemma (requires holds x d) (ensures R.heq (mj x) (mk d.dst))
  = reveal_holds ();
    views_wd x d

let mark_done_wd (x: config fc) (d: dsc)
  : Lemma (requires holds x d) (ensures T.mark_done (mj x) <==> T.no_grey (mk d.dst))
  = reveal_holds ();
    mj_wd x d

/// ---------------------------------------------------------------------------
/// The initial configuration
/// ---------------------------------------------------------------------------

let d0 : dsc = { dph = T.Idle; dst = st0; dys = FM0.ms0; dym = M.empty_heap ywords; drt = [] }

let init_holds (es: list event)
  : Lemma (requires ff_room) (ensures holds (at fc msize ywords es 0) d0)
  = reveal_holds ();
    at_zero fc msize ywords es;
    init_repr ();
    init_ok ();
    init_facts ();
    Y.yinit_ok' ywords;
    FM0.yinit_ms0 ywords

/// ---------------------------------------------------------------------------
/// Model helpers
/// ---------------------------------------------------------------------------

let brep_size_of (m: M.mheap) (g: heap) : Lemma (requires brepr m g) (ensures m.M.size == msize) = ()

let fill_heq (h h': M.mheap) (o: nat) (vs: list M.value)
  : Lemma (requires R.heq h h') (ensures R.heq (M.fill h o vs) (M.fill h' o vs))
  = ()

let brep_of_heq (m m': M.mheap)
  : Lemma (requires brep_ok m /\ R.canonical m /\ R.heq m m') (ensures brep_ok m' /\ R.canonical m')
  = brep_heq m m';
    R.canonical_heq m m'

/// The lowest grey block is the one a slice scans.
#push-options "--fuel 1"
let rec find_grey_lt (h: M.mheap) (n: nat)
  : Lemma (ensures (match TM.find_grey h n with Some g -> g < n | None -> True)) (decreases n)
  = if n > 0 then find_grey_lt h (n - 1)

let rec find_grey_low (h: M.mheap) (n t: nat)
  : Lemma (requires M.is_block h t /\ M.col_of h t == M.Grey /\ t < n /\
                    (forall (o: nat). o < t /\ M.is_block h o ==> M.col_of h o <> M.Grey))
          (ensures TM.find_grey h n == Some t) (decreases n)
  = if n - 1 > t then find_grey_low h (n - 1) t
    else begin TM.find_grey_spec h (n - 1); find_grey_lt h (n - 1) end

let rec find_grey_heq (h h': M.mheap) (n: nat)
  : Lemma (requires R.heq h h') (ensures TM.find_grey h n == TM.find_grey h' n) (decreases n)
  = if n > 0 then find_grey_heq h h' (n - 1)
#pop-options

/// ---------------------------------------------------------------------------
/// The steps
/// ---------------------------------------------------------------------------

/// No young pointer: the Fill remembers nothing.
let rec no_young (vs: list M.value) : bool =
  match vs with
  | [] -> true
  | v :: tl -> (match v with M.VPtr (M.Young _) -> false | _ -> true) && no_young tl

#push-options "--fuel 1"
let rec binit_rem (g: heap) (o i: nat) (vs: list M.value)
  : Lemma (requires no_young vs == true) (ensures snd (BB.binit_from g [] o i vs) == []) (decreases vs)
  = match vs with
    | [] -> ()
    | v :: tl ->
      let g1 = if pos (o + 1 + i) < heap_size then write_word g (hp (o + 1 + i)) (concv v) else g in
      binit_rem g1 o (i + 1) tl
#pop-options

let fill_shape (m: M.mheap) (o: nat) (vs: list M.value) (w: nat)
  : Lemma (requires brep_ok m /\ M.is_block m o /\ L.length vs == M.wz_of m o /\ R.storable_all byte_rep vs)
          (ensures R.field_word m w ==> storable_w ((M.fill m o vs).M.body w))
  = if FStar.IndefiniteDescription.strong_excluded_middle (R.field_word m w) then begin
      if o < w && w - o - 1 < L.length vs then L.lemma_index_memP vs (w - o - 1)
      else brep_store m w
    end

let fill_same_shape (m: M.mheap) (o: nat) (vs: list M.value)
  : Lemma (requires brep_ok m /\ R.canonical m /\ M.is_block m o /\ L.length vs == M.wz_of m o /\
                    R.storable_all byte_rep vs)
          (ensures brep_ok (M.fill m o vs) /\ R.canonical (M.fill m o vs))
  = FStar.Classical.forall_intro (brep_tag m);
    FStar.Classical.forall_intro (fill_shape m o vs);
    let nf (w: nat) : Lemma (~(R.field_word m w) ==> (M.fill m o vs).M.body w == m.M.body w)
      = if o < w && w - o - 1 < L.length vs then begin
          brep_block m o;
          assert (M.covers m o w)
        end in
    FStar.Classical.forall_intro nf;
    same_shape_ok m (M.fill m o vs)

/// The Fill after first-fit, on the model.
#push-options "--z3rlimit 40"
let alloc_fill (ph: T.phase U64.t) (h: heap) (s: ffst) (m: M.mheap) (f: nat) (sz: M.size_t) (tag: M.tag_t)
               (vs: list M.value) (m': M.mheap)
  : Lemma (requires brepr m h /\ FWA.head_ok m f /\ sz + 2 <= f /\ U64.v s.fp == base + 8 /\ tag <> M.infix_tag /\
                    L.length vs == sz /\ R.storable_all byte_rep vs /\ no_young vs == true /\
                    R.heq (M.fill (FWA.split m f sz tag (T.colour_at ffk ph (f - sz))) (f - sz) vs) m')
          (ensures (let (h', s', r) = ffalloc ph h s sz tag in
                    let (h'', rem') = BB.binit h' [] (f - sz) vs in
                    r == T.Ok (f - sz) /\ U64.v s'.fp == base + 8 /\ brepr m' h'' /\ rem' == []))
  = FWA.ffalloc_head ph h s m f sz tag;
    let col = T.colour_at ffk ph (f - sz) in
    let o = f - sz in
    let m1 = FWA.split m f sz tag col in
    FWA.split_def m f sz tag col;
    brep_size m; brep_block m 0;
    let (h', s', _) = ffalloc ph h s sz tag in
    assert (M.is_block m1 o /\ M.wz_of m1 o == sz);
    BB.binit_from_ok h' [] o 0 vs;
    binit_rem h' o 0 vs;
    BB.fill_at_zero (cabs h') o vs;
    fill_heq m1 (cabs h') o vs
#pop-options

/// **EAlloc**: first-fit from the bottom block, then the Fill.
#push-options "--z3rlimit 40"
let step_alloc (x: config fc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (st': wst)
  : Lemma (requires holds x d /\ sz + 2 <= d.dst.f /\ tag <> M.infix_tag /\ L.length vs == sz /\
                    R.storable_all byte_rep vs /\ no_young vs == true /\ d.dst.f < msize /\
                    R.heq (M.fill (FWA.split (mk d.dst) d.dst.f sz tag (T.colour_at ffk d.dph (d.dst.f - sz)))
                                  (d.dst.f - sz) vs) (mk st'))
          (ensures holds (step fc x (EAlloc sz tag vs)) ({ d with dst = st'; drt = M.VPtr (M.Major (d.dst.f - sz)) :: d.drt }))
  = reveal_holds ();
    let m = mk d.dst in
    let s : ffst = x.ast in
    assert (m.M.hd 0 == Some (FWA.free_hdr d.dst.f));
    alloc_fill x.ph x.w.cmaj s m d.dst.f sz tag vs (mk st');
    let col = T.colour_at ffk d.dph (d.dst.f - sz) in
    let m1 = FWA.split m d.dst.f sz tag col in
    FWA.split_ok m d.dst.f sz tag col;
    FWA.split_def m d.dst.f sz tag col;
    fill_same_shape m1 (d.dst.f - sz) vs;
    brep_of_heq (M.fill m1 (d.dst.f - sz) vs) (mk st')
#pop-options

#push-options "--fuel 1"
let not_young_slot (h: M.mheap) (o i: nat) (v: M.value)
  : Lemma (requires no_young [v] == true) (ensures T.young_slot h o i v == false)
  = ()
#pop-options

let write_parts (marking: bool) (m m': M.mheap) (g: heap) (o i: nat) (v: M.value)
  : Lemma (requires brepr m g /\ M.is_block m o /\ i < M.wz_of m o /\ storable_w v /\ no_young [v] == true /\
                    R.heq (M.set_field (BB.tdark marking m o i) o i v) m')
          (ensures (let (g', rem') = BB.bwrite marking g [] o i v in brepr m' g' /\ rem' == []))
  = BB.bwrite_cabs marking m g [] o i v;
    BB.tbwrite_eq marking m [] o i v;
    not_young_slot m o i v;
    not_young_slot (cabs g) o i v

/// **EWrite** to a major block.
let step_write (x: config fc) (d: dsc) (o i: nat) (v: M.value) (st': wst)
  : Lemma (requires holds x d /\ M.is_block (mk d.dst) o /\ i < M.wz_of (mk d.dst) o /\ storable_w v /\
                    no_young [v] == true /\
                    R.heq (M.set_field (BB.tdark (T.is_marking d.dph) (mk d.dst) o i) o i v) (mk st') /\
                    okm (mk st'))
          (ensures holds (step fc x (EWrite (M.Major o) i v)) ({ d with dst = st' }))
  = okm_def (mk st');
    reveal_holds ();
    write_parts (T.is_marking x.ph) (mk d.dst) (mk st') x.w.cmaj o i v

/// **ERead** of a major block's field.
let step_read (x: config fc) (d: dsc) (o i: nat)
  : Lemma (requires holds x d /\ M.is_block (mk d.dst) o /\ i < M.wz_of (mk d.dst) o)
          (ensures holds (step fc x (ERead (M.Major o) i)) ({ d with drt = M.field (mk d.dst) o i :: d.drt }))
  = reveal_holds ();
    byte_major_reads (mk d.dst) x.w.cmaj

/// **ERoots**.
let step_roots (x: config fc) (d: dsc) (rs: list M.value)
  : Lemma (requires holds x d) (ensures holds (step fc x (ERoots rs)) ({ d with drt = rs }))
  = reveal_holds ();
    ()

let start_parts (x: config fc) (d: dsc) (st': wst)
  : Lemma (requires holds x d /\ T.mark_start_pre (wd d) /\ R.heq (TM.tmstart (wd d)) (mk st'))
          (ensures brepr (mk st') (BM.bstart x.w))
  = reveal_holds ();
    views_d x d;
    BM.bstart_cabs x.w (wd d)

/// **EStart**: the mark greys the outside references.
#push-options "--z3rlimit 40"
let step_start (x: config fc) (d: dsc) (st': wst)
  : Lemma (requires holds x d /\ T.mark_start_pre (wd d) /\ R.heq (TM.tmstart (wd d)) (mk st') /\
                    okm (mk st'))
          (ensures holds (step fc x EStart) ({ d with dph = T.Marking; dst = st' }))
  = okm_def (mk st');
    reveal_holds ();
    start_parts x d st';
    assert (fc.m.T.mstart x.w == BM.bstart x.w)
#pop-options

let slice_parts (g: heap) (m m': M.mheap) (t: nat)
  : Lemma (requires brepr m g /\ M.well_formed m /\ M.is_block m t /\ M.col_of m t == M.Grey /\
                    R.heq (TM.tmslice_with m t) m')
          (ensures brepr m' (fst (T.mmoves BM.bmark g None (BM.obj_mv m t))) /\
                   snd (T.mmoves BM.bmark g None (BM.obj_mv m t)) == None)
  = BM.obj_moves_bytes g m t;
    let g' = fst (T.mmoves BM.bmark g None (BM.obj_mv m t)) in
    R.heq_sym (TM.tmslice_with m t) m';
    R.heq_trans m' (TM.tmslice_with m t) (cabs g')

/// **ESlice**: a grey block scanned whole (its moves, `BM.obj_mv`).
#push-options "--z3rlimit 40"
let step_slice (x: config fc) (d: dsc) (t: nat) (st': wst) (mvs: list T.move)
  : Lemma (requires holds x d /\ M.is_block (mk d.dst) t /\ M.col_of (mk d.dst) t == M.Grey /\
                    mvs == BM.obj_mv (mk d.dst) t /\ R.heq (TM.tmslice_with (mk d.dst) t) (mk st') /\
                    okm (mk st'))
          (ensures holds (step fc x (ESlice mvs)) ({ d with dst = st' }))
  = okm_def (mk st');
    holds_def x d;
    let x' = step fc x (ESlice mvs) in
    holds_def x' ({ d with dst = st' });
    reveal_opaque (`%brep_ok) (brep_ok (mk d.dst));
    slice_parts x.w.cmaj (mk d.dst) (mk st') t;
    assert (fc.m == BM.bmark);
    assert (x'.w.cmaj == fst (T.mmoves BM.bmark x.w.cmaj None mvs) /\ x'.ms == snd (T.mmoves BM.bmark x.w.cmaj None mvs))
#pop-options

/// **EHandover**: the sweep starts at the bottom.
let step_handover (x: config fc) (d: dsc)
  : Lemma (requires holds x d)
          (ensures holds (step fc x EHandover) ({ d with dph = T.Sweeping (FWS.cur 0) }))
  = reveal_holds ();
    FWS.cur0 ()

/// **ESweep** at the bottom free block.
let step_sweep_head (x: config fc) (d: dsc)
  : Lemma (requires holds x d /\ d.dph == T.Sweeping (FWS.cur 0) /\ d.dst.f + 1 <= msize)
          (ensures holds (step fc x ESweep) ({ d with dph = T.Sweeping (FWS.cur (d.dst.f + 1)) }))
  = reveal_holds ();
    let s : ffst = x.ast in
    FWS.sweep_head x.w.cmaj s (mk d.dst) d.dst.f;
    let (c', _, _, _) = FSw.ffstep (FWS.cur 0) x.w.cmaj s in
    FWS.cur_v (d.dst.f + 1);
    U64.v_inj c' (FWS.cur (d.dst.f + 1))

let black_parts (h: heap) (s: ffst) (m m': M.mheap) (o: nat)
  : Lemma (requires brepr m h /\ brep_ok m /\ R.canonical m /\ M.is_block m o /\ M.col_of m o == M.Black /\
                    o + M.wz_of m o + 1 <= msize /\ R.heq (M.set_col m o M.White) m')
          (ensures (let (c', h', s', _) = FSw.ffstep (FWS.cur o) h s in
                    c' == FWS.cur (o + M.wz_of m o + 1) /\ s'.fp == s.fp /\ brepr m' h' /\
                    brep_ok m' /\ R.canonical m'))
  = FWS.sweep_black h s m o;
    let (c', _, _, _) = FSw.ffstep (FWS.cur o) h s in
    FWS.cur_v (o + M.wz_of m o + 1);
    U64.v_inj c' (FWS.cur (o + M.wz_of m o + 1));
    recol_shape m o M.White;
    same_shape_ok m (M.set_col m o M.White);
    brep_of_heq (M.set_col m o M.White) m'

/// **ESweep** at a survivor.
let step_sweep_black (x: config fc) (d: dsc) (o: nat) (st': wst)
  : Lemma (requires holds x d /\ d.dph == T.Sweeping (FWS.cur o) /\ M.is_block (mk d.dst) o /\
                    M.col_of (mk d.dst) o == M.Black /\ o + M.wz_of (mk d.dst) o + 1 <= msize /\
                    R.heq (M.set_col (mk d.dst) o M.White) (mk st'))
          (ensures holds (step fc x ESweep)
                         ({ d with dph = T.Sweeping (FWS.cur (o + M.wz_of (mk d.dst) o + 1)); dst = st' }))
  = reveal_holds ();
    black_parts x.w.cmaj x.ast (mk d.dst) (mk st') o

let white_parts (h: heap) (s: ffst) (m m': M.mheap) (f o: nat)
  : Lemma (requires brepr m h /\ FWA.head_ok m f /\ f >= 1 /\ M.is_block m o /\ M.col_of m o == M.White /\
                    o > f + 1 /\ FWS.blue_below m o /\ o + M.wz_of m o + 1 <= msize /\
                    R.heq (FWS.freed m o) m')
          (ensures (let (c', h', s', _) = FSw.ffstep (FWS.cur o) h s in
                    c' == FWS.cur (o + M.wz_of m o + 1) /\ s'.fp == s.fp /\ brepr m' h'))
  = FWS.sweep_white h s m f o;
    let (c', _, _, _) = FSw.ffstep (FWS.cur o) h s in
    FWS.cur_v (o + M.wz_of m o + 1);
    U64.v_inj c' (FWS.cur (o + M.wz_of m o + 1))

/// **ESweep** at garbage.
let step_sweep_white (x: config fc) (d: dsc) (o: nat) (st': wst)
  : Lemma (requires holds x d /\ d.dph == T.Sweeping (FWS.cur o) /\ M.is_block (mk d.dst) o /\
                    M.col_of (mk d.dst) o == M.White /\ o > d.dst.f + 1 /\ d.dst.f >= 1 /\
                    FWS.blue_below (mk d.dst) o /\ o + M.wz_of (mk d.dst) o + 1 <= msize /\
                    R.heq (FWS.freed (mk d.dst) o) (mk st') /\ okm (mk st'))
          (ensures holds (step fc x ESweep)
                         ({ d with dph = T.Sweeping (FWS.cur (o + M.wz_of (mk d.dst) o + 1)); dst = st' }))
  = okm_def (mk st');
    reveal_holds ();
    assert ((mk d.dst).M.hd 0 == Some (FWA.free_hdr d.dst.f));
    white_parts x.w.cmaj x.ast (mk d.dst) (mk st') d.dst.f o

/// **EEnd**.
let step_end (x: config fc) (d: dsc)
  : Lemma (requires holds x d) (ensures holds (step fc x EEnd) ({ d with dph = T.Idle }))
  = reveal_holds ();
    ()

/// **EMinor** of the empty nursery.
#push-options "--z3rlimit 40"
let step_minor0 (x: config fc) (d: dsc)
  : Lemma (requires holds x d /\ d.dys == FM0.ms0) (ensures holds (step fc x EMinor) d)
  = reveal_holds ();
    let s : ffst = x.ast in
    FM0.pcollect_empty x.ph s x.w;
    FM0.map_fwd_none (Y.ycabs FM0.ms0) x.w.croots;
    FM0.yreset_yinit FM0.ms0;
    cabs_set_low x.w.cmaj s.lo;
    low_set_low x.w.cmaj s.lo
#pop-options

/// **EYoungAlloc**, when the nursery has room.
#push-options "--z3rlimit 40"
let step_yalloc (x: config fc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires holds x d /\ Some? (Y.yalloc d.dys sz tag vs) /\ tag <> M.infix_tag /\ L.length vs == sz /\
                    (forall (v: M.value). L.memP v vs ==> storable_w v))
          (ensures (let Some (o, ms') = Y.yalloc d.dys sz tag vs in
                    holds (step fc x (EYoungAlloc sz tag vs))
                          ({ d with dys = ms'; dym = M.young_alloc d.dym o sz tag vs;
                                    drt = M.VPtr (M.Young o) :: d.drt })))
  = holds_def x d;
    Y.yalloc_repr d.dym d.dys sz tag vs;
    let Some (o, ms') = Y.yalloc d.dys sz tag vs in
    holds_def (step fc x (EYoungAlloc sz tag vs))
              ({ d with dys = ms'; dym = M.young_alloc d.dym o sz tag vs; drt = M.VPtr (M.Young o) :: d.drt })
#pop-options

/// A described heap is one a byte heap represents.
let holds_brep (x: config fc) (d: dsc)
  : Lemma (requires holds x d) (ensures okm (mk d.dst))
  = holds_def x d; okm_def (mk d.dst)
