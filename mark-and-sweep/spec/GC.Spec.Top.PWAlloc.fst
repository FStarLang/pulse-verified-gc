/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWAlloc - an allocation of a pages witness run
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  `EAlloc` on a described configuration
/// (GC.Spec.Top.PWDesc), from the allocator's contract (`alloc_at`) and the
/// byte barrier's Fill (`ByteBarrier.binit_from_ok`):
///   - a page left in the budget gives room, so the allocation succeeds
///     (`PWPages.room_of`), at a block that was free;
///   - the new block has the colour rule's colour and the Fill's fields;
///   - every block in use keeps its header and fields;
///   - the allocator's invariant holds after the Fill, and the allocation
///     costs one page of the budget.
/// Where the block is, is not computed: it is the allocator's answer
/// (`aaddr`).

module GC.Spec.Top.PWAlloc

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
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
module BB = GC.Spec.Top.ByteBarrier
module PIn = GC.Spec.Top.PagesInst
module PWP = GC.Spec.Top.PWPages
module FWS = GC.Spec.Top.FFWStep
module Y = GC.Spec.Top.Young

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The allocator's result, by parts.
let a_h (x: config pc) (sz: M.size_t) (tag: M.tag_t) : GTot heap =
  let (h', _, _) = pa.T.alloc x.ph x.w.cmaj (stx x) sz tag in h'
let a_s (x: config pc) (sz: M.size_t) (tag: M.tag_t) : GTot pst =
  let (_, s', _) = pa.T.alloc x.ph x.w.cmaj (stx x) sz tag in s'
let a_r (x: config pc) (sz: M.size_t) (tag: M.tag_t) : GTot T.result =
  let (_, _, r) = pa.T.alloc x.ph x.w.cmaj (stx x) sz tag in r

/// The allocator's answer.
let aaddr (x: config pc) (sz: M.size_t) (tag: M.tag_t) : GTot nat =
  match a_r x sz tag with
  | T.Ok o -> o
  | _ -> 0

let a_parts (x: config pc) (sz: M.size_t) (tag: M.tag_t)
  : Lemma (pa.T.alloc x.ph x.w.cmaj (stx x) sz tag == (a_h x sz tag, a_s x sz tag, a_r x sz tag))
  = ()

/// The description after the allocation.
let dalloc (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) : GTot dsc =
  let o = aaddr x sz tag in
  { d with db = (fun (y: nat) -> if y = o then Some ({ bw = sz; bt = tag; bc = T.colour_at pk x.ph o;
                                                       blv = true; bf = vs })
                                 else d.db y);
           drt = M.VPtr (M.Major o) :: d.drt; dj = d.dj + 1 }

/// What the allocation needs.
let apre (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) : prop =
  cok /\ holds x d /\ d.dj < n_pages /\ sz + 1 <= small_max /\
  tag <> M.infix_tag /\ L.length vs == sz /\ R.storable_all byte_rep vs /\ FWS.no_young vs == true /\
  (M.scannable tag ==> (forall (v: M.value). L.memP v vs ==> T.sound_value pa x.ph (stx x) x.w.cmaj (mx x) v))

/// In use, read on the canonical model of any heap.
let iu_any (s: pst) (h: heap) (m: M.mheap) (o: nat)
  : Lemma (requires R.heq m (cabs h))
          (ensures T.in_use pa s h m o == (M.is_block (cabs h) o && M.col_of (cabs h) o <> M.Blue))
  = PIn.pfree_blue h s h o

/// The Fill writes only the new block's words.
let fill_other (m: M.mheap) (o y i: nat) (vs: list M.value)
  : Lemma (requires M.well_formed m /\ M.is_block m o /\ L.length vs == M.wz_of m o /\
                    M.is_block m y /\ y <> o /\ i < M.wz_of m y)
          (ensures M.field (M.fill m o vs) y i == M.field m y i)
  = let w = y + 1 + i in
    if o < w && w - o - 1 < L.length vs then begin
      assert (M.covers m o w);
      assert (M.covers m y w)
    end

let fill_wf (m: M.mheap) (o: nat) (vs: list M.value)
  : Lemma (requires M.well_formed m) (ensures M.well_formed (M.fill m o vs))
  = assert (forall (y w: nat). M.covers (M.fill m o vs) y w == M.covers m y w)

/// A block whose words were free was not in use.
let was_free (s: pst) (h: heap) (m m': M.mheap) (o: nat)
  : Lemma (requires M.well_formed m /\ M.is_block m' o /\
                    (forall (w: nat). M.covers m' o w ==> T.free_word pa s h m w))
          (ensures T.in_use pa s h m o == false)
  = assert (M.covers m' o o);
    if T.in_use pa s h m o then begin
      assert (M.covers m o o);
      eliminate exists (o': nat). M.covers m o' o /\ pa.T.free s h o'
      with ()
    end

/// What the contract gives, on the models: `m'` the model of the heap the
/// allocator returns.
let apost (x: config pc) (sz: M.size_t) (tag: M.tag_t) (m': M.mheap) : prop =
  let h' = a_h x sz tag in let st' = a_s x sz tag in let r = a_r x sz tag in
  let o = aaddr x sz tag in
  T.Ok? r /\ T.Ok?._0 r == o /\ brepr m' h' /\ M.well_formed m' /\ M.is_block m' o /\
  m'.M.hd o == Some ({ M.wz = sz; M.tag = tag; M.col = T.colour_at pk x.ph o }) /\
  (forall (z: nat). T.in_use pa st' h' m' z <==> (iu x z \/ z == o)) /\
  (forall (z: nat). iu x z ==> M.same_block (mx x) m' z) /\
  (forall (w: nat). M.covers m' o w ==> T.free_word pa (stx x) x.w.cmaj (mx x) w) /\
  (forall (vs: list M.value) (h'': heap).
     L.length vs == sz /\ (M.scannable tag ==> (forall (v: M.value). L.memP v vs ==> T.sound_value pa x.ph (stx x) x.w.cmaj (mx x) v)) /\
     byte_rep.R.repr (M.fill m' o vs) h'' ==> pa.T.inv x.ph h'' st')

#push-options "--z3rlimit 40"
let apost_of (x: config pc) (sz: M.size_t) (tag: M.tag_t) (m': M.mheap)
  : Lemma (requires (let h' = a_h x sz tag in let st' = a_s x sz tag in let r = a_r x sz tag in
                     T.Ok? r /\ brepr m' h' /\ T.alloc_post byte_rep pa x.ph x.w.cmaj (stx x) sz tag h' st' r (mx x) m'))
          (ensures apost x sz tag m')
  = a_parts x sz tag;
    let h' = a_h x sz tag in let st' = a_s x sz tag in let r = a_r x sz tag in
    let o = aaddr x sz tag in
    assert (T.Ok?._0 r == o);
    assert (brepr m' h' /\ M.well_formed m' /\ M.is_block m' o);
    assert (m'.M.hd o == Some ({ M.wz = sz; M.tag = tag; M.col = T.colour_at pk x.ph o }));
    assert (forall (z: nat). T.in_use pa st' h' m' z <==> (iu x z \/ z == o));
    assert (forall (z: nat). iu x z ==> M.same_block (mx x) m' z);
    assert (forall (w: nat). M.covers m' o w ==> T.free_word pa (stx x) x.w.cmaj (mx x) w);
    assert (forall (vs: list M.value) (h'': heap).
     L.length vs == sz /\ (M.scannable tag ==> (forall (v: M.value). L.memP v vs ==> T.sound_value pa x.ph (stx x) x.w.cmaj (mx x) v)) /\
     byte_rep.R.repr (M.fill m' o vs) h'' ==> pa.T.inv x.ph h'' st');
    assert_norm (apost x sz tag m' <==>
      (let h' = a_h x sz tag in let st' = a_s x sz tag in let r = a_r x sz tag in
       let o = aaddr x sz tag in
       T.Ok? r /\ T.Ok?._0 r == o /\ brepr m' h' /\ M.well_formed m' /\ M.is_block m' o /\
       m'.M.hd o == Some ({ M.wz = sz; M.tag = tag; M.col = T.colour_at pk x.ph o }) /\
       (forall (z: nat). T.in_use pa st' h' m' z <==> (iu x z \/ z == o)) /\
       (forall (z: nat). iu x z ==> M.same_block (mx x) m' z) /\
       (forall (w: nat). M.covers m' o w ==> T.free_word pa (stx x) x.w.cmaj (mx x) w) /\
       (forall (vs: list M.value) (h'': heap).
          L.length vs == sz /\ (M.scannable tag ==> (forall (v: M.value). L.memP v vs ==> T.sound_value pa x.ph (stx x) x.w.cmaj (mx x) v)) /\
          byte_rep.R.repr (M.fill m' o vs) h'' ==> pa.T.inv x.ph h'' st')))
#pop-options

#push-options "--z3rlimit 40"
let alloc_model (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires apre x d sz tag vs) (ensures exists (m': M.mheap). apost x sz tag m')
  = a_parts x sz tag;
    holds_elim x d;
    PWP.room_of x.ph x.w.cmaj (stx x) sz d.dj;
    brepr_cabs x.w.cmaj;
    let h' = a_h x sz tag in let st' = a_s x sz tag in let r = a_r x sz tag in
    assert (T.alloc_pre pa x.ph x.w.cmaj (stx x) tag (mx x));
    cok_alloc x.ph x.w.cmaj (stx x) sz tag;
    assert (exists (m': M.mheap). brepr m' h' /\ T.alloc_post byte_rep pa x.ph x.w.cmaj (stx x) sz tag h' st' r (mx x) m');
    eliminate exists (m': M.mheap). brepr m' h' /\ T.alloc_post byte_rep pa x.ph x.w.cmaj (stx x) sz tag h' st' r (mx x) m'
    with begin
      assert (T.Ok? r);
      apost_of x sz tag m'
    end
#pop-options

let kinds_of (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t)
  : Lemma (requires holds x d /\ sz + 1 <= small_max)
          (ensures (let st' = a_s x sz tag in PWP.kinds_ok st'.ps (d.dj + 1)))
  = a_parts x sz tag;
    holds_elim x d;
    PWP.palloc_kinds x.ph x.w.cmaj (stx x) sz tag d.dj

/// The configuration after the allocation.
let x_after (x: config pc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires T.Ok? (let r = a_r x sz tag in r) /\ x.w.crem == [])
          (ensures (let h' = a_h x sz tag in let st' = a_s x sz tag in
                    let o = aaddr x sz tag in
                    let x' = step pc x (EAlloc sz tag vs) in
                    x'.w.cmaj == fst (BB.binit h' [] o vs) /\ x'.w.crem == snd (BB.binit h' [] o vs) /\
                    stx x' == st' /\ x'.ph == x.ph /\ x'.stopped == x.stopped /\ x'.w.cyng == x.w.cyng /\
                    x'.w.croots == M.VPtr (M.Major o) :: x.w.croots))
  = a_parts x sz tag;
    ()

/// The heap after the Fill: its model, the remembered set, the invariant.
#push-options "--z3rlimit 40"
let fill_model (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (m': M.mheap)
  : Lemma (requires apre x d sz tag vs /\ apost x sz tag m')
          (ensures (let h' = a_h x sz tag in let st' = a_s x sz tag in let r = a_r x sz tag in
                    let o = aaddr x sz tag in
                    let (h'', rem') = BB.binit h' [] o vs in
                    R.heq (cabs h'') (M.fill m' o vs) /\ rem' == [] /\ pa.T.inv x.ph h'' st'))
  = a_parts x sz tag;
    let h' = a_h x sz tag in let st' = a_s x sz tag in let r = a_r x sz tag in
    let o = aaddr x sz tag in
    assert (M.is_block (cabs h') o /\ M.wz_of (cabs h') o == sz);
    BB.binit_from_ok h' [] o 0 vs;
    FWS.binit_rem h' o 0 vs;
    BB.fill_at_zero (cabs h') o vs;
    let (h'', _) = BB.binit h' [] o vs in
    let fa = BB.fill_at (cabs h') o 0 vs in
    assert (R.heq (cabs h'') fa);
    R.heq_sym (M.fill (cabs h') o vs) fa;
    R.heq_trans (cabs h'') fa (M.fill (cabs h') o vs);
    R.heq_sym m' (cabs h');
    FWS.fill_heq (cabs h') m' o vs;
    R.heq_trans (cabs h'') (M.fill (cabs h') o vs) (M.fill m' o vs);
    R.heq_sym (cabs h'') (M.fill m' o vs);
    assert (brepr (M.fill m' o vs) h'');
    assert (byte_rep.R.repr (M.fill m' o vs) h'');
    assert (pa.T.inv x.ph h'' st')
#pop-options

/// The new block, described.
let new_o (x x': config pc) (d': dsc) (o: nat) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (m': M.mheap)
  : Lemma (requires x'.ph == x.ph /\ L.length vs == sz /\ R.heq (mx x') (M.fill m' o vs) /\
                    m'.M.hd o == Some ({ M.wz = sz; M.tag = tag; M.col = T.colour_at pk x.ph o }) /\
                    iu x' o == true)
          (ensures bk x' d' o ({ bw = sz; bt = tag; bc = T.colour_at pk x.ph o; blv = true; bf = vs }))
  = let aux (i: nat) : Lemma (i < sz ==> M.field (mx x') o i == vi vs i) = () in
    FStar.Classical.forall_intro aux

/// An old block, described as before.
#push-options "--z3rlimit 40"
let new_old (x x': config pc) (d d': dsc) (o y: nat) (vs: list M.value) (m': M.mheap) (b: bd)
  : Lemma (requires x'.ph == x.ph /\ d'.dk == d.dk /\ y <> o /\ bk x d y b /\
                    M.well_formed m' /\ M.is_block m' o /\ L.length vs == M.wz_of m' o /\
                    R.heq (mx x') (M.fill m' o vs) /\
                    (iu x' y == iu x y) /\ (iu x y ==> M.same_block (mx x) m' y /\ M.is_block (mx x) y))
          (ensures bk x' d' y b)
  = if iu x y then begin
      let aux (i: nat) : Lemma (i < b.bw ==> M.field (mx x') y i == M.field (mx x) y i)
        = if i < b.bw then fill_other m' o y i vs in
      FStar.Classical.forall_intro aux
    end
#pop-options

/// In use after the allocation.
let iu_after (x x': config pc) (st': pst) (h': heap) (m': M.mheap) (o: nat) (vs: list M.value) (z: nat)
  : Lemma (requires stx x' == st' /\ brepr m' h' /\ R.heq (mx x') (M.fill m' o vs) /\
                    (T.in_use pa st' h' m' z <==> (iu x z \/ z == o)))
          (ensures iu x' z == (iu x z || z = o))
  = iu_any st' x'.w.cmaj (mx x') z;
    iu_any st' h' m' z

let apost_iu (x: config pc) (sz: M.size_t) (tag: M.tag_t) (m': M.mheap) (z: nat)
  : Lemma (requires apost x sz tag m')
          (ensures (let h' = a_h x sz tag in let st' = a_s x sz tag in
                    brepr m' h' /\ (T.in_use pa st' h' m' z <==> (iu x z \/ z == aaddr x sz tag))))
  = ()

/// What the next configuration is, on the models.
let aft (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (m': M.mheap) : prop =
  let x' = step pc x (EAlloc sz tag vs) in
  let o = aaddr x sz tag in
  R.heq (mx x') (M.fill m' o vs) /\ x'.w.crem == [] /\
  pa.T.inv x'.ph x'.w.cmaj (stx x') /\ PWP.kinds_ok (stx x').ps (d.dj + 1) /\
  x'.ph == x.ph /\ x'.stopped == x.stopped /\ x'.w.cyng == x.w.cyng /\
  x'.w.croots == M.VPtr (M.Major o) :: x.w.croots /\ M.well_formed (mx x') /\
  (forall (z: nat). iu x' z == (iu x z || z = o)) /\ iu x o == false

/// The configuration after the allocation, on the models.
#push-options "--z3rlimit 40"
let after (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (m': M.mheap)
  : Lemma (requires apre x d sz tag vs /\ apost x sz tag m')
          (ensures aft x d sz tag vs m')
  = a_parts x sz tag;
    holds_elim x d;
    let h' = a_h x sz tag in let st' = a_s x sz tag in let r = a_r x sz tag in
    let o = aaddr x sz tag in
    let x' = step pc x (EAlloc sz tag vs) in
    x_after x sz tag vs;
    fill_model x d sz tag vs m';
    kinds_of x d sz tag;
    let (h'', rem') = BB.binit h' [] o vs in
    assert (x'.w.cmaj == h'' /\ x'.w.crem == rem' /\ stx x' == st');
    assert (R.heq (mx x') (M.fill m' o vs));
    fill_wf m' o vs;
    R.heq_sym (mx x') (M.fill m' o vs);
    PIn.wf_heq (M.fill m' o vs) (mx x');
    let iz (z: nat) : Lemma (iu x' z == (iu x z || z = o))
      = apost_iu x sz tag m' z;
        iu_after x x' st' h' m' o vs z in
    FStar.Classical.forall_intro iz;
    was_free (stx x) x.w.cmaj (mx x) m' o
#pop-options

let old_blk (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (m': M.mheap) (y: nat)
  : Lemma (requires apre x d sz tag vs /\ apost x sz tag m' /\ aft x d sz tag vs m' /\
                    Some? (d.db y) /\ y <> aaddr x sz tag)
          (ensures bk (step pc x (EAlloc sz tag vs)) (dalloc x d sz tag vs) y (Some?.v (d.db y)))
  = let o = aaddr x sz tag in
    let x' = step pc x (EAlloc sz tag vs) in
    holds_elim x d;
    holds_blk x d y;
    (if iu x y then iu_def x y);
    assert (iu x' y == iu x y);
    new_old x x' d (dalloc x d sz tag vs) o y vs m' (Some?.v (d.db y))

let des_blk (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (m': M.mheap) (y: nat)
  : Lemma (requires apre x d sz tag vs /\ aft x d sz tag vs m' /\ iu (step pc x (EAlloc sz tag vs)) y == true)
          (ensures Some? ((dalloc x d sz tag vs).db y))
  = if iu x y then holds_iu x d y

let blk_new (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (m': M.mheap) (y: nat)
  : Lemma (requires apre x d sz tag vs /\ apost x sz tag m' /\ aft x d sz tag vs m' /\
                    Some? ((dalloc x d sz tag vs).db y))
          (ensures bk (step pc x (EAlloc sz tag vs)) (dalloc x d sz tag vs) y (Some?.v ((dalloc x d sz tag vs).db y)))
  = let o = aaddr x sz tag in
    if y = o then new_o x (step pc x (EAlloc sz tag vs)) (dalloc x d sz tag vs) o sz tag vs m'
    else old_blk x d sz tag vs m' y

let blk_all (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (m': M.mheap) (y: nat)
  : Lemma (requires apre x d sz tag vs /\ apost x sz tag m' /\ aft x d sz tag vs m')
          (ensures Some? ((dalloc x d sz tag vs).db y) ==>
                   bk (step pc x (EAlloc sz tag vs)) (dalloc x d sz tag vs) y (Some?.v ((dalloc x d sz tag vs).db y)))
  = if Some? ((dalloc x d sz tag vs).db y) then blk_new x d sz tag vs m' y

let des_all (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (m': M.mheap) (y: nat)
  : Lemma (requires apre x d sz tag vs /\ aft x d sz tag vs m')
          (ensures iu (step pc x (EAlloc sz tag vs)) y == true ==> Some? ((dalloc x d sz tag vs).db y))
  = if iu (step pc x (EAlloc sz tag vs)) y then des_blk x d sz tag vs m' y

let kph_same (x x': config pc) (k: phk) : Lemma (requires x'.ph == x.ph) (ensures kph x' k <==> kph x k) = ()

let intro_new (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (m': M.mheap)
  : Lemma (requires holds x d /\ aft x d sz tag vs m' /\
                    (forall (y: nat). Some? ((dalloc x d sz tag vs).db y) ==>
                       bk (step pc x (EAlloc sz tag vs)) (dalloc x d sz tag vs) y (Some?.v ((dalloc x d sz tag vs).db y))) /\
                    (forall (y: nat). iu (step pc x (EAlloc sz tag vs)) y == true ==> Some? ((dalloc x d sz tag vs).db y)))
          (ensures holds (step pc x (EAlloc sz tag vs)) (dalloc x d sz tag vs))
  = holds_elim x d;
    kph_same x (step pc x (EAlloc sz tag vs)) d.dk;
    holds_intro (step pc x (EAlloc sz tag vs)) (dalloc x d sz tag vs)

/// **EAlloc** on a description.
#push-options "--z3rlimit 40"
let step_alloc (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires apre x d sz tag vs)
          (ensures T.Ok? (a_r x sz tag) /\ iu x (aaddr x sz tag) == false /\
                   holds (step pc x (EAlloc sz tag vs)) (dalloc x d sz tag vs))
  = alloc_model x d sz tag vs;
    let x' = step pc x (EAlloc sz tag vs) in
    let d' = dalloc x d sz tag vs in
    eliminate exists (m': M.mheap). apost x sz tag m'
    with begin
      after x d sz tag vs m';
      FStar.Classical.forall_intro (blk_all x d sz tag vs m');
      FStar.Classical.forall_intro (des_all x d sz tag vs m');
      intro_new x d sz tag vs m'
    end
#pop-options
