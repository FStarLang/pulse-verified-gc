/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWMinor - a minor collection of a pages witness run
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  `EMinor` on a described configuration
/// (GC.Spec.Top.PWDesc) whose nursery holds at most the two one-field
/// blocks at young addresses 0 and 2 (`PWFold.ynice`), from the minor
/// collection's contract (`minor_at`):
///   - `mpre_of`: its precondition holds;
///   - `step_minor`: the result is `Done` (`OutOfRoom` is never justified,
///     `PWFold.no_oor`); every live young block is promoted once, to a block
///     that was free, with the colour rule's colour and the young block's
///     field; every block in use keeps its header and, if the program may
///     use it, its fields; the roots are forwarded; the nursery is empty;
///     the collection costs two pages of the budget at most.
/// Where the copies are is the collection's answer (`mfwd`).

module GC.Spec.Top.PWMinor

open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.MinorHeap
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
module Y = GC.Spec.Top.Young
module PIn = GC.Spec.Top.PagesInst
module PWP = GC.Spec.Top.PWPages
module PWA = GC.Spec.Top.PWAlloc
module PWF = GC.Spec.Top.PWFold
module PWM = GC.Spec.Top.PWMut
module FM0 = GC.Spec.Top.FFWMinor0
module FWS = GC.Spec.Top.FFWStep

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The nurseries of the runs
/// ---------------------------------------------------------------------------

let nice_v (k: nat) (v: M.value) : prop = PWF.yval k v == true /\ storable_w v

#push-options "--fuel 2 --z3rlimit 40"
let ym0_ok (k: nat)
  : Lemma (M.young_ok (M.empty_heap ywords) /\ T.young_follow_ok (M.empty_heap ywords) /\
           PWF.ynice k (M.empty_heap ywords))
  = ()

let ym1_ok (k: nat) (v: M.value)
  : Lemma (requires 4 <= ywords /\ nice_v k v)
          (ensures M.young_ok (PWM.ym1 v) /\ T.young_follow_ok (PWM.ym1 v) /\ PWF.ynice k (PWM.ym1 v) /\
                   M.is_block (PWM.ym1 v) 0 /\ M.field (PWM.ym1 v) 0 0 == v)
  = ()

let ym2_ok (k: nat) (v w: M.value)
  : Lemma (requires 4 <= ywords /\ nice_v k v /\ nice_v k w)
          (ensures M.young_ok (PWM.ym2 v w) /\ T.young_follow_ok (PWM.ym2 v w) /\ PWF.ynice k (PWM.ym2 v w) /\
                   M.is_block (PWM.ym2 v w) 0 /\ M.field (PWM.ym2 v w) 0 0 == v /\
                   M.is_block (PWM.ym2 v w) 2 /\ M.field (PWM.ym2 v w) 2 0 == w)
  = ()
#pop-options

/// ---------------------------------------------------------------------------
/// The collection's answer
/// ---------------------------------------------------------------------------

let mres (x: config pc) : GTot (T.minor_result heap pk pa) = pc.n.T.collect x.ph (stx x) x.w

let mfwd (x: config pc) : GTot (nat -> option nat) =
  match mres x with T.Done _ _ _ f -> f | _ -> (fun _ -> None)

/// The copy of young block `o`.
let cpy (x: config pc) (d: dsc) (o: nat) : GTot bd =
  let c = match mfwd x o with Some c -> c | None -> 0 in
  { bw = 1; bt = 0; bc = T.colour_at pk x.ph c; blv = true; bf = [M.field d.dym o 0] }

let is_cp (x: config pc) (d: dsc) (o y: nat) : GTot bool = M.is_block d.dym o && mfwd x o = Some y

/// The description after the collection.
let dminor (x: config pc) (d: dsc) : GTot dsc =
  { d with db = (fun (y: nat) -> if is_cp x d 0 y then Some (cpy x d 0)
                                 else if is_cp x d 2 y then Some (cpy x d 2)
                                 else d.db y);
           dys = ms0; dym = M.empty_heap ywords; drt = L.map (T.fwdv d.dym (mfwd x)) d.drt; dj = d.dj + 2 }

/// ---------------------------------------------------------------------------
/// The precondition
/// ---------------------------------------------------------------------------

/// The closure `k`, described and live.
let kdesc (d: dsc) (k: nat) : prop =
  Some? (d.db k) /\ (Some?.v (d.db k)).blv /\ (Some?.v (d.db k)).bt == M.closure_tag /\
  (Some?.v (d.db k)).bw == 3 /\ vi (Some?.v (d.db k)).bf 1 == M.infix_word 2

/// No field the program may use holds a young pointer.
let no_yf (d: dsc) : prop =
  forall (y: nat). Some? (d.db y) /\ usable d (Some?.v (d.db y)) ==> FWS.no_young (Some?.v (d.db y)).bf == true

#push-options "--fuel 1"
let rec no_young_idx (l: list M.value) (i: nat)
  : Lemma (requires FWS.no_young l == true) (ensures not (M.VPtr? (vi l i) && M.Young? (M.VPtr?._0 (vi l i))))
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: tl -> if i = 0 then () else no_young_idx tl (i - 1)
#pop-options

/// The closure, live in the major heap.
let kok_of (x: config pc) (d: dsc) (k: nat)
  : Lemma (requires holds x d /\ kdesc d k) (ensures PWF.kok x.ph (stx x) x.w.cmaj k)
  = holds_elim x d;
    blk x d k

let mpre_parts (x: config pc) (d: dsc) (k: nat) : prop =
  holds x d /\ PWF.ynice k d.dym /\ M.young_ok d.dym /\ T.young_follow_ok d.dym /\ kdesc d k /\ no_yf d

let rem_ok (x: config pc) (d: dsc) (k: nat) (o i b: nat)
  : Lemma (requires mpre_parts x d k)
          (ensures ~(T.live_target pa x.ph (stx x) x.w.cmaj (mx x) o /\ M.ptr_field (mx x) o i /\
                     M.field (mx x) o i == M.VPtr (M.Young b)))
  = holds_elim x d;
    if iu x o then begin
      holds_iu x d o;
      holds_blk x d o;
      let bb = Some?.v (d.db o) in
      if usable d bb then begin
        blk x d o;
        if i < bb.bw then no_young_idx bb.bf i
      end
    end

let ysound_ok (x: config pc) (d: dsc) (k: nat) (y i b: nat)
  : Lemma (requires mpre_parts x d k /\ M.ptr_field d.dym y i /\ M.field d.dym y i == M.VPtr (M.Major b))
          (ensures T.sound_value pa x.ph (stx x) x.w.cmaj (mx x) (M.VPtr (M.Major b)))
  = assert (M.is_block d.dym y /\ i < M.wz_of d.dym y);
    assert (M.wz_of d.dym y == 1 /\ PWF.yval k (M.field d.dym y 0));
    let i0 : nat = i in
    assert (i0 < 1);
    assert (M.field d.dym y i == M.field d.dym y 0);
    kok_of x d k;
    PWF.sound_y x.ph (stx x) x.w.cmaj k (M.VPtr (M.Major b))

/// **The collection's precondition.**
let mpre_of (x: config pc) (d: dsc) (k: nat)
  : Lemma (requires mpre_parts x d k) (ensures T.minor_pre pa x.ph (stx x) x.w.cmaj (wd x d))
  = holds_elim x d;
    FStar.Classical.forall_intro_3 (fun o i b -> rem_ok x d k o i b);
    FStar.Classical.forall_intro_3 (fun y i b -> FStar.Classical.move_requires (ysound_ok x d k y i) b)

/// ---------------------------------------------------------------------------
/// The step
/// ---------------------------------------------------------------------------

let mstep_pre (x: config pc) (d: dsc) (k: nat) : prop =
  cok /\ mpre_parts x d k /\ d.dj + 2 <= n_pages /\
  (forall (o: nat). M.is_block d.dym o ==> storable_w (M.field d.dym o 0))

/// The result is `Done`, with the contract's model.
let mpost (x: config pc) (d: dsc) (hm: M.mheap) : prop =
  match mres x with
  | T.Done hc' st' rts fwd -> brepr hm hc' /\ T.minor_post_done pa x.ph (stx x) x.w.cmaj (wd x d) hc' st' rts fwd hm /\
                              PWP.kinds_ok (st' <: pst).ps (d.dj + 2)
  | _ -> False

#push-options "--z3rlimit 40"
let minor_done (x: config pc) (d: dsc) (k: nat)
  : Lemma (requires mstep_pre x d k) (ensures exists (hm: M.mheap). mpost x d hm)
  = holds_elim x d;
    mpre_of x d k;
    views_wd x d;
    kok_of x d k;
    cok_hyps x EMinor;
    assert (T.minor_m byte_rep pc.n x.ph (stx x) x.w (wd x d));
    PWF.no_oor x.ph (stx x) x.w (wd x d) k d.dj;
    PWF.minor_kinds x.ph (stx x) x.w (wd x d) k d.dj;
    match mres x with
    | T.OutOfRoom -> assert (T.oor_justified byte_rep pa x.ph (stx x) x.w (wd x d))
    | T.Done hc' st' rts fwd ->
      assert (exists (h': M.mheap). byte_rep.R.repr h' hc' /\
                T.minor_post_done pa x.ph (stx x) x.w.cmaj (wd x d) hc' st' rts fwd h');
      eliminate exists (h': M.mheap). byte_rep.R.repr h' hc' /\
                T.minor_post_done pa x.ph (stx x) x.w.cmaj (wd x d) hc' st' rts fwd h'
      with begin
        assert (brepr h' hc');
        assert (PWP.kinds_ok (st' <: pst).ps (d.dj + 2));
        assert (T.minor_post_done pa x.ph (stx x) x.w.cmaj (wd x d) hc' st' rts fwd h');
        assert (mpost x d h')
      end
#pop-options

/// `z` is a copy.
let cp_of (x: config pc) (z: nat) : prop = exists (o: nat). mfwd x o == Some z

/// The next configuration, on the models.
let maft (x: config pc) (d: dsc) (hm: M.mheap) : prop =
  let x' = step pc x EMinor in
  R.heq (mx x') hm /\ x'.w.crem == [] /\ x'.ph == x.ph /\ x'.stopped == x.stopped /\
  x'.w.cyng == ms0 /\ x'.w.croots == L.map (T.fwdv d.dym (mfwd x)) d.drt /\
  pa.T.inv x'.ph x'.w.cmaj (stx x') /\ PWP.kinds_ok (stx x').ps (d.dj + 2) /\ M.well_formed (mx x') /\
  (forall (z: nat). iu x' z == true <==> (iu x z == true \/ cp_of x z))

/// The configuration after a `Done` collection.
let x_minor (x: config pc)
  : Lemma (requires T.Done? (mres x))
          (ensures (let x' = step pc x EMinor in
                    x'.w.cmaj == T.Done?.maj (mres x) /\ stx x' == T.Done?.st (mres x) /\
                    x'.w.croots == T.Done?.roots (mres x) /\ x'.w.cyng == Y.yreset x.w.cyng /\
                    x'.w.crem == [] /\ x'.ph == x.ph /\ x'.stopped == x.stopped /\
                    mfwd x == T.Done?.fwd (mres x)))
  = ()

let mpost_parts (x: config pc) (d: dsc) (hm: M.mheap)
  : Lemma (requires mpost x d hm)
          (ensures T.Done? (mres x) /\
                   (let hc' = T.Done?.maj (mres x) in
                    let st' : pst = T.Done?.st (mres x) in
                    brepr hm hc' /\ PWP.kinds_ok st'.ps (d.dj + 2) /\ M.well_formed hm /\
                    pa.T.inv x.ph hc' st' /\
                    T.Done?.roots (mres x) == L.map (T.fwdv d.dym (mfwd x)) d.drt /\
                    (forall (z: nat). T.in_use pa st' hc' hm z <==> (iu x z \/ cp_of x z))))
  = ()

let mp_iu (x: config pc) (d: dsc) (hm: M.mheap) (z: nat)
  : Lemma (requires mpost x d hm)
          (ensures T.Done? (mres x) /\
                   (T.in_use pa (T.Done?.st (mres x)) (T.Done?.maj (mres x)) hm z <==>
                    (iu x z \/ cp_of x z)))
  = mpost_parts x d hm

let iu_m (x: config pc) (d: dsc) (hm: M.mheap) (z: nat)
  : Lemma (requires mpost x d hm)
          (ensures iu (step pc x EMinor) z == true <==> (iu x z == true \/ cp_of x z))
  = mp_iu x d hm z;
    mpost_parts x d hm;
    x_minor x;
    let hc' = T.Done?.maj (mres x) in
    let st' : pst = T.Done?.st (mres x) in
    let x' = step pc x EMinor in
    PWA.iu_any st' hc' hm z;
    PWA.iu_any st' hc' (mx x') z

let iu_all (x: config pc) (d: dsc) (hm: M.mheap)
  : Lemma (requires mpost x d hm)
          (ensures forall (z: nat). iu (step pc x EMinor) z == true <==> (iu x z == true \/ cp_of x z))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (iu_m x d hm))

let maft_intro (x: config pc) (d: dsc) (hm: M.mheap)
  : Lemma (requires (let x' = step pc x EMinor in
                     R.heq (mx x') hm /\ x'.w.crem == [] /\ x'.ph == x.ph /\ x'.stopped == x.stopped /\
                     x'.w.cyng == ms0 /\ x'.w.croots == L.map (T.fwdv d.dym (mfwd x)) d.drt /\
                     pa.T.inv x'.ph x'.w.cmaj (stx x') /\ PWP.kinds_ok (stx x').ps (d.dj + 2) /\ M.well_formed (mx x') /\
                     (forall (z: nat). iu x' z == true <==> (iu x z == true \/ cp_of x z))))
          (ensures maft x d hm)
  = ()

let after (x: config pc) (d: dsc) (k: nat) (hm: M.mheap)
  : Lemma (requires mstep_pre x d k /\ mpost x d hm) (ensures maft x d hm)
  = mpost_parts x d hm;
    x_minor x;
    let x' = step pc x EMinor in
    FM0.yreset_yinit x.w.cyng;
    R.heq_sym hm (mx x');
    PIn.wf_heq hm (mx x');
    iu_all x d hm;
    assert (FM0.ms0 == ms0);
    assert (R.heq (mx x') hm);
    assert (x'.w.cyng == ms0);
    assert (x'.w.croots == L.map (T.fwdv d.dym (mfwd x)) d.drt);
    assert (pa.T.inv x'.ph x'.w.cmaj (stx x'));
    assert (PWP.kinds_ok (stx x').ps (d.dj + 2));
    assert (M.well_formed (mx x'));
    maft_intro x d hm

/// The contract's facts, at one block.
let post_at (x: config pc) (d: dsc) (hm: M.mheap) (o c y: nat)
  : Lemma (requires mpost x d hm)
          (ensures (mfwd x o == Some c ==>
                      M.is_block d.dym o /\
                      hm.M.hd c == Some ({ M.wz = M.wz_of d.dym o; M.tag = M.tag_of d.dym o; M.col = T.colour_at pk x.ph c }) /\
                      (forall (i: nat). i < M.wz_of d.dym o ==> M.field hm c i == T.fwd_field d.dym o i d.dym (mfwd x))) /\
                   (Some? (mfwd x o) <==> (M.is_block d.dym o /\ M.minor_live (wd x d) o)) /\
                   (iu x y ==> hm.M.hd y == (mx x).M.hd y /\
                      (T.live_target pa x.ph (stx x) x.w.cmaj (mx x) y ==>
                         (forall (i: nat). i < M.wz_of (mx x) y ==> M.field hm y i == T.fwd_field (mx x) y i d.dym (mfwd x)))))
  = mpost_parts x d hm;
    let T.Done hc' st' rts fwd = mres x in
    assert (mfwd x == fwd);
    assert (T.minor_post_done pa x.ph (stx x) x.w.cmaj (wd x d) hc' st' rts fwd hm);
    assert ((wd x d).M.yng == d.dym /\ (wd x d).M.maj == mx x)

/// A field without young pointers is not forwarded.
let fwdv_old (y: M.mheap) (f: nat -> option nat) (v: M.value)
  : Lemma (requires not (M.VPtr? v && M.Young? (M.VPtr?._0 v))) (ensures T.fwdv y f v == v)
  = ()

let yval_ny (k: nat) (v: M.value)
  : Lemma (requires PWF.yval k v == true) (ensures not (M.VPtr? v && M.Young? (M.VPtr?._0 v)))
  = ()

let hcol_live (x: config pc) (b: bd) (y: nat)
  : Lemma (requires b.blv == true /\ b.bc == T.colour_at pk x.ph y) (ensures hcol x b y == T.colour_at pk x.ph y)
  = ()

#push-options "--fuel 2"
let vi1 (v: M.value) : Lemma (L.length [v] == 1 /\ vi [v] 0 == v) = ()
#pop-options

/// A copy, from facts about it alone.
let bk_cp (x': config pc) (d': dsc) (y: nat) (v: M.value) (col: M.colour)
  : Lemma (requires iu x' y == true /\ col == T.colour_at pk x'.ph y /\
                    (mx x').M.hd y == Some ({ M.wz = 1; M.tag = 0; M.col = col }) /\ M.field (mx x') y 0 == v)
          (ensures bk x' d' y ({ bw = 1; bt = 0; bc = col; blv = true; bf = [v] }))
  = let b = { bw = 1; bt = 0; bc = col; blv = true; bf = [v] } in
    hcol_live x' b y;
    vi1 v;
    let fl (i: nat) : Lemma (i < 1 ==> M.field (mx x') y i == vi b.bf i) = () in
    FStar.Classical.forall_intro fl

/// The facts about a copy.
#push-options "--z3rlimit 40"
let cp_facts (x: config pc) (d: dsc) (k: nat) (hm: M.mheap) (o y: nat)
  : Lemma (requires mstep_pre x d k /\ mpost x d hm /\ maft x d hm /\ is_cp x d o y)
          (ensures (let x' = step pc x EMinor in
                    iu x' y == true /\ x'.ph == x.ph /\
                    (mx x').M.hd y == Some ({ M.wz = 1; M.tag = 0; M.col = T.colour_at pk x.ph y }) /\
                    M.field (mx x') y 0 == M.field d.dym o 0))
  = let x' = step pc x EMinor in
    post_at x d hm o y y;
    assert (cp_of x y);
    assert (M.wz_of d.dym o == 1 /\ M.tag_of d.dym o == 0 /\ PWF.yval k (M.field d.dym o 0));
    yval_ny k (M.field d.dym o 0);
    fwdv_old d.dym (mfwd x) (M.field d.dym o 0);
    assert (M.field hm y 0 == M.field d.dym o 0)
#pop-options

let blk_cp (x: config pc) (d: dsc) (k: nat) (hm: M.mheap) (o y: nat)
  : Lemma (requires mstep_pre x d k /\ mpost x d hm /\ maft x d hm /\ is_cp x d o y)
          (ensures bk (step pc x EMinor) (dminor x d) y (cpy x d o))
  = cp_facts x d k hm o y;
    bk_cp (step pc x EMinor) (dminor x d) y (M.field d.dym o 0) (T.colour_at pk x.ph y)

let post_blk (x: config pc) (d: dsc) (hm: M.mheap) (o c: nat)
  : Lemma (requires mpost x d hm /\ mfwd x o == Some c) (ensures M.is_block d.dym o)
  = post_at x d hm o c 0

/// No copy but those of 0 and 2.
let cp_pick (x: config pc) (d: dsc) (k: nat) (y o: nat)
  : Lemma (requires PWF.ynice k d.dym /\ M.is_block d.dym o /\ mfwd x o == Some y)
          (ensures is_cp x d 0 y \/ is_cp x d 2 y)
  = if o = 0 then assert (is_cp x d 0 y) else assert (is_cp x d 2 y)

let cp_only (x: config pc) (d: dsc) (k: nat) (hm: M.mheap) (y: nat)
  : Lemma (requires PWF.ynice k d.dym /\ mpost x d hm /\ cp_of x y)
          (ensures is_cp x d 0 y \/ is_cp x d 2 y)
  = let o = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun (o: nat) -> mfwd x o == Some y) in
    post_blk x d hm o y;
    cp_pick x d k y o

/// A block the program may use is one the collection rewrites.
let usable_lt (x: config pc) (d: dsc) (y: nat)
  : Lemma (requires holds x d /\ Some? (d.db y) /\ usable d (Some?.v (d.db y)))
          (ensures T.live_target pa x.ph (stx x) x.w.cmaj (mx x) y)
  = holds_elim x d;
    blk x d y

/// Its fields, forwarded, are its fields: none is a young pointer.
let fwd_same (x: config pc) (d: dsc) (f: nat -> option nat) (y: nat)
  : Lemma (requires holds x d /\ no_yf d /\ Some? (d.db y) /\ usable d (Some?.v (d.db y)))
          (ensures forall (i: nat). i < (Some?.v (d.db y)).bw ==>
                     T.fwd_field (mx x) y i d.dym f == M.field (mx x) y i)
  = blk x d y;
    let b = Some?.v (d.db y) in
    let one (i: nat) : Lemma (i < b.bw ==> T.fwd_field (mx x) y i d.dym f == M.field (mx x) y i)
      = if i < b.bw then begin no_young_idx b.bf i; fwdv_old d.dym f (vi b.bf i) end in
    FStar.Classical.forall_intro one

/// The facts about an old block.
#push-options "--z3rlimit 40"
let old_facts (x: config pc) (d: dsc) (k: nat) (hm: M.mheap) (y: nat)
  : Lemma (requires mstep_pre x d k /\ mpost x d hm /\ maft x d hm /\
                    not (is_cp x d 0 y) /\ not (is_cp x d 2 y))
          (ensures (let x' = step pc x EMinor in
                    iu x' y == iu x y /\ x'.ph == x.ph /\
                    (iu x y ==> (mx x').M.hd y == (mx x).M.hd y) /\
                    (iu x y /\ T.live_target pa x.ph (stx x) x.w.cmaj (mx x) y ==>
                       (forall (i: nat). i < M.wz_of (mx x) y ==> M.field (mx x') y i == T.fwd_field (mx x) y i d.dym (mfwd x)))))
  = FStar.Classical.move_requires (cp_only x d k hm) y;
    post_at x d hm 0 0 y
#pop-options

/// An old block, from facts about it alone.
let bk_old (x x': config pc) (d d': dsc) (y: nat) (b: bd)
  : Lemma (requires bk x d y b /\ d'.dk == d.dk /\ x'.ph == x.ph /\ iu x' y == iu x y /\
                    (iu x y ==> (mx x').M.hd y == (mx x).M.hd y) /\
                    (iu x y /\ usable d b ==> (forall (i: nat). i < b.bw ==> M.field (mx x') y i == M.field (mx x) y i)))
          (ensures bk x' d' y b)
  = assert (hcol x' b y == hcol x b y);
    assert (unsw x' y == unsw x y)

/// An old block, described as before.
let blk_old (x: config pc) (d: dsc) (k: nat) (hm: M.mheap) (y: nat)
  : Lemma (requires mstep_pre x d k /\ mpost x d hm /\ maft x d hm /\ Some? (d.db y) /\
                    not (is_cp x d 0 y) /\ not (is_cp x d 2 y))
          (ensures bk (step pc x EMinor) (dminor x d) y (Some?.v (d.db y)))
  = let x' = step pc x EMinor in
    let b = Some?.v (d.db y) in
    holds_blk x d y;
    old_facts x d k hm y;
    if iu x y && usable d b then begin
      usable_lt x d y;
      fwd_same x d (mfwd x) y;
      blk x d y
    end;
    bk_old x x' d (dminor x d) y b

let blk_all (x: config pc) (d: dsc) (k: nat) (hm: M.mheap) (y: nat)
  : Lemma (requires mstep_pre x d k /\ mpost x d hm /\ maft x d hm)
          (ensures Some? ((dminor x d).db y) ==> bk (step pc x EMinor) (dminor x d) y (Some?.v ((dminor x d).db y)))
  = if is_cp x d 0 y then blk_cp x d k hm 0 y
    else if is_cp x d 2 y then blk_cp x d k hm 2 y
    else if Some? (d.db y) then blk_old x d k hm y

let db_minor (x: config pc) (d: dsc) (y: nat)
  : Lemma ((dminor x d).db y == (if is_cp x d 0 y then Some (cpy x d 0)
                                 else if is_cp x d 2 y then Some (cpy x d 2) else d.db y))
  = ()

let maft_iu (x: config pc) (d: dsc) (hm: M.mheap) (y: nat)
  : Lemma (requires maft x d hm /\ iu (step pc x EMinor) y == true) (ensures iu x y == true \/ cp_of x y)
  = ()

let cp_all (x: config pc) (d: dsc) (k: nat) (hm: M.mheap)
  : Lemma (requires PWF.ynice k d.dym /\ mpost x d hm)
          (ensures forall (y: nat). cp_of x y ==> is_cp x d 0 y \/ is_cp x d 2 y)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (cp_only x d k hm))

let des_all (x: config pc) (d: dsc) (hm: M.mheap) (y: nat)
  : Lemma (requires holds x d /\ maft x d hm /\ (forall (y: nat). cp_of x y ==> is_cp x d 0 y \/ is_cp x d 2 y))
          (ensures iu (step pc x EMinor) y == true ==> Some? ((dminor x d).db y))
  = db_minor x d y;
    if iu (step pc x EMinor) y then begin
      maft_iu x d hm y;
      if iu x y then holds_iu x d y
    end

let minor_intro (x: config pc) (d: dsc) (hm: M.mheap)
  : Lemma (requires holds x d /\ maft x d hm /\
                    (forall (y: nat). Some? ((dminor x d).db y) ==>
                       bk (step pc x EMinor) (dminor x d) y (Some?.v ((dminor x d).db y))) /\
                    (forall (y: nat). iu (step pc x EMinor) y == true ==> Some? ((dminor x d).db y)))
          (ensures holds (step pc x EMinor) (dminor x d))
  = holds_elim x d;
    Y.yinit_ok' ywords;
    yinit_ms0 ywords;
    holds_intro (step pc x EMinor) (dminor x d)

/// **EMinor**: `Done`, every live young block promoted.
let step_minor (x: config pc) (d: dsc) (k: nat)
  : Lemma (requires mstep_pre x d k)
          (ensures T.Done? (mres x) /\ holds (step pc x EMinor) (dminor x d) /\
                   (forall (o: nat). M.is_block d.dym o /\ M.minor_live (wd x d) o ==> Some? (mfwd x o)))
  = minor_done x d k;
    eliminate exists (hm: M.mheap). mpost x d hm
    with begin
      after x d k hm;
      FStar.Classical.forall_intro (blk_all x d k hm);
      holds_elim x d;
      cp_all x d k hm;
      FStar.Classical.forall_intro (des_all x d hm);
      minor_intro x d hm;
      let lv (o: nat) : Lemma (M.is_block d.dym o /\ M.minor_live (wd x d) o ==> Some? (mfwd x o))
        = post_at x d hm o 0 0 in
      FStar.Classical.forall_intro lv
    end

/// A young root is live for the collection.
let live_root (w: M.world) (a o: nat)
  : Lemma (requires L.memP (M.VPtr (M.Young a)) w.M.roots /\ M.resolve w.M.yng a == Some o)
          (ensures M.minor_live w o)
  = let l : M.mlive w o = M.LRoot o a () in
    assert (M.minor_live w o)
