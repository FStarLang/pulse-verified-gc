/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWIncA - the pages incremental witness run's descriptions
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  The incremental run (GC.Spec.Top.PWInc) adds blocks to
/// those of `PWPre.dd`: D, allocated while marking, and the copies the minor
/// collections make.  `dx` describes A (its first field `a0`, written while
/// marking), B, K, C (garbage) and extra blocks `ex`, none of them grey.
/// On it:
///   - `grey_dx`: a grey block is one of A, B, K described grey;
///   - `slice_dx`: a slice, while A's first field is an integer (A has no
///     edge, B's is to K);
///   - `hand_dx`: the hand-over, when every block is black or white and the
///     extra blocks hold integers and pointers to B or K only;
///   - `end_dx`: the end.

module GC.Spec.Top.PWIncA

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.Run
open GC.Spec.Top.PWDesc
open GC.Spec.Top.PWRun
open GC.Spec.Top.PWPre
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module TM = GC.Spec.Top.ToyMark
module RA = GC.Spec.Top.RunApp
module PWK = GC.Spec.Top.PWMark
module PWM = GC.Spec.Top.PWMinor
module PWS = GC.Spec.Top.PWSweep
module PWC = GC.Spec.Top.PWCyc

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

type exb = nat -> GTot (option bd)

let dx (dk: phk) (cA cB cK: M.colour) (hasC: bool) (a0: M.value) (ex: exb) (rs: list M.value) (j: nat)
       (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap) : GTot dsc =
  { dk = dk; dys = ys; dym = ym; drt = rs; dj = j;
    db = (fun (y: nat) ->
      if y = xK () then Some ({ bK with bc = cK })
      else if y = xC () then (if hasC then Some ({ blkC (vB ()) with blv = false }) else None)
      else if y = xB () then Some ({ blkB (vK2 ()) with bc = cB })
      else if y = xA () then Some ({ blkA a0 with bc = cA })
      else ex y) }

let bofx (cA cB cK: M.colour) (a0: M.value) (o: nat) : GTot bd =
  if o = xK () then { bK with bc = cK }
  else if o = xB () then { blkB (vK2 ()) with bc = cB }
  else { blkA a0 with bc = cA }

let db_dx (dk: phk) (cA cB cK: M.colour) (hasC: bool) (a0: M.value) (ex: exb) (rs: list M.value) (j: nat)
          (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap) (o: nat)
  : Lemma (requires pw_room /\ cok /\ (o == xA () \/ o == xB () \/ o == xK ()))
          (ensures (dx dk cA cB cK hasC a0 ex rs j ys ym).db o == Some (bofx cA cB cK a0 o))
  = distinct ()

let db_ex (dk: phk) (cA cB cK: M.colour) (hasC: bool) (a0: M.value) (ex: exb) (rs: list M.value) (j: nat)
          (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap) (o: nat)
  : Lemma (requires o <> xA () /\ o <> xB () /\ o <> xC () /\ o <> xK ())
          (ensures (dx dk cA cB cK hasC a0 ex rs j ys ym).db o == ex o)
  = ()

/// The extra blocks: none grey, each a one-field block of tag 0.
let ex_ok (ex: exb) : prop =
  forall (y: nat). Some? (ex y) ==> (Some?.v (ex y)).bc =!= M.Grey /\ (Some?.v (ex y)).blv == true /\
                                   (Some?.v (ex y)).bw == 1 /\ (Some?.v (ex y)).bt == 0

/// ---------------------------------------------------------------------------
/// Marking
/// ---------------------------------------------------------------------------

/// A grey block in use is one of A, B, K, described grey.
let grey_dx (x: config pc) (dk: phk) (cA cB cK: M.colour) (hasC: bool) (a0: M.value) (ex: exb) (rs: list M.value)
            (j: nat) (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap) (t: nat)
  : Lemma (requires pw_room /\ cok /\ holds x (dx dk cA cB cK hasC a0 ex rs j ys ym) /\ dk == DM /\ ex_ok ex /\
                    M.is_block (mx x) t /\ M.col_of (mx x) t == M.Grey)
          (ensures (t == xA () /\ cA == M.Grey) \/ (t == xB () /\ cB == M.Grey) \/ (t == xK () /\ cK == M.Grey))
  = let d = dx dk cA cB cK hasC a0 ex rs j ys ym in
    distinct ();
    holds_elim x d;
    iu_def x t;
    holds_iu x d t;
    holds_blk x d t

/// The pointer fields of A (its first field an integer), B and K.
let fields_dx (x: config pc) (cA cB cK: M.colour) (n: int) (o i a o': nat)
  : Lemma (requires pw_room /\ cok /\ (o == xA () \/ o == xB () \/ o == xK ()) /\
                    i < (bofx cA cB cK (M.VInt n) o).bw /\ vi (bofx cA cB cK (M.VInt n) o).bf i == M.VPtr (M.Major a) /\
                    M.resolve (mx x) a == Some o' /\
                    M.is_block (mx x) (xK ()) /\ M.well_formed (mx x) /\
                    M.tag_of (mx x) (xK ()) == M.closure_tag /\ M.wz_of (mx x) (xK ()) == 3 /\
                    M.field (mx x) (xK ()) 1 == iw)
          (ensures o == xB () /\ o' == xK ())
  = distinct ();
    st_vals ();
    l2 (M.VInt n) i1; l1 (vK2 ()); l3 i1 iw i1;
    if o = xA () then begin
      assert ((bofx cA cB cK (M.VInt n) o).bf == [M.VInt n; i1]);
      assert (i < 2)
    end
    else if o = xB () then begin
      assert ((bofx cA cB cK (M.VInt n) o).bf == [vK2 ()]);
      res_infix (mx x) (xK ())
    end
    else begin
      assert ((bofx cA cB cK (M.VInt n) o).bf == [i1; iw; i1]);
      assert (i < 3)
    end

/// A pointer field of A, B or K is B's, the infix pointer into K.
let ptr_dx (cA cB cK: M.colour) (n: int) (o i a: nat)
  : Lemma (requires pw_room /\ cok /\ (o == xA () \/ o == xB () \/ o == xK ()) /\
                    i < (bofx cA cB cK (M.VInt n) o).bw /\ vi (bofx cA cB cK (M.VInt n) o).bf i == M.VPtr (M.Major a))
          (ensures o == xB () /\ a == xK () + 2)
  = distinct ();
    st_vals ();
    l2 (M.VInt n) i1; l1 (vK2 ()); l3 i1 iw i1;
    if o = xA () then assert ((bofx cA cB cK (M.VInt n) o).bf == [M.VInt n; i1])
    else if o = xB () then assert ((bofx cA cB cK (M.VInt n) o).bf == [vK2 ()])
    else assert ((bofx cA cB cK (M.VInt n) o).bf == [i1; iw; i1])

/// The edges of A (its first field an integer), B and K.
let edges_dx (x: config pc) (dk: phk) (cA cB cK: M.colour) (hasC: bool) (n: int) (ex: exb) (rs: list M.value)
             (j: nat) (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap) (o y: nat)
  : Lemma (requires pw_room /\ cok /\ holds x (dx dk cA cB cK hasC (M.VInt n) ex rs j ys ym) /\
                    (o == xA () \/ o == xB () \/ o == xK ()))
          (ensures (M.major_edge (mx x) o y <==> (o == xB () /\ y == xK ())) /\
                   (forall (i a: nat). M.ptr_field (mx x) o i /\ M.field (mx x) o i == M.VPtr (M.Major a) ==>
                      Some? (M.resolve (mx x) a)))
  = let d = dx dk cA cB cK hasC (M.VInt n) ex rs j ys ym in
    distinct ();
    holds_elim x d;
    db_dx dk cA cB cK hasC (M.VInt n) ex rs j ys ym o;
    db_dx dk cA cB cK hasC (M.VInt n) ex rs j ys ym (xK ());
    blk x d o;
    blk x d (xK ());
    st_vals ();
    l2 (M.VInt n) i1; l1 (vK2 ()); l3 i1 iw i1;
    res_infix (mx x) (xK ());
    let fwd () : Lemma (requires M.major_edge (mx x) o y) (ensures o == xB () /\ y == xK ())
      = eliminate exists (i a: nat). M.ptr_field (mx x) o i /\ M.field (mx x) o i == M.VPtr (M.Major a) /\
                                     M.resolve (mx x) a == Some y
        with fields_dx x cA cB cK n o i a y in
    FStar.Classical.move_requires fwd ();
    if o = xB () && y = xK () then
      assert (M.ptr_field (mx x) o 0 /\ M.field (mx x) o 0 == M.VPtr (M.Major (xK () + 2)));
    let rs_ (i a: nat) : Lemma (M.ptr_field (mx x) o i /\ M.field (mx x) o i == M.VPtr (M.Major a) ==>
                                Some? (M.resolve (mx x) a))
      = if M.ptr_field (mx x) o i && M.field (mx x) o i = M.VPtr (M.Major a) then
          ptr_dx cA cB cK n o i a in
    FStar.Classical.forall_intro_2 rs_

let ngA (t: nat) (cA: M.colour) : GTot M.colour = if t = xA () then M.Black else cA
let ngB (t: nat) (cB: M.colour) : GTot M.colour = if t = xB () then M.Black else cB
let ngK (t: nat) (cK: M.colour) : GTot M.colour =
  if t = xK () then M.Black else if t = xB () && cK = M.White then M.Grey else cK

let anygrey (cA cB cK: M.colour) : bool = cA = M.Grey || cB = M.Grey || cK = M.Grey

let slpre_dx (x: config pc) (cA cB cK: M.colour) (hasC: bool) (n: int) (ex: exb) (rs: list M.value) (j: nat)
             (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap)
  : Lemma (requires pw_room /\ cok /\ holds x (dx DM cA cB cK hasC (M.VInt n) ex rs j ys ym) /\ ex_ok ex /\
                    anygrey cA cB cK)
          (ensures PWK.slpre x (dx DM cA cB cK hasC (M.VInt n) ex rs j ys ym))
  = let d = dx DM cA cB cK hasC (M.VInt n) ex rs j ys ym in
    distinct ();
    holds_elim x d;
    db_dx DM cA cB cK hasC (M.VInt n) ex rs j ys ym (xA ());
    db_dx DM cA cB cK hasC (M.VInt n) ex rs j ys ym (xB ());
    db_dx DM cA cB cK hasC (M.VInt n) ex rs j ys ym (xK ());
    blk x d (xA ()); blk x d (xB ()); blk x d (xK ());
    let ng () : Lemma (~(T.no_grey (mx x)))
      = if cA = M.Grey then assert (M.col_of (mx x) (xA ()) == M.Grey)
        else if cB = M.Grey then assert (M.col_of (mx x) (xB ()) == M.Grey)
        else assert (M.col_of (mx x) (xK ()) == M.Grey) in
    ng ();
    let gt (t: nat) : Lemma (M.is_block (mx x) t /\ M.col_of (mx x) t == M.Grey ==>
                             (forall (i a: nat). M.ptr_field (mx x) t i /\ M.field (mx x) t i == M.VPtr (M.Major a) ==>
                                Some? (M.resolve (mx x) a)) /\
                             (forall (y: nat). M.major_edge (mx x) t y ==> iu x y == true))
      = if M.is_block (mx x) t && M.col_of (mx x) t = M.Grey then begin
          grey_dx x DM cA cB cK hasC (M.VInt n) ex rs j ys ym t;
          FStar.Classical.forall_intro (edges_dx x DM cA cB cK hasC n ex rs j ys ym t)
        end in
    FStar.Classical.forall_intro gt

/// **ESlice**, A's first field an integer.
#push-options "--z3rlimit 40"
let slice_dx (sty: style) (x: config pc) (cA cB cK: M.colour) (hasC: bool) (n: int) (ex: exb) (rs: list M.value)
             (j: nat) (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap)
  : Lemma (requires pw_room /\ cok /\ holds x (dx DM cA cB cK hasC (M.VInt n) ex rs j ys ym) /\ ex_ok ex /\
                    anygrey cA cB cK)
          (ensures (let t = PWK.fg x in
                    ((t == xA () /\ cA == M.Grey) \/ (t == xB () /\ cB == M.Grey) \/ (t == xK () /\ cK == M.Grey)) /\
                    holds (step pc x (PWK.esl x)) (dx DM (ngA t cA) (ngB t cB) (ngK t cK) hasC (M.VInt n) ex rs j ys ym) /\
                    RA.conds pc sty x (PWK.esl x) /\ GC.Spec.Top.Transp.alloc_succeeds x (PWK.esl x)))
  = let d = dx DM cA cB cK hasC (M.VInt n) ex rs j ys ym in
    slpre_dx x cA cB cK hasC n ex rs j ys ym;
    PWK.step_slice x d;
    let t = PWK.fg x in
    PWK.grey_found x d;
    grey_dx x DM cA cB cK hasC (M.VInt n) ex rs j ys ym t;
    distinct ();
    let d' = dx DM (ngA t cA) (ngB t cB) (ngK t cK) hasC (M.VInt n) ex rs j ys ym in
    let pt (y: nat) : Lemma (d'.db y == (PWK.dslice x d).db y)
      = TM.edge_b_iff (mx x) t y;
        edges_dx x DM cA cB cK hasC n ex rs j ys ym t y in
    FStar.Classical.forall_intro pt;
    holds_ext (step pc x (PWK.esl x)) (PWK.dslice x d) d';
    enabled_slice x d;
    conds_of sty x d (PWK.esl x)
#pop-options

/// ---------------------------------------------------------------------------
/// The hand-over
/// ---------------------------------------------------------------------------

/// The extra blocks' fields: integers, or pointers to B or into K.
let ex_ptr (ex: exb) : prop =
  forall (y i a: nat). Some? (ex y) /\ i < (Some?.v (ex y)).bw /\ vi (Some?.v (ex y)).bf i == M.VPtr (M.Major a) ==>
    a == xB () \/ a == xK () + 2

let ex_black (ex: exb) : prop = forall (y: nat). Some? (ex y) ==> (Some?.v (ex y)).bc == M.Black

/// A dark block in use, described.
let dark_dx (x: config pc) (cA cB cK: M.colour) (hasC: bool) (a0: M.value) (ex: exb) (rs: list M.value) (j: nat)
            (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap) (o: nat)
  : Lemma (requires pw_room /\ cok /\ holds x (dx DM cA cB cK hasC a0 ex rs j ys ym) /\
                    M.is_block (mx x) o /\ M.dark (M.col_of (mx x) o))
          (ensures Some? ((dx DM cA cB cK hasC a0 ex rs j ys ym).db o) /\
                   usable (dx DM cA cB cK hasC a0 ex rs j ys ym) (Some?.v ((dx DM cA cB cK hasC a0 ex rs j ys ym).db o)))
  = let d = dx DM cA cB cK hasC a0 ex rs j ys ym in
    holds_elim x d;
    iu_def x o;
    holds_iu x d o

/// Every dark block's pointer fields lead to B or K, both black.
#push-options "--z3rlimit 40"
let closed_dx (x: config pc) (n: int) (ex: exb) (rs: list M.value) (j: nat)
              (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap) (o i a y: nat)
  : Lemma (requires pw_room /\ cok /\ holds x (dx DM M.Black M.Black M.Black true (M.VInt n) ex rs j ys ym) /\
                    ex_ptr ex /\
                    M.is_block (mx x) o /\ M.dark (M.col_of (mx x) o) /\ M.ptr_field (mx x) o i /\
                    M.field (mx x) o i == M.VPtr (M.Major a) /\ M.resolve (mx x) a == Some y)
          (ensures M.col_of (mx x) y =!= M.White)
  = let d = dx DM M.Black M.Black M.Black true (M.VInt n) ex rs j ys ym in
    distinct ();
    holds_elim x d;
    dark_dx x M.Black M.Black M.Black true (M.VInt n) ex rs j ys ym o;
    blk x d o;
    db_dx DM M.Black M.Black M.Black true (M.VInt n) ex rs j ys ym (xB ());
    db_dx DM M.Black M.Black M.Black true (M.VInt n) ex rs j ys ym (xK ());
    blk x d (xB ()); blk x d (xK ());
    st_vals (); l3 i1 iw i1;
    res_infix (mx x) (xK ());
    if o = xA () || o = xB () || o = xK () then begin
      db_dx DM M.Black M.Black M.Black true (M.VInt n) ex rs j ys ym o;
      ptr_dx M.Black M.Black M.Black n o i a
    end
    else if o = xC () then ()
    else db_ex DM M.Black M.Black M.Black true (M.VInt n) ex rs j ys ym o
#pop-options

#push-options "--z3rlimit 40"
let hand_dx (sty: style) (x: config pc) (n: int) (ex: exb) (rs: list M.value) (j: nat)
            (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap)
  : Lemma (requires pw_room /\ cok /\ holds x (dx DM M.Black M.Black M.Black true (M.VInt n) ex rs j ys ym) /\
                    ex_ok ex /\ ex_ptr ex /\ ex_black ex)
          (ensures holds (step pc x EHandover) (dx DS M.Black M.Black M.Black true (M.VInt n) ex rs j ys ym) /\
                   RA.conds pc sty x EHandover /\ GC.Spec.Top.Transp.alloc_succeeds x EHandover /\
                   (forall (y: nat). iu x y == true ==> unsw (step pc x EHandover) y == true) /\
                   (forall (y: nat). iu (step pc x EHandover) y == iu x y))
  = let d = dx DM M.Black M.Black M.Black true (M.VInt n) ex rs j ys ym in
    distinct ();
    holds_elim x d;
    let ng (o: nat) : Lemma (M.is_block (mx x) o ==> M.col_of (mx x) o <> M.Grey)
      = if M.is_block (mx x) o && M.col_of (mx x) o = M.Grey then
          grey_dx x DM M.Black M.Black M.Black true (M.VInt n) ex rs j ys ym o in
    FStar.Classical.forall_intro ng;
    let dc (o i a y: nat) : Lemma (M.is_block (mx x) o /\ M.dark (M.col_of (mx x) o) /\ M.ptr_field (mx x) o i /\
                                   M.field (mx x) o i == M.VPtr (M.Major a) /\ M.resolve (mx x) a == Some y ==>
                                   M.col_of (mx x) y =!= M.White)
      = if FStar.IndefiniteDescription.strong_excluded_middle
             (M.is_block (mx x) o /\ M.dark (M.col_of (mx x) o) /\ M.ptr_field (mx x) o i /\
              M.field (mx x) o i == M.VPtr (M.Major a) /\ M.resolve (mx x) a == Some y)
        then closed_dx x n ex rs j ys ym o i a y in
    FStar.Classical.forall_intro_4 dc;
    let lab (y: nat) : Lemma (Some? (d.db y) ==>
                              ((Some?.v (d.db y)).blv ==> (Some?.v (d.db y)).bc == M.Black) /\
                              (not (Some?.v (d.db y)).blv ==> (Some?.v (d.db y)).bc == M.White))
      = () in
    FStar.Classical.forall_intro lab;
    assert (PWS.hpre x d);
    PWS.hand_model x d;
    PWS.step_hand x d;
    holds_ext (step pc x EHandover) (PWS.dhand d) (dx DS M.Black M.Black M.Black true (M.VInt n) ex rs j ys ym);
    enabled_hand x d;
    conds_of sty x d EHandover
#pop-options

/// ---------------------------------------------------------------------------
/// The end
/// ---------------------------------------------------------------------------

let exw (ex: exb) : exb = fun (y: nat) -> match ex y with Some b -> Some ({ b with bc = M.White }) | None -> None

let end_dx (sty: style) (x: config pc) (a0: M.value) (ex: exb) (rs: list M.value) (j: nat)
           (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap)
  : Lemma (requires pw_room /\ cok /\ ex_ok ex /\
                    holds x (dx DS M.Black M.Black M.Black true a0 ex rs j ys ym) /\ PWS.nsx x == 0)
          (ensures holds (step pc x EEnd) (dx DI M.White M.White M.White false a0 (exw ex) rs j ys ym) /\
                   RA.conds pc sty x EEnd /\ GC.Spec.Top.Transp.alloc_succeeds x EEnd)
  = let d = dx DS M.Black M.Black M.Black true a0 ex rs j ys ym in
    PWS.step_end x d;
    distinct ();
    let pt (y: nat) : Lemma ((dx DI M.White M.White M.White false a0 (exw ex) rs j ys ym).db y == (PWS.dend d).db y) = () in
    FStar.Classical.forall_intro pt;
    holds_ext (step pc x EEnd) (PWS.dend d) (dx DI M.White M.White M.White false a0 (exw ex) rs j ys ym);
    match sty with Sequential -> () | Incremental -> ()

/// ---------------------------------------------------------------------------
/// A minor collection
/// ---------------------------------------------------------------------------

module PWA = GC.Spec.Top.PWAlloc
module PIn = GC.Spec.Top.PagesInst

#push-options "--z3rlimit 40"
let post_free (ph: T.phase pprog) (st: pst) (hc: heap) (w: M.world) (hc': heap) (st': pst) (rts: list M.value)
              (fwd: nat -> option nat) (h': M.mheap) (o c w': nat)
  : Lemma (requires T.minor_post_done pa ph st hc w hc' st' rts fwd h' /\ fwd o == Some c /\ M.covers h' c w')
          (ensures T.free_word pa st hc w.M.maj w')
  = assert (h'.M.hd c == Some ({ M.wz = M.wz_of w.M.yng o; M.tag = M.tag_of w.M.yng o; M.col = T.colour_at pk ph c }));
    assert (forall (w': nat). M.covers h' c w' ==> T.free_word pa st hc w.M.maj w')
#pop-options

/// A copy is a block that was free.
#push-options "--z3rlimit 40"
let cp_fresh (x: config pc) (d: dsc) (k o y: nat)
  : Lemma (requires PWM.mstep_pre x d k /\ PWM.mfwd x o == Some y) (ensures iu x y == false)
  = PWM.minor_done x d k;
    holds_elim x d;
    eliminate exists (hm: M.mheap). PWM.mpost x d hm
    with begin
      let T.Done hc' st' rts fwd = PWM.mres x in
      assert (T.minor_post_done pa x.ph (stx x) x.w.cmaj (wd x d) hc' st' rts fwd hm);
      assert (fwd o == Some y);
      assert ((wd x d).M.maj == mx x);
      let fw (w': nat) : Lemma (M.covers hm y w' ==> T.free_word pa (stx x) x.w.cmaj (mx x) w')
        = if M.covers hm y w' then post_free x.ph (stx x) x.w.cmaj (wd x d) hc' st' rts fwd hm o y w' in
      FStar.Classical.forall_intro fw;
      assert (T.in_use pa st' hc' hm y);
      PWA.was_free (stx x) x.w.cmaj (mx x) hm y
    end
#pop-options

/// The extra blocks after the collection: the copies, then the others.
let exm (x: config pc) (d: dsc) (ex: exb) : exb =
  fun (y: nat) -> if PWM.is_cp x d 0 y then Some (PWM.cpy x d 0)
                  else if PWM.is_cp x d 2 y then Some (PWM.cpy x d 2)
                  else ex y

let mdx_pre (x: config pc) (dk: phk) (cA cB cK: M.colour) (hasC: bool) (a0: M.value) (ex: exb) (rs: list M.value)
            (j: nat) (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap) : prop =
  pw_room /\ cok /\ PWM.mstep_pre x (dx dk cA cB cK hasC a0 ex rs j ys ym) (xK ()) /\
  (iu x (xC ()) == true \/ (forall (o: nat). ~(M.is_block ym o)))

/// The description after the collection, pointwise.
let pt_minor (x: config pc) (dk: phk) (cA cB cK: M.colour) (hasC: bool) (a0: M.value) (ex: exb)
             (rs: list M.value) (j: nat) (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap) (y: nat)
  : Lemma (requires pw_room /\ cok /\
                    (let d = dx dk cA cB cK hasC a0 ex rs j ys ym in
                     (forall (o z: nat). PWM.is_cp x d o z ==> iu x z == false) /\
                     iu x (xA ()) == true /\ iu x (xB ()) == true /\ iu x (xK ()) == true /\
                     (iu x (xC ()) == true \/ (forall (o: nat). ~(M.is_block ym o)))))
          (ensures (let d = dx dk cA cB cK hasC a0 ex rs j ys ym in
                    (dx dk cA cB cK hasC a0 (exm x d ex) (L.map (T.fwdv ym (PWM.mfwd x)) rs) (j + 2)
                        ms0 (M.empty_heap ywords)).db y == (PWM.dminor x d).db y))
  = let d = dx dk cA cB cK hasC a0 ex rs j ys ym in
    distinct ();
    PWM.db_minor x d y

#push-options "--z3rlimit 40"
let minor_dx (sty: style) (x: config pc) (dk: phk) (cA cB cK: M.colour) (hasC: bool) (a0: M.value) (ex: exb)
             (rs: list M.value) (j: nat) (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap)
  : Lemma (requires mdx_pre x dk cA cB cK hasC a0 ex rs j ys ym)
          (ensures (let d = dx dk cA cB cK hasC a0 ex rs j ys ym in
                    holds (step pc x EMinor)
                          (dx dk cA cB cK hasC a0 (exm x d ex) (L.map (T.fwdv ym (PWM.mfwd x)) rs) (j + 2)
                              ms0 (M.empty_heap ywords)) /\
                    T.Done? (PWM.mres x) /\
                    (forall (o: nat). M.is_block ym o /\ M.minor_live (wd x d) o ==> Some? (PWM.mfwd x o)) /\
                    RA.conds pc sty x EMinor /\ GC.Spec.Top.Transp.alloc_succeeds x EMinor))
  = let d = dx dk cA cB cK hasC a0 ex rs j ys ym in
    PWM.step_minor x d (xK ());
    holds_elim x d;
    distinct ();
    db_dx dk cA cB cK hasC a0 ex rs j ys ym (xA ());
    db_dx dk cA cB cK hasC a0 ex rs j ys ym (xB ());
    db_dx dk cA cB cK hasC a0 ex rs j ys ym (xK ());
    blk x d (xA ()); blk x d (xB ()); blk x d (xK ());
    let d' = dx dk cA cB cK hasC a0 (exm x d ex) (L.map (T.fwdv ym (PWM.mfwd x)) rs) (j + 2) ms0 (M.empty_heap ywords) in
    let cf (o z: nat) : Lemma (PWM.is_cp x d o z ==> iu x z == false)
      = if PWM.is_cp x d o z then cp_fresh x d (xK ()) o z in
    FStar.Classical.forall_intro_2 cf;
    FStar.Classical.forall_intro (pt_minor x dk cA cB cK hasC a0 ex rs j ys ym);
    holds_ext (step pc x EMinor) (PWM.dminor x d) d';
    enabled_plain x d EMinor;
    conds_of sty x d EMinor
#pop-options

/// No field holds a young pointer; K is the closure.
let ex_ny (ex: exb) : prop =
  forall (y: nat). Some? (ex y) ==> GC.Spec.Top.FFWStep.no_young (Some?.v (ex y)).bf == true

let blocks_dx (dk: phk) (cA cB cK: M.colour) (hasC: bool) (a0: M.value) (ex: exb) (rs: list M.value) (j: nat)
              (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap)
  : Lemma (requires pw_room /\ cok /\ ex_ny ex /\ not (M.VPtr? a0 && M.Young? (M.VPtr?._0 a0)))
          (ensures PWM.no_yf (dx dk cA cB cK hasC a0 ex rs j ys ym) /\ PWM.kdesc (dx dk cA cB cK hasC a0 ex rs j ys ym) (xK ()))
  = distinct ();
    st_vals ();
    l2 a0 i1; l1 (vK2 ()); l3 i1 iw i1; l1 (vB ())
