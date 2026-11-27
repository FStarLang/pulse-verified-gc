/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWCyc - the pages witness runs' cycle, shared facts
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  On the configurations the runs describe by `PWPre.dd`
/// (A, B, K live, C garbage):
///   - `outside_dd`: with an empty nursery, the outside references are the
///     roots' targets;
///   - `edges_dd`: A's only edge is to B, B's only edge is to K (through
///     the infix pointer), K has none;
///   - `grey_is`: the block a slice scans is the one described grey;
///   - `start7`: at 7, A is a root, A, B and K are reachable, C is in use
///     and unreachable, and the mark may start.

module GC.Spec.Top.PWCyc

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
module PWK = GC.Spec.Top.PWMark
module PWM = GC.Spec.Top.PWMinor
module RA = GC.Spec.Top.RunApp

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let ddv (dk: phk) (cA cB cK: M.colour) (hasC: bool) (rs: list M.value) (j: nat) : GTot dsc =
  dd dk cA cB cK hasC rs j ms0 (M.empty_heap ywords)

/// With an empty nursery, an outside reference is a root's target.
let outside_empty (w: M.world) (o: nat)
  : Lemma (requires w.M.yng == M.empty_heap ywords)
          (ensures M.outside_ref w o <==> M.root_ref w o)
  = ()

/// The edges of the live blocks.
let edges_dd (x: config pc) (dk: phk) (cA cB cK: M.colour) (hasC: bool) (rs: list M.value) (j: nat)
             (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap) (o y: nat)
  : Lemma (requires pw_room /\ cok /\ holds x (dd dk cA cB cK hasC rs j ys ym) /\
                    (o == xA () \/ o == xB () \/ o == xK ()))
          (ensures M.major_edge (mx x) o y <==> ((o == xA () /\ y == xB ()) \/ (o == xB () /\ y == xK ())))
  = let d = dd dk cA cB cK hasC rs j ys ym in
    distinct ();
    holds_elim x d;
    db_dd dk cA cB cK hasC rs j ys ym (xB ());
    db_dd dk cA cB cK hasC rs j ys ym (xK ());
    db_dd dk cA cB cK hasC rs j ys ym (xA ());
    blk x d (xB ()); blk x d (xK ()); blk x d (xA ());
    db_dd dk cA cB cK hasC rs j ys ym o;
    st_vals ();
    l2 (vB ()) i1; l1 (vK2 ()); l3 i1 iw i1;
    let fwd () : Lemma (requires M.major_edge (mx x) o y)
                       (ensures (o == xA () /\ y == xB ()) \/ (o == xB () /\ y == xK ()))
      = eliminate exists (i a: nat). M.ptr_field (mx x) o i /\ M.field (mx x) o i == M.VPtr (M.Major a) /\
                                     M.resolve (mx x) a == Some y
        with fields_dd x cA cB cK o i a y in
    FStar.Classical.move_requires fwd ();
    if o = xA () && y = xB () then begin
      res_infix (mx x) (xK ());
      assert (M.ptr_field (mx x) o 0 /\ M.field (mx x) o 0 == M.VPtr (M.Major (xB ())))
    end;
    if o = xB () && y = xK () then begin
      res_infix (mx x) (xK ());
      assert (M.ptr_field (mx x) o 0 /\ M.field (mx x) o 0 == M.VPtr (M.Major (xK () + 2)))
    end

/// A grey block in use, described by `dd`: one of those described grey.
let grey_is (x: config pc) (dk: phk) (cA cB cK: M.colour) (hasC: bool) (rs: list M.value) (j: nat)
            (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap) (t: nat)
  : Lemma (requires pw_room /\ cok /\ holds x (dd dk cA cB cK hasC rs j ys ym) /\ dk == DM /\
                    M.is_block (mx x) t /\ M.col_of (mx x) t == M.Grey)
          (ensures (t == xA () /\ cA == M.Grey) \/ (t == xB () /\ cB == M.Grey) \/ (t == xK () /\ cK == M.Grey))
  = let d = dd dk cA cB cK hasC rs j ys ym in
    distinct ();
    holds_elim x d;
    iu_def x t;
    holds_iu x d t;
    holds_blk x d t

/// ---------------------------------------------------------------------------
/// The cycle's start
/// ---------------------------------------------------------------------------

/// With roots [A] and an empty nursery, A is the only outside reference.
let outside_A (x: config pc) (d: dsc) (o: nat)
  : Lemma (requires pw_room /\ cok /\ holds x d /\ d.drt == [vA ()] /\ d.dym == M.empty_heap ywords /\
                    iu x (xA ()) == true)
          (ensures M.outside_ref (wd x d) o <==> o == xA ())
  = l1 (vA ());
    res_iu x (xA ());
    outside_empty (wd x d) o

let white_dd (hasC: bool) (rs: list M.value) (j: nat) (y: nat)
  : Lemma (Some? ((ddv DI M.White M.White M.White hasC rs j).db y) ==>
           (Some?.v ((ddv DI M.White M.White M.White hasC rs j).db y)).bc == M.White)
  = ()

#push-options "--z3rlimit 40"
let start7 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x7 ()) (d7c ()) /\ PWK.spre (x7 ()) (d7c ()) /\
           (forall (o: nat). M.reachable (wd (x7 ()) (d7c ())) o <==> reach7_set o) /\
           (forall (o: nat). M.outside_ref (wd (x7 ()) (d7c ())) o <==> o == xA ()) /\
           iu (x7 ()) (xC ()) == true /\ ~(M.reachable (wd (x7 ()) (d7c ())) (xC ())))
  = h7c ();
    let x = x7 () in
    let d = d7c () in
    distinct ();
    holds_elim x d;
    db_dd DI M.White M.White M.White true [vA ()] 4 ms0 (M.empty_heap ywords) (xA ());
    db_dd DI M.White M.White M.White true [vA ()] 4 ms0 (M.empty_heap ywords) (xB ());
    db_dd DI M.White M.White M.White true [vA ()] 4 ms0 (M.empty_heap ywords) (xK ());
    blk x d (xA ()); blk x d (xB ()); blk x d (xK ()); blk x d (xC ());
    FStar.Classical.forall_intro (FStar.Classical.move_requires (outside_A x d));
    reach_dd x DI M.White M.White M.White true [vA ()] 4 ms0 (M.empty_heap ywords);
    l1 (vA ()); l2 (vB ()) i1; l1 (vK2 ()); l3 i1 iw i1;
    FStar.Classical.forall_intro (white_dd true [vA ()] 4);
    assert (iu x (xA ()) /\ iu x (xB ()) /\ iu x (xK ()));
    reach_r x d (xA ());
    reach_f x d (xA ()) 0 (xB ()) (xB ());
    res_infix (mx x) (xK ());
    reach_f x d (xB ()) 0 (xK () + 2) (xK ());
    assert (forall (y: nat). Some? (d.db y) ==> (Some?.v (d.db y)).bc == M.White);
    assert (forall (y: nat). M.outside_ref (wd x d) y ==> iu x y == true);
    assert (forall (y: nat). M.reachable (wd x d) y ==> iu x y == true);
    assert (d.dk == DI)
#pop-options

/// **EStart**: A grey.
let d8c () : GTot dsc = ddv DM M.Grey M.White M.White true [vA ()] 4

let s8 (sty: style) : Lemma (requires pw_room /\ cok)
  (ensures holds (step pc (x7 ()) EStart) (d8c ()) /\ RA.conds pc sty (x7 ()) EStart /\
           GC.Spec.Top.Transp.alloc_succeeds (x7 ()) EStart)
  = start7 ();
    let x = x7 () in
    let d = d7c () in
    PWK.step_start x d;
    distinct ();
    let pt (y: nat) : Lemma ((d8c ()).db y == (PWK.dstart x d).db y)
      = TM.outside_b_iff (wd x d) y in
    FStar.Classical.forall_intro pt;
    holds_ext (step pc x EStart) (PWK.dstart x d) (d8c ());
    enabled_start x d;
    conds_of sty x d EStart

/// ---------------------------------------------------------------------------
/// A minor collection of the empty nursery
/// ---------------------------------------------------------------------------

/// No field of the runs' blocks holds a young pointer; K is the closure.
let blocks_ok (dk: phk) (cA cB cK: M.colour) (hasC: bool) (rs: list M.value) (j: nat)
              (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap)
  : Lemma (requires pw_room /\ cok)
          (ensures PWM.no_yf (dd dk cA cB cK hasC rs j ys ym) /\ PWM.kdesc (dd dk cA cB cK hasC rs j ys ym) (xK ()))
  = distinct ();
    st_vals ();
    l2 (vB ()) i1; l1 (vK2 ()); l3 i1 iw i1; l1 (vB ())

#push-options "--z3rlimit 40"
let minor_empty (sty: style) (x: config pc) (dk: phk) (cA cB cK: M.colour) (hasC: bool) (rs: list M.value) (j: nat)
  : Lemma (requires pw_room /\ cok /\ holds x (ddv dk cA cB cK hasC rs j) /\
                    GC.Spec.Top.FFWStep.no_young rs == true /\ j + 2 <= n_pages)
          (ensures holds (step pc x EMinor) (ddv dk cA cB cK hasC rs (j + 2)) /\ RA.conds pc sty x EMinor /\
                   GC.Spec.Top.Transp.alloc_succeeds x EMinor)
  = let d = ddv dk cA cB cK hasC rs j in
    blocks_ok dk cA cB cK hasC rs j ms0 (M.empty_heap ywords);
    PWM.ym0_ok (xK ());
    assert (PWM.mstep_pre x d (xK ()));
    PWM.step_minor x d (xK ());
    let d' = PWM.dminor x d in
    map_fwd d.dym (PWM.mfwd x) rs;
    let pt (y: nat) : Lemma (d'.db y == (ddv dk cA cB cK hasC rs (j + 2)).db y) = () in
    FStar.Classical.forall_intro pt;
    holds_ext (step pc x EMinor) d' (ddv dk cA cB cK hasC rs (j + 2));
    enabled_plain x d EMinor;
    conds_of sty x d EMinor
#pop-options

/// ---------------------------------------------------------------------------
/// A slice
/// ---------------------------------------------------------------------------

let ngA (t: nat) (cA: M.colour) : GTot M.colour = if t = xA () then M.Black else cA
let ngB (t: nat) (cB: M.colour) : GTot M.colour =
  if t = xB () then M.Black else if t = xA () && cB = M.White then M.Grey else cB
let ngK (t: nat) (cK: M.colour) : GTot M.colour =
  if t = xK () then M.Black else if t = xB () && cK = M.White then M.Grey else cK

let anygrey (cA cB cK: M.colour) : bool = cA = M.Grey || cB = M.Grey || cK = M.Grey

/// The pointer fields of the live blocks resolve.
let fres_dd (x: config pc) (dk: phk) (cA cB cK: M.colour) (hasC: bool) (rs: list M.value) (j: nat)
            (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap) (t i a: nat)
  : Lemma (requires pw_room /\ cok /\ holds x (dd dk cA cB cK hasC rs j ys ym) /\
                    (t == xA () \/ t == xB () \/ t == xK ()) /\
                    M.ptr_field (mx x) t i /\ M.field (mx x) t i == M.VPtr (M.Major a))
          (ensures Some? (M.resolve (mx x) a))
  = let d = dd dk cA cB cK hasC rs j ys ym in
    distinct ();
    holds_elim x d;
    db_dd dk cA cB cK hasC rs j ys ym t;
    db_dd dk cA cB cK hasC rs j ys ym (xB ());
    db_dd dk cA cB cK hasC rs j ys ym (xK ());
    blk x d t;
    blk x d (xB ()); blk x d (xK ());
    st_vals ();
    l2 (vB ()) i1; l1 (vK2 ()); l3 i1 iw i1;
    if t = xA () then (if i = 0 then ublk x d (xB ()))
    else if t = xB () then res_infix (mx x) (xK ())

/// What a slice of `dd` needs.
let slpre_dd (x: config pc) (cA cB cK: M.colour) (hasC: bool) (rs: list M.value) (j: nat)
  : Lemma (requires pw_room /\ cok /\ holds x (ddv DM cA cB cK hasC rs j) /\ anygrey cA cB cK)
          (ensures PWK.slpre x (ddv DM cA cB cK hasC rs j))
  = let d = ddv DM cA cB cK hasC rs j in
    distinct ();
    holds_elim x d;
    db_dd DM cA cB cK hasC rs j ms0 (M.empty_heap ywords) (xA ());
    db_dd DM cA cB cK hasC rs j ms0 (M.empty_heap ywords) (xB ());
    db_dd DM cA cB cK hasC rs j ms0 (M.empty_heap ywords) (xK ());
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
          grey_is x DM cA cB cK hasC rs j ms0 (M.empty_heap ywords) t;
          FStar.Classical.forall_intro (edges_dd x DM cA cB cK hasC rs j ms0 (M.empty_heap ywords) t);
          FStar.Classical.forall_intro_2 (fun i a ->
            FStar.Classical.move_requires (fres_dd x DM cA cB cK hasC rs j ms0 (M.empty_heap ywords) t i) a)
        end in
    FStar.Classical.forall_intro gt

/// **ESlice** on `dd`: the grey block the mark finds turns black, its white
/// target grey.
#push-options "--z3rlimit 40"
let slice_dd (sty: style) (x: config pc) (cA cB cK: M.colour) (hasC: bool) (rs: list M.value) (j: nat)
  : Lemma (requires pw_room /\ cok /\ holds x (ddv DM cA cB cK hasC rs j) /\ anygrey cA cB cK)
          (ensures (let t = PWK.fg x in
                    ((t == xA () /\ cA == M.Grey) \/ (t == xB () /\ cB == M.Grey) \/ (t == xK () /\ cK == M.Grey)) /\
                    holds (step pc x (PWK.esl x)) (ddv DM (ngA t cA) (ngB t cB) (ngK t cK) hasC rs j) /\
                    RA.conds pc sty x (PWK.esl x) /\ GC.Spec.Top.Transp.alloc_succeeds x (PWK.esl x)))
  = let d = ddv DM cA cB cK hasC rs j in
    slpre_dd x cA cB cK hasC rs j;
    PWK.step_slice x d;
    let t = PWK.fg x in
    PWK.grey_found x d;
    grey_is x DM cA cB cK hasC rs j ms0 (M.empty_heap ywords) t;
    distinct ();
    let d' = ddv DM (ngA t cA) (ngB t cB) (ngK t cK) hasC rs j in
    let pt (y: nat) : Lemma (d'.db y == (PWK.dslice x d).db y)
      = TM.edge_b_iff (mx x) t y;
        edges_dd x DM cA cB cK hasC rs j ms0 (M.empty_heap ywords) t y in
    FStar.Classical.forall_intro pt;
    holds_ext (step pc x (PWK.esl x)) (PWK.dslice x d) d';
    enabled_slice x d;
    conds_of sty x d (PWK.esl x)
#pop-options

/// ---------------------------------------------------------------------------
/// The hand-over and the end
/// ---------------------------------------------------------------------------

module PWS = GC.Spec.Top.PWSweep

/// A dark block in use is one of the live blocks.
let dark_is (x: config pc) (dk: phk) (cA cB cK: M.colour) (hasC: bool) (rs: list M.value) (j: nat) (o: nat)
  : Lemma (requires pw_room /\ cok /\ holds x (ddv dk cA cB cK hasC rs j) /\ dk == DM /\
                    M.is_block (mx x) o /\ M.dark (M.col_of (mx x) o))
          (ensures (o == xA () /\ cA == M.col_of (mx x) o) \/ (o == xB () /\ cB == M.col_of (mx x) o) \/
                   (o == xK () /\ cK == M.col_of (mx x) o))
  = let d = ddv dk cA cB cK hasC rs j in
    distinct ();
    holds_elim x d;
    iu_def x o;
    holds_iu x d o;
    holds_blk x d o

#push-options "--z3rlimit 40"
let hand_dd (sty: style) (x: config pc) (hasC: bool) (rs: list M.value) (j: nat)
  : Lemma (requires pw_room /\ cok /\ holds x (ddv DM M.Black M.Black M.Black hasC rs j))
          (ensures holds (step pc x EHandover) (ddv DS M.Black M.Black M.Black hasC rs j) /\
                   RA.conds pc sty x EHandover /\ GC.Spec.Top.Transp.alloc_succeeds x EHandover /\
                   (forall (y: nat). iu x y == true ==> unsw (step pc x EHandover) y == true))
  = let d = ddv DM M.Black M.Black M.Black hasC rs j in
    distinct ();
    holds_elim x d;
    db_dd DM M.Black M.Black M.Black hasC rs j ms0 (M.empty_heap ywords) (xB ());
    db_dd DM M.Black M.Black M.Black hasC rs j ms0 (M.empty_heap ywords) (xK ());
    blk x d (xB ()); blk x d (xK ());
    let ng (o: nat) : Lemma (M.is_block (mx x) o ==> M.col_of (mx x) o <> M.Grey)
      = if M.is_block (mx x) o && M.col_of (mx x) o = M.Grey then
          grey_is x DM M.Black M.Black M.Black hasC rs j ms0 (M.empty_heap ywords) o in
    FStar.Classical.forall_intro ng;
    let dc (o i a y: nat) : Lemma (M.is_block (mx x) o /\ M.dark (M.col_of (mx x) o) /\ M.ptr_field (mx x) o i /\
                                   M.field (mx x) o i == M.VPtr (M.Major a) /\ M.resolve (mx x) a == Some y ==>
                                   M.col_of (mx x) y =!= M.White)
      = if FStar.IndefiniteDescription.strong_excluded_middle
             (M.is_block (mx x) o /\ M.dark (M.col_of (mx x) o) /\ M.ptr_field (mx x) o i /\
              M.field (mx x) o i == M.VPtr (M.Major a) /\ M.resolve (mx x) a == Some y)
        then begin
          dark_is x DM M.Black M.Black M.Black hasC rs j o;
          edges_dd x DM M.Black M.Black M.Black hasC rs j ms0 (M.empty_heap ywords) o y
        end in
    FStar.Classical.forall_intro_4 dc;
    let lab (y: nat) : Lemma (Some? (d.db y) ==>
                              ((Some?.v (d.db y)).blv ==> (Some?.v (d.db y)).bc == M.Black) /\
                              (not (Some?.v (d.db y)).blv ==> (Some?.v (d.db y)).bc == M.White))
      = () in
    FStar.Classical.forall_intro lab;
    assert (PWS.hpre x d);
    PWS.hand_model x d;
    PWS.step_hand x d;
    holds_ext (step pc x EHandover) (PWS.dhand d) (ddv DS M.Black M.Black M.Black hasC rs j);
    enabled_hand x d;
    conds_of sty x d EHandover
#pop-options

let end_dd (sty: style) (x: config pc) (hasC: bool) (rs: list M.value) (j: nat)
  : Lemma (requires pw_room /\ cok /\ holds x (ddv DS M.Black M.Black M.Black hasC rs j) /\ PWS.nsx x == 0)
          (ensures holds (step pc x EEnd) (ddv DI M.White M.White M.White false rs j) /\
                   RA.conds pc sty x EEnd /\ GC.Spec.Top.Transp.alloc_succeeds x EEnd)
  = let d = ddv DS M.Black M.Black M.Black hasC rs j in
    PWS.step_end x d;
    distinct ();
    let pt (y: nat) : Lemma ((ddv DI M.White M.White M.White false rs j).db y == (PWS.dend d).db y) = () in
    FStar.Classical.forall_intro pt;
    holds_ext (step pc x EEnd) (PWS.dend d) (ddv DI M.White M.White M.White false rs j);
    match sty with Sequential -> () | Incremental -> ()

/// The sweep's steps allocate nothing.
#push-options "--fuel 1"
let rec nf_repl (x: config pc) (k: nat) : Lemma (ensures nf_tail x (PWS.repl k)) (decreases k)
  = if k = 0 then () else (asucc_def x ESweep; nf_repl (step pc x ESweep) (k - 1))
#pop-options
