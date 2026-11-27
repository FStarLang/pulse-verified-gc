/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWSeq - the first-fit collector's sequential witness run
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  A run of the first-fit collector (`FFComps.fc`), in the
/// sequential style, from the allocator's initial heap of `msize` words,
/// under `ff_room` (GC.Spec.Top.FFWState):
///   0-3   A, B, C (holding a pointer to B), K (a closure: its second field
///         an infix header) allocated and filled, through first-fit;
///   4-5   A.0 := B, A.1 := an infix pointer into K (the barrier, idle);
///   6-7   the roots become [A]; a read of A.0 into a new root;
///   8     the cycle starts: A, B, K reachable, C in use and unreachable;
///   9     a minor collection while marking (empty nursery);
///   10-12 three mark slices (B, A greying K through the infix pointer, K);
///   13    hand-over to the sweep;
///   14-19 sweep steps: the free block, a minor collection while sweeping,
///         K whitened, C freed, B and A whitened;
///   20    the cycle ends;
///   21-22 two young allocations: Y1 holding the infix pointer into K, Y2
///         holding an integer that reads as an infix header;
///   23    the roots become [A; Y1; Y2];
///   24    a minor collection while idle, of Y1 and Y2.
/// Every event is enabled, in the style, and meets the program's obligations
/// (`seq_run_ok`); with the components' contracts (`FFComps.ff_components_ok`)
/// every hypothesis of `gc_correct` and `gc_correct_local` holds
/// (`ff_vacuity_sequential`).  In the sequential style the program runs only
/// while idle, so no write happens while marking: the barrier's darkening is
/// exercised by the incremental run (GC.Spec.Top.FFWInc).

module GC.Spec.Top.FFWSeq

open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.ByteRep
open GC.Spec.Top.Run
open GC.Spec.Top.RunFacts
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.FFWState
open GC.Spec.Top.FFWOps
open GC.Spec.Top.FFWStep
open GC.Spec.Top.FFWRun
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module FWS = GC.Spec.Top.FFWSweep
module FM0 = GC.Spec.Top.FFWMinor0
module MK = GC.Spec.Top.FFWMark
module SS = GC.Spec.Top.FFWStart
module OK = GC.Spec.Top.FFWOk
module YW = GC.Spec.Top.FFWYoung
module BM = GC.Spec.Top.ByteMark
module FC = GC.Spec.Top.FFComps
module TM = GC.Spec.Top.ToyMark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The run
/// ---------------------------------------------------------------------------

let vA : M.value = M.VPtr (M.Major xA)
let vB : M.value = M.VPtr (M.Major xB)
let vC : M.value = M.VPtr (M.Major xC)
let vK : M.value = M.VPtr (M.Major xK)
let vK2 : M.value = M.VPtr (M.Major (xK + 2))
let i1 : M.value = M.VInt 1
let iw : M.value = M.infix_word 2
let y1 : M.value = M.VPtr (M.Young 0)
let y2 : M.value = M.VPtr (M.Young 2)

let es_seq : list event = [
  EAlloc 2 0 [i1; i1];                       (* 0: A *)
  EAlloc 1 0 [i1];                           (* 1: B *)
  EAlloc 1 0 [vB];                           (* 2: C, C.0 = B *)
  EAlloc 3 M.closure_tag [i1; iw; i1];       (* 3: K, an infix header at K.1 *)
  EWrite (M.Major xA) 0 vB;                  (* 4: A.0 := B *)
  EWrite (M.Major xA) 1 vK2;                 (* 5: A.1 := an infix pointer into K *)
  ERoots [vA];                               (* 6: drop B, C, K from the roots *)
  ERead (M.Major xA) 0;                      (* 7: read A.0 (B) into a root *)
  EStart;                                    (* 8 *)
  EMinor;                                    (* 9: while marking *)
  ESlice MK.sl_B;                                    (* 10: B *)
  ESlice MK.sl_A;                                    (* 11: A, greys K *)
  ESlice MK.sl_K;                                    (* 12: K *)
  EHandover;                                 (* 13 *)
  ESweep;                                    (* 14: the free block *)
  EMinor;                                    (* 15: while sweeping *)
  ESweep;                                    (* 16: K whitened *)
  ESweep;                                    (* 17: C freed *)
  ESweep;                                    (* 18: B whitened *)
  ESweep;                                    (* 19: A whitened *)
  EEnd;                                      (* 20 *)
  EYoungAlloc 1 0 [vK2];                     (* 21: Y1, an infix pointer into K *)
  EYoungAlloc 1 0 [iw];                      (* 22: Y2, an integer reading as an infix header *)
  ERoots [vA; y1; y2];                       (* 23 *)
  EMinor                                     (* 24: while idle, of Y1 and Y2 *)
]

let len_seq () : Lemma (L.length es_seq == 25) = assert_norm (L.length es_seq == 25)

let cs (i: nat) : GTot (config fc) = at fc msize ywords es_seq i

/// The configuration after `i + 1` events.
let next (i: nat) (e: event)
  : Lemma (requires i < L.length es_seq /\ ev es_seq i == e) (ensures cs (i + 1) == step fc (cs i) e)
  = at_succ fc msize ywords es_seq i

/// ---------------------------------------------------------------------------
/// The heaps
/// ---------------------------------------------------------------------------

let st1 = { st0 with f = sub msize 4; ca = Some M.White; a0 = i1; a1 = i1 }
let st2 = { st1 with f = sub msize 6; cb = Some M.White }
let st3 = { st2 with f = sub msize 8; cc = Some M.White; c0 = vB }
let st4 = { st3 with f = sub msize 12; ck = Some M.White }
let st5 = { st4 with a0 = vB }
let st6 = { st5 with a1 = vK2 }
let st7 = { st6 with ca = Some M.Grey; cb = Some M.Grey }
let st8 = { st7 with cb = Some M.Black }
let st9 = { st8 with ca = Some M.Black; ck = Some M.Grey }
let st10 = { st9 with ck = Some M.Black }
let st11 = { st10 with ck = Some M.White }
let st12 = { st11 with cc = Some M.Blue; c0 = st11.lk; lk = vC }
let st13 = { st12 with cb = Some M.White }
let st14 = { st13 with ca = Some M.White }

let ym0 : M.mheap = M.empty_heap ywords

let dI (st: wst) (rs: list M.value) : dsc = { dph = T.Idle; dst = st; dys = FM0.ms0; dym = ym0; drt = rs }
let dM (st: wst) : dsc = { dph = T.Marking; dst = st; dys = FM0.ms0; dym = ym0; drt = [vB; vA] }
let dS (o: nat) (st: wst) : dsc = { dph = T.Sweeping (FWS.cur o); dst = st; dys = FM0.ms0; dym = ym0; drt = [vB; vA] }

let d1 = dI st1 [vA]
let d2 = dI st2 [vB; vA]
let d3 = dI st3 [vC; vB; vA]
let d4 = dI st4 [vK; vC; vB; vA]
let d5 = dI st5 [vK; vC; vB; vA]
let d6 = dI st6 [vK; vC; vB; vA]
let d7 = dI st6 [vA]
let d8 = dI st6 [vB; vA]
let d9 = dM st7
let d11 = dM st8
let d12 = dM st9
let d13 = dM st10
let d14 = dS 0 st10
let d15 = dS xK st10
let d17 = dS xC st11
let d18 = dS xB st12
let d19 = dS xA st13
let d20 = dS msize st14
let d21 = dI st14 [vB; vA]
let d22 () : GTot dsc = { d21 with dys = YW.ms1 vK2; dym = YW.ym1 vK2; drt = [y1; vB; vA] }
let d23 () : GTot dsc = { d21 with dys = YW.ms2 vK2 iw; dym = YW.ym2 vK2 iw; drt = [y2; y1; vB; vA] }
let d24 () : GTot dsc = { d21 with dys = YW.ms2 vK2 iw; dym = YW.ym2 vK2 iw; drt = [vA; y1; y2] }

/// ---------------------------------------------------------------------------
/// Words the run stores
/// ---------------------------------------------------------------------------

#push-options "--fuel 3"
let stores (_: unit)
  : Lemma (requires ff_room)
          (ensures R.storable_all byte_rep [i1; i1] /\ R.storable_all byte_rep [i1] /\ R.storable_all byte_rep [vB] /\
                   R.storable_all byte_rep [i1; iw; i1] /\ R.storable_all byte_rep [vK2] /\ R.storable_all byte_rep [iw] /\
                   R.storable_all byte_rep [vA] /\ R.storable_all byte_rep [vA; y1; y2] /\
                   storable_w vB /\ storable_w vK2 /\ storable_w i1 /\ storable_w iw /\
                   no_young [i1; i1] == true /\ no_young [i1] == true /\ no_young [vB] == true /\
                   no_young [i1; iw; i1] == true /\ no_young [vK2] == true /\ no_young [vB] == true /\
                   L.length [i1; i1] == 2 /\ L.length [i1] == 1 /\ L.length [vB] == 1 /\
                   L.length [i1; iw; i1] == 3 /\ L.length [vK2] == 1 /\ L.length [iw] == 1)
  = xs ();
    base_facts ();
    assert_norm (1 < pow2 64);
    st_int 1; st_iw (); st_maj xA; st_maj xB; st_maj (xK + 2); st_yng 0; st_yng 2
#pop-options

/// ---------------------------------------------------------------------------
/// The configurations, event by event
/// ---------------------------------------------------------------------------

/// The lowest grey blocks.
let low7 () : Lemma (requires ff_room)
  (ensures forall (o: nat). o < xB /\ M.is_block (mk st7) o ==> M.col_of (mk st7) o <> M.Grey) = xs ()
let low8 () : Lemma (requires ff_room)
  (ensures forall (o: nat). o < xA /\ M.is_block (mk st8) o ==> M.col_of (mk st8) o <> M.Grey) = xs ()
let low9 () : Lemma (requires ff_room)
  (ensures forall (o: nat). o < xK /\ M.is_block (mk st9) o ==> M.col_of (mk st9) o <> M.Grey) = xs ()

let ev_is (i: nat) (e: event) : prop = i < L.length es_seq /\ ev es_seq i == e

#push-options "--z3rlimit 40"
let h0 () : Lemma (requires ff_room) (ensures holds (cs 0) (dI st0 []))
  = init_holds es_seq

let h1 () : Lemma (requires ff_room) (ensures holds (cs 1) d1)
  = h0 (); len_seq (); xs (); stores ();
    assert_norm (ev es_seq 0 == EAlloc 2 0 [i1; i1]);
    next 0 (EAlloc 2 0 [i1; i1]);
    alloc_A st0 M.White;
    assert_norm (L.length [i1; i1] == 2);
    step_alloc (cs 0) (dI st0 []) 2 0 [i1; i1] st1

let h2 () : Lemma (requires ff_room) (ensures holds (cs 2) d2)
  = h1 (); len_seq (); xs (); stores ();
    assert_norm (ev es_seq 1 == EAlloc 1 0 [i1]);
    next 1 (EAlloc 1 0 [i1]);
    alloc_B st1 M.White;
    step_alloc (cs 1) d1 1 0 [i1] st2

let h3 () : Lemma (requires ff_room) (ensures holds (cs 3) d3)
  = h2 (); len_seq (); xs (); stores ();
    assert_norm (ev es_seq 2 == EAlloc 1 0 [vB]);
    next 2 (EAlloc 1 0 [vB]);
    alloc_C st2 M.White vB;
    step_alloc (cs 2) d2 1 0 [vB] st3

let h4 () : Lemma (requires ff_room) (ensures holds (cs 4) d4)
  = h3 (); len_seq (); xs (); stores ();
    assert_norm (ev es_seq 3 == EAlloc 3 M.closure_tag [i1; iw; i1]);
    next 3 (EAlloc 3 M.closure_tag [i1; iw; i1]);
    alloc_K st3 M.White;
    step_alloc (cs 3) d3 3 M.closure_tag [i1; iw; i1] st4

let h5 () : Lemma (requires ff_room) (ensures holds (cs 5) d5)
  = h4 (); holds_brep (cs 4) d4; len_seq (); xs (); stores ();
    assert_norm (ev es_seq 4 == EWrite (M.Major xA) 0 vB);
    next 4 (EWrite (M.Major xA) 0 vB);
    blk st4 xA;
    set_a0 st4 vB;
    OK.a0_ok st4 vB;
    step_write (cs 4) d4 xA 0 vB st5

let h6 () : Lemma (requires ff_room) (ensures holds (cs 6) d6)
  = h5 (); holds_brep (cs 5) d5; len_seq (); xs (); stores ();
    assert_norm (ev es_seq 5 == EWrite (M.Major xA) 1 vK2);
    next 5 (EWrite (M.Major xA) 1 vK2);
    blk st5 xA;
    set_a1 st5 vK2;
    OK.a1_ok st5 vK2;
    step_write (cs 5) d5 xA 1 vK2 st6

let h7 () : Lemma (requires ff_room) (ensures holds (cs 7) d7)
  = h6 (); len_seq ();
    assert_norm (ev es_seq 6 == ERoots [vA]);
    next 6 (ERoots [vA]);
    step_roots (cs 6) d6 [vA]

let h8 () : Lemma (requires ff_room) (ensures holds (cs 8) d8)
  = h7 (); len_seq (); xs ();
    assert_norm (ev es_seq 7 == ERead (M.Major xA) 0);
    next 7 (ERead (M.Major xA) 0);
    blk st6 xA;
    step_read (cs 7) d7 xA 0

let h9 () : Lemma (requires ff_room) (ensures holds (cs 9) d9)
  = h8 (); holds_brep (cs 8) d8; len_seq (); xs ();
    assert_norm (ev es_seq 8 == EStart);
    next 8 EStart;
    SS.roots_two (); SS.empty_ywords ();
    assert (SS.st_start st6);
    SS.start_pre st6 ym0 [vB; vA];
    MK.start_seq st6 ym0;
    OK.recol_ok st6 xA M.Grey;
    OK.recol_ok (recol st6 xA M.Grey) xB M.Grey;
    recol_A st6 M.Grey; recol_B ({ st6 with ca = Some M.Grey }) M.Grey;
    step_start (cs 8) d8 st7

let h10 () : Lemma (requires ff_room) (ensures holds (cs 10) d9)
  = h9 (); len_seq ();
    assert_norm (ev es_seq 9 == EMinor);
    next 9 EMinor;
    step_minor0 (cs 9) d9

let h11 () : Lemma (requires ff_room) (ensures holds (cs 11) d11)
  = h10 (); holds_brep (cs 10) d9; len_seq (); xs ();
    assert_norm (ev es_seq 10 == ESlice MK.sl_B);
    next 10 (ESlice MK.sl_B);
    blk st7 xB;
    MK.scan_B st7;
    low7 ();
    MK.slice_B st7;
    MK.mv_B st7;
    OK.recol_ok st7 xB M.Black;
    recol_B st7 M.Black;
    step_slice (cs 10) d9 xB st8 MK.sl_B

let h12 () : Lemma (requires ff_room) (ensures holds (cs 12) d12)
  = h11 (); holds_brep (cs 11) d11; len_seq (); xs ();
    assert_norm (ev es_seq 11 == ESlice MK.sl_A);
    next 11 (ESlice MK.sl_A);
    blk st8 xA; blk st8 xB; res_k2 st8;
    MK.scan_A st8;
    low8 ();
    MK.slice_A st8;
    MK.mv_A st8;
    OK.recol_ok st8 xA M.Black;
    OK.recol_ok (recol st8 xA M.Black) xK M.Grey;
    recol_A st8 M.Black; recol_K ({ st8 with ca = Some M.Black }) M.Grey;
    step_slice (cs 11) d11 xA st9 MK.sl_A

let h13 () : Lemma (requires ff_room) (ensures holds (cs 13) d13)
  = h12 (); holds_brep (cs 12) d12; len_seq (); xs ();
    assert_norm (ev es_seq 12 == ESlice MK.sl_K);
    next 12 (ESlice MK.sl_K);
    blk st9 xK;
    MK.scan_K st9;
    low9 ();
    MK.slice_K st9;
    MK.mv_K st9;
    OK.recol_ok st9 xK M.Black;
    recol_K st9 M.Black;
    step_slice (cs 12) d12 xK st10 MK.sl_K

let h14 () : Lemma (requires ff_room) (ensures holds (cs 14) d14)
  = h13 (); len_seq ();
    assert_norm (ev es_seq 13 == EHandover);
    next 13 EHandover;
    step_handover (cs 13) d13

let h15 () : Lemma (requires ff_room) (ensures holds (cs 15) d15)
  = h14 (); len_seq (); xs ();
    assert_norm (ev es_seq 14 == ESweep);
    next 14 ESweep;
    step_sweep_head (cs 14) d14

let h16 () : Lemma (requires ff_room) (ensures holds (cs 16) d15)
  = h15 (); len_seq ();
    assert_norm (ev es_seq 15 == EMinor);
    next 15 EMinor;
    step_minor0 (cs 15) d15

let h17 () : Lemma (requires ff_room) (ensures holds (cs 17) d17)
  = h16 (); len_seq (); xs ();
    assert_norm (ev es_seq 16 == ESweep);
    next 16 ESweep;
    blk st10 xK;
    recol_eq st10 xK M.White;
    recol_K st10 M.White;
    step_sweep_black (cs 16) d15 xK st11

let h18 () : Lemma (requires ff_room) (ensures holds (cs 18) d18)
  = h17 (); holds_brep (cs 17) d17; len_seq (); xs ();
    assert_norm (ev es_seq 17 == ESweep);
    next 17 ESweep;
    blk st11 xC;
    free_C st11;
    OK.freed_ok st11;
    step_sweep_white (cs 17) d17 xC st12

let h19 () : Lemma (requires ff_room) (ensures holds (cs 19) d19)
  = h18 (); len_seq (); xs ();
    assert_norm (ev es_seq 18 == ESweep);
    next 18 ESweep;
    blk st12 xB;
    recol_eq st12 xB M.White;
    recol_B st12 M.White;
    step_sweep_black (cs 18) d18 xB st13

let h20 () : Lemma (requires ff_room) (ensures holds (cs 20) d20)
  = h19 (); len_seq (); xs ();
    assert_norm (ev es_seq 19 == ESweep);
    next 19 ESweep;
    blk st13 xA;
    recol_eq st13 xA M.White;
    recol_A st13 M.White;
    step_sweep_black (cs 19) d19 xA st14

let h21 () : Lemma (requires ff_room) (ensures holds (cs 21) d21)
  = h20 (); len_seq ();
    assert_norm (ev es_seq 20 == EEnd);
    next 20 EEnd;
    step_end (cs 20) d20

let h22 () : Lemma (requires ff_room) (ensures holds (cs 22) (d22 ()))
  = h21 (); len_seq (); stores ();
    assert_norm (ev es_seq 21 == EYoungAlloc 1 0 [vK2]);
    next 21 (EYoungAlloc 1 0 [vK2]);
    YW.yal1 vK2;
    step_yalloc (cs 21) d21 1 0 [vK2]

let h23 () : Lemma (requires ff_room) (ensures holds (cs 23) (d23 ()))
  = h22 (); len_seq (); stores ();
    assert_norm (ev es_seq 22 == EYoungAlloc 1 0 [iw]);
    next 22 (EYoungAlloc 1 0 [iw]);
    YW.yal2 vK2 iw;
    step_yalloc (cs 22) (d22 ()) 1 0 [iw]

let h24 () : Lemma (requires ff_room) (ensures holds (cs 24) (d24 ()))
  = h23 (); len_seq ();
    assert_norm (ev es_seq 23 == ERoots [vA; y1; y2]);
    next 23 (ERoots [vA; y1; y2]);
    step_roots (cs 23) (d23 ()) [vA; y1; y2]
#pop-options

/// ---------------------------------------------------------------------------
/// Lists
/// ---------------------------------------------------------------------------

#push-options "--fuel 5"
let mems (_: unit)
  : Lemma (L.memP vA [vA] /\ L.memP vB [vB; vA] /\ L.memP vA [vB; vA] /\
           L.memP vA [vK; vC; vB; vA] /\ L.memP vK [vK; vC; vB; vA] /\ L.memP vB [vK; vC; vB; vA] /\
           L.memP vA [y2; y1; vB; vA] /\ L.memP y1 [y2; y1; vB; vA] /\ L.memP y2 [y2; y1; vB; vA] /\
           L.memP vA [y1; vB; vA])
  = ()

let fill_ints (w: M.world) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires L.for_all M.VInt? vs == true /\ L.length vs <= 3) (ensures fill_ok w tag vs)
  = let f (i: nat) : Lemma (i < L.length vs ==> value_ok w (L.index vs i))
      = match vs with
        | [] -> ()
        | a :: tl -> (match tl with [] -> () | b :: tl' -> (match tl' with [] -> () | c :: _ -> ())) in
    FStar.Classical.forall_intro f

let fill_one (w: M.world) (tag: M.tag_t) (v: M.value)
  : Lemma (requires value_ok w v) (ensures fill_ok w tag [v])
  = let f (i: nat) : Lemma (i < 1 ==> value_ok w (L.index [v] i)) = () in
    FStar.Classical.forall_intro f

let roots1 (w: M.world) (v: M.value)
  : Lemma (requires value_ok w v) (ensures forall (u: M.value). L.memP u [v] ==> value_ok w u)
  = ()

let roots3 (w: M.world) (a b c: M.value)
  : Lemma (requires value_ok w a /\ value_ok w b /\ value_ok w c)
          (ensures forall (u: M.value). L.memP u [a; b; c] ==> value_ok w u)
  = ()

let ints (_: unit)
  : Lemma (L.for_all M.VInt? [i1; i1] == true /\ L.for_all M.VInt? [i1] == true /\
           L.for_all M.VInt? [i1; iw; i1] == true /\ L.for_all M.VInt? [iw] == true)
  = assert_norm (L.for_all M.VInt? [i1; iw; i1] == true);
    assert_norm (L.for_all M.VInt? [iw] == true)
#pop-options

/// ---------------------------------------------------------------------------
/// Every event is allowed
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let ok0 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 0) (ev es_seq 0))
  = h0 (); len_seq (); stores (); ints ();
    assert_norm (ev es_seq 0 == EAlloc 2 0 [i1; i1]);
    fill_ints (wd (dI st0 [])) 0 [i1; i1];
    ok_alloc Sequential (cs 0) (dI st0 []) 2 0 [i1; i1]

let ok1 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 1) (ev es_seq 1))
  = h1 (); len_seq (); stores (); ints ();
    assert_norm (ev es_seq 1 == EAlloc 1 0 [i1]);
    fill_ints (wd d1) 0 [i1];
    ok_alloc Sequential (cs 1) d1 1 0 [i1]

let ok2 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 2) (ev es_seq 2))
  = h2 (); len_seq (); stores (); mems (); xs ();
    assert_norm (ev es_seq 2 == EAlloc 1 0 [vB]);
    blk st2 xB;
    reach_root (wd d2) xB xB;
    vmaj_ok (wd d2) xB xB;
    fill_one (wd d2) 0 vB;
    ok_alloc Sequential (cs 2) d2 1 0 [vB]

let ok3 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 3) (ev es_seq 3))
  = h3 (); len_seq (); stores (); ints ();
    assert_norm (ev es_seq 3 == EAlloc 3 M.closure_tag [i1; iw; i1]);
    fill_ints (wd d3) M.closure_tag [i1; iw; i1];
    ok_alloc Sequential (cs 3) d3 3 M.closure_tag [i1; iw; i1]

let ok4 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 4) (ev es_seq 4))
  = h4 (); len_seq (); stores (); mems (); xs ();
    assert_norm (ev es_seq 4 == EWrite (M.Major xA) 0 vB);
    blk st4 xA; blk st4 xB;
    reach_root (wd d4) xA xA;
    reach_root (wd d4) xB xB;
    vmaj_ok (wd d4) xB xB;
    ok_write Sequential (cs 4) d4 xA 0 vB

let ok5 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 5) (ev es_seq 5))
  = h5 (); len_seq (); stores (); mems (); xs ();
    assert_norm (ev es_seq 5 == EWrite (M.Major xA) 1 vK2);
    blk st5 xA; blk st5 xK; res_k2 st5;
    reach_root (wd d5) xA xA;
    reach_root (wd d5) xK xK;
    vmaj_ok (wd d5) (xK + 2) xK;
    ok_write Sequential (cs 5) d5 xA 1 vK2

let ok6 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 6) (ev es_seq 6))
  = h6 (); len_seq (); stores (); mems ();
    assert_norm (ev es_seq 6 == ERoots [vA]);
    blk st6 xA;
    reach_root (wd d6) xA xA;
    vmaj_ok (wd d6) xA xA;
    roots1 (wd d6) vA;
    ok_roots Sequential (cs 6) d6 [vA]

let ok7 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 7) (ev es_seq 7))
  = h7 (); len_seq (); mems (); xs ();
    assert_norm (ev es_seq 7 == ERead (M.Major xA) 0);
    blk st6 xA;
    reach_root (wd d7) xA xA;
    ok_read Sequential (cs 7) d7 xA 0

let ok8 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 8) (ev es_seq 8))
  = h8 (); len_seq ();
    assert_norm (ev es_seq 8 == EStart);
    ok_start Sequential (cs 8) d8

let ok9 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 9) (ev es_seq 9))
  = h9 (); len_seq ();
    assert_norm (ev es_seq 9 == EMinor);
    ok_minor Sequential (cs 9) d9

let ok10 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 10) (ev es_seq 10))
  = h10 (); len_seq (); xs ();
    assert_norm (ev es_seq 10 == ESlice MK.sl_B);
    blk st7 xB;
    MK.mv_B st7; ok_slice Sequential (cs 10) d9 xB MK.sl_B

let ok11 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 11) (ev es_seq 11))
  = h11 (); len_seq (); xs ();
    assert_norm (ev es_seq 11 == ESlice MK.sl_A);
    blk st8 xA;
    MK.mv_A st8; ok_slice Sequential (cs 11) d11 xA MK.sl_A

let ok12 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 12) (ev es_seq 12))
  = h12 (); len_seq (); xs ();
    assert_norm (ev es_seq 12 == ESlice MK.sl_K);
    blk st9 xK;
    MK.mv_K st9; ok_slice Sequential (cs 12) d12 xK MK.sl_K

let ok13 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 13) (ev es_seq 13))
  = h13 (); len_seq (); xs ();
    assert_norm (ev es_seq 13 == EHandover);
    assert (T.no_grey (mk st10));
    ok_handover Sequential (cs 13) d13

let ok14 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 14) (ev es_seq 14))
  = h14 (); len_seq ();
    assert_norm (ev es_seq 14 == ESweep);
    ok_sweep Sequential (cs 14) d14 0

let ok15 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 15) (ev es_seq 15))
  = h15 (); len_seq ();
    assert_norm (ev es_seq 15 == EMinor);
    ok_minor Sequential (cs 15) d15

let ok16 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 16) (ev es_seq 16))
  = h16 (); len_seq (); xs ();
    assert_norm (ev es_seq 16 == ESweep);
    ok_sweep Sequential (cs 16) d15 xK

let ok17 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 17) (ev es_seq 17))
  = h17 (); len_seq (); xs ();
    assert_norm (ev es_seq 17 == ESweep);
    ok_sweep Sequential (cs 17) d17 xC

let ok18 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 18) (ev es_seq 18))
  = h18 (); len_seq (); xs ();
    assert_norm (ev es_seq 18 == ESweep);
    ok_sweep Sequential (cs 18) d18 xB

let ok19 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 19) (ev es_seq 19))
  = h19 (); len_seq (); xs ();
    assert_norm (ev es_seq 19 == ESweep);
    ok_sweep Sequential (cs 19) d19 xA

let ok20 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 20) (ev es_seq 20))
  = h20 (); len_seq ();
    assert_norm (ev es_seq 20 == EEnd);
    ok_end Sequential (cs 20) d20

let k_reach (st: wst) (rs: list M.value) (y: M.mheap)
  : Lemma (requires ff_room /\ Some? st.ca /\ Some? st.ck /\ st.a1 == vK2 /\ L.memP vA rs)
          (ensures value_ok ({ M.maj = mk st; M.yng = y; M.roots = rs; M.rem = [] }) vK2)
  = let w = { M.maj = mk st; M.yng = y; M.roots = rs; M.rem = [] } in
    xs ();
    blk st xA; res_k2 st;
    reach_root w xA xA;
    reach_edge w xA 1 (xK + 2) xK;
    vmaj_ok w (xK + 2) xK

let ok21 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 21) (ev es_seq 21))
  = h21 (); len_seq (); stores (); mems ();
    assert_norm (ev es_seq 21 == EYoungAlloc 1 0 [vK2]);
    k_reach st14 [vB; vA] ym0;
    fill_one (wd d21) 0 vK2;
    YW.yal1 vK2;
    ok_yalloc Sequential (cs 21) d21 1 0 [vK2]

let ok22 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 22) (ev es_seq 22))
  = h22 (); len_seq (); stores (); ints ();
    assert_norm (ev es_seq 22 == EYoungAlloc 1 0 [iw]);
    fill_ints (wd (d22 ())) 0 [iw];
    YW.yal2 vK2 iw;
    ok_yalloc Sequential (cs 22) (d22 ()) 1 0 [iw]

let ok23 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 23) (ev es_seq 23))
  = h23 (); len_seq (); stores (); mems (); xs ();
    assert_norm (ev es_seq 23 == ERoots [vA; y1; y2]);
    let w = wd (d23 ()) in
    blk st14 xA;
    reach_root w xA xA;
    vmaj_ok w xA xA;
    YW.yblocks vK2 iw;
    yreach_root w 0 0;
    yreach_root w 2 2;
    vyng_ok w 0 0;
    vyng_ok w 2 2;
    roots3 w vA y1 y2;
    ok_roots Sequential (cs 23) (d23 ()) [vA; y1; y2]

let ok24 () : Lemma (requires ff_room /\ L.length es_seq == 25) (ensures ok_at Sequential (cs 24) (ev es_seq 24))
  = h24 (); len_seq ();
    assert_norm (ev es_seq 24 == EMinor);
    ok_minor Sequential (cs 24) (d24 ())
#pop-options

/// ---------------------------------------------------------------------------
/// The run is allowed, and every hypothesis holds
/// ---------------------------------------------------------------------------

let seq_ok (i: nat)
  : Lemma (requires ff_room /\ i < 25) (ensures i < L.length es_seq /\ ok_at Sequential (cs i) (ev es_seq i))
  = len_seq ();
    match i with
    | 0 -> ok0 () | 1 -> ok1 () | 2 -> ok2 () | 3 -> ok3 () | 4 -> ok4 () | 5 -> ok5 () | 6 -> ok6 ()
    | 7 -> ok7 () | 8 -> ok8 () | 9 -> ok9 () | 10 -> ok10 () | 11 -> ok11 () | 12 -> ok12 ()
    | 13 -> ok13 () | 14 -> ok14 () | 15 -> ok15 () | 16 -> ok16 () | 17 -> ok17 () | 18 -> ok18 ()
    | 19 -> ok19 () | 20 -> ok20 () | 21 -> ok21 () | 22 -> ok22 () | 23 -> ok23 () | 24 -> ok24 ()

/// **The sequential run is allowed.**
let seq_run_ok () : Lemma (requires ff_room) (ensures run_ok fc Sequential msize ywords es_seq)
  = len_seq ();
    let f (i: nat) : Lemma (i < L.length es_seq ==>
                            (let x = at fc msize ywords es_seq i in
                             let e = ev es_seq i in
                             enabled fc x e /\ style_ok Sequential x e /\ mutator_ok x e))
      = if i < 25 then seq_ok i in
    FStar.Classical.forall_intro f

/// **Every hypothesis of `gc_correct` and `gc_correct_local` holds of the
/// sequential run.**
let ff_vacuity_sequential ()
  : Lemma (requires ff_room)
          (ensures components_ok fc /\ run_ok fc Sequential msize ywords es_seq /\
                   run_hyps fc msize ywords es_seq)
  = FC.ff_components_ok ();
    seq_run_ok ();
    run_hyps_of_ok fc msize ywords es_seq

/// Every event occurs in the run.
let every_event (es: list event) : bool =
  L.existsb EAlloc? es && L.existsb EYoungAlloc? es && L.existsb EWrite? es && L.existsb ERead? es &&
  L.existsb ERoots? es &&
  L.existsb EMinor? es && L.existsb EStart? es && L.existsb ESlice? es && L.existsb EHandover? es &&
  L.existsb ESweep? es && L.existsb EEnd? es

let seq_every_event () : Lemma (every_event es_seq) = assert_norm (every_event es_seq)

/// A minor collection in each phase: at 9 (marking), 15 (sweeping), 24 (idle).
let seq_minor_phases ()
  : Lemma (requires ff_room /\ L.length es_seq == 25)
          (ensures ev es_seq 9 == EMinor /\ T.Marking? (cs 9).ph /\
                   ev es_seq 15 == EMinor /\ T.Sweeping? (cs 15).ph /\
                   ev es_seq 24 == EMinor /\ T.Idle? (cs 24).ph)
  = len_seq ();
    assert_norm (ev es_seq 9 == EMinor /\ ev es_seq 15 == EMinor /\ ev es_seq 24 == EMinor);
    h9 (); h15 (); h24 ();
    holds_def (cs 9) d9; holds_def (cs 15) d15; holds_def (cs 24) (d24 ())

/// ---------------------------------------------------------------------------
/// Non-triviality
/// ---------------------------------------------------------------------------

/// **At the cycle's start: a root, the reachable A, B (through the root
/// read from A.0) and K (only through A's infix pointer), and C, in use and
/// unreachable.**
#push-options "--z3rlimit 40"
let seq_nontrivial ()
  : Lemma (requires ff_room)
          (ensures (let x = cs 8 in
                    let w = vw x in
                    L.memP vA w.M.roots /\ M.reachable w xA /\ M.reachable w xB /\ M.reachable w xK /\
                    T.in_use fc.a x.ast x.w.cmaj w.M.maj xC == true /\ ~(M.reachable w xC)))
  = h8 (); mems (); xs ();
    let x = cs 8 in
    let w0 = wd d8 in
    views_wd x d8;
    holds_def x d8;
    blk st6 xA; blk st6 xB; blk st6 xC; res_k2 st6;
    reach_root w0 xA xA;
    reach_root w0 xB xB;
    reach_edge w0 xA 1 (xK + 2) xK;
    SS.roots_two (); SS.empty_ywords ();
    SS.c_unreachable st6 ym0 [vB; vA];
    reachable_wheq w0 (vw x) xA;
    reachable_wheq w0 (vw x) xB;
    reachable_wheq w0 (vw x) xK;
    reachable_wheq w0 (vw x) xC;
    assert ((cabs x.w.cmaj).M.hd xC == (mk st6).M.hd xC)
#pop-options

#push-options "--fuel 4"
let infix_w0 ()
  : Lemma (requires ff_room)
          (ensures (let w = wd (d24 ()) in
                    M.yreachable w 0 /\ M.yreachable w 2 /\
                    M.field w.M.yng 0 0 == vK2 /\ M.field w.M.yng 2 0 == iw /\
                    M.resolve w.M.maj (xK + 2) == Some xK /\ M.is_block w.M.maj xK /\
                    M.col_of w.M.maj xK == M.White))
  = let w = wd (d24 ()) in
    xs ();
    res_k2 st14; blk st14 xK;
    YW.yblocks vK2 iw;
    assert (L.memP y1 [vA; y1; y2] /\ L.memP y2 [vA; y1; y2]);
    yreach_root w 0 0;
    yreach_root w 2 2
#pop-options

/// **The last minor collection sees both young blocks, reachable from the
/// roots: Y1's field is an infix pointer into the old closure K, which
/// resolves to K, in use; Y2's field is an integer that reads as an infix
/// header.**
#push-options "--z3rlimit 40"
let seq_infix_cases ()
  : Lemma (requires ff_room /\ L.length es_seq == 25)
          (ensures (let x = cs 24 in
                    let w = vw x in
                    ev es_seq 24 == EMinor /\
                    M.yreachable w 0 /\ M.yreachable w 2 /\
                    M.field w.M.yng 0 0 == M.VPtr (M.Major (xK + 2)) /\
                    M.resolve w.M.maj (xK + 2) == Some xK /\ T.in_use fc.a x.ast x.w.cmaj w.M.maj xK == true /\
                    M.field w.M.yng 2 0 == M.infix_word 2 /\ Some? (M.infix_hdr (M.field w.M.yng 2 0))))
  = h24 ();
    assert_norm (ev es_seq 24 == EMinor);
    let x = cs 24 in
    let w0 = wd (d24 ()) in
    infix_w0 ();
    views_wd x (d24 ());
    holds_def x (d24 ());
    wheq_sym (vw x) w0;
    yreachable_wheq w0 (vw x) 0;
    yreachable_wheq w0 (vw x) 2;
    resolve_heq w0.M.maj (vw x).M.maj (xK + 2);
    assert_norm (M.infix_hdr (M.infix_word 2) == Some 2);
    assert ((cabs x.w.cmaj).M.hd xK == (mk st14).M.hd xK)
#pop-options
