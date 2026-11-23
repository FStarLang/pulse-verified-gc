/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWInc - the first-fit collector's incremental witness run
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  A run of the first-fit collector (`FFComps.fc`), in the
/// incremental style, from the allocator's initial heap, under `ff_room`:
///   0-6   as the sequential run (GC.Spec.Top.FFWSeq): A, B, C, K allocated
///         and filled, A.0 := B, A.1 := an infix pointer into K, roots [A];
///   7     the cycle starts (A grey; A, B, K reachable, C unreachable);
///   8     while marking: D allocated, black, D.0 = B;
///   9     while marking: A.0 := 1, the barrier darkens B (white to grey);
///   10    a minor collection while marking;
///   11-13 mark slices (B, A greying K, K);
///   14    hand-over;
///   15    a sweep step (the free block);
///   16    while sweeping: E allocated, white (behind the cursor), E.0 = A;
///   17    while sweeping: D.0 := the infix pointer into K;
///   18    a minor collection while sweeping;
///   19-20 two young allocations (Y1: the infix pointer into K; Y2: an
///         integer that reads as an infix header);
///   21    the roots become [A; E; Y1; Y2] (D dropped);
///   22-26 sweep steps: D and K whitened, C freed, B and A whitened;
///   27    the cycle ends;
///   28    a read of A.1 (the infix pointer) into a root;
///   29    a minor collection while idle, of Y1 and Y2.
/// Every event is allowed (`inc_run_ok`); with the components' contracts every
/// hypothesis of `gc_correct` and `gc_correct_local` holds
/// (`ff_vacuity_incremental`).

module GC.Spec.Top.FFWInc

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
module SQ = GC.Spec.Top.FFWSeq
module BB = GC.Spec.Top.ByteBarrier
module FC = GC.Spec.Top.FFComps

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The run
/// ---------------------------------------------------------------------------

let vA = SQ.vA
let vB = SQ.vB
let vC = SQ.vC
let vD : M.value = M.VPtr (M.Major xD)
let vE : M.value = M.VPtr (M.Major xE)
let vK = SQ.vK
let vK2 = SQ.vK2
let i1 = SQ.i1
let iw = SQ.iw
let y1 = SQ.y1
let y2 = SQ.y2

let es_inc : list event = [
  EAlloc 2 0 [i1; i1];                       (* 0: A *)
  EAlloc 1 0 [i1];                           (* 1: B *)
  EAlloc 1 0 [vB];                           (* 2: C *)
  EAlloc 3 M.closure_tag [i1; iw; i1];       (* 3: K *)
  EWrite (M.Major xA) 0 vB;                  (* 4 *)
  EWrite (M.Major xA) 1 vK2;                 (* 5 *)
  ERoots [vA];                               (* 6 *)
  EStart;                                    (* 7 *)
  EAlloc 1 0 [vB];                           (* 8: D, black *)
  EWrite (M.Major xA) 0 i1;                  (* 9: the barrier darkens B *)
  EMinor;                                    (* 10: while marking *)
  ESlice;                                    (* 11: B *)
  ESlice;                                    (* 12: A *)
  ESlice;                                    (* 13: K *)
  EHandover;                                 (* 14 *)
  ESweep;                                    (* 15: the free block *)
  EAlloc 1 0 [vA];                           (* 16: E, white *)
  EWrite (M.Major xD) 0 vK2;                 (* 17 *)
  EMinor;                                    (* 18: while sweeping *)
  EYoungAlloc 1 0 [vK2];                     (* 19: Y1 *)
  EYoungAlloc 1 0 [iw];                      (* 20: Y2 *)
  ERoots [vA; vE; y1; y2];                   (* 21 *)
  ESweep;                                    (* 22: D *)
  ESweep;                                    (* 23: K *)
  ESweep;                                    (* 24: C freed *)
  ESweep;                                    (* 25: B *)
  ESweep;                                    (* 26: A *)
  EEnd;                                      (* 27 *)
  ERead (M.Major xA) 1;                      (* 28: the infix pointer into a root *)
  EMinor                                     (* 29: while idle, of Y1 and Y2 *)
]

let len_inc () : Lemma (L.length es_inc == 30) = assert_norm (L.length es_inc == 30)

let ci (i: nat) : GTot (config fc) = at fc msize ywords es_inc i

let next (i: nat) (e: event)
  : Lemma (requires i < L.length es_inc /\ ev es_inc i == e) (ensures ci (i + 1) == step fc (ci i) e)
  = at_succ fc msize ywords es_inc i

/// ---------------------------------------------------------------------------
/// The heaps
/// ---------------------------------------------------------------------------

let st6 = SQ.st6
let st7 = { st6 with ca = Some M.Grey }
let st8 = { st7 with f = sub msize 14; cd = Some M.Black; d0 = vB }
let st9 = { st8 with cb = Some M.Grey; a0 = i1 }
let st10 = { st9 with cb = Some M.Black }
let st11 = { st10 with ca = Some M.Black; ck = Some M.Grey }
let st12 = { st11 with ck = Some M.Black }
let st13 = { st12 with f = sub msize 16; ce = Some M.White }
let st14 = { st13 with d0 = vK2 }
let st15 = { st14 with cd = Some M.White }
let st16 = { st15 with ck = Some M.White }
let st17 = { st16 with cc = Some M.Blue; c0 = st16.lk; lk = vC }
let st18 = { st17 with cb = Some M.White }
let st19 = { st18 with ca = Some M.White }

let ym0 = SQ.ym0
let dI (st: wst) (rs: list M.value) : dsc = { dph = T.Idle; dst = st; dys = FM0.ms0; dym = ym0; drt = rs }
let dM (st: wst) (rs: list M.value) : dsc = { dph = T.Marking; dst = st; dys = FM0.ms0; dym = ym0; drt = rs }
let dS (o: nat) (st: wst) (rs: list M.value) : dsc =
  { dph = T.Sweeping (FWS.cur o); dst = st; dys = FM0.ms0; dym = ym0; drt = rs }

let d7 = dI st6 [vA]
let d8 = dM st7 [vA]
let d9 = dM st8 [vD; vA]
let d10 = dM st9 [vD; vA]
let d12 = dM st10 [vD; vA]
let d13 = dM st11 [vD; vA]
let d14 = dM st12 [vD; vA]
let d15 = dS 0 st12 [vD; vA]
let d16 = dS xD st12 [vD; vA]
let d17 = dS xD st13 [vE; vD; vA]
let d18 = dS xD st14 [vE; vD; vA]
let d20 () : GTot dsc = { d18 with dys = YW.ms1 vK2; dym = YW.ym1 vK2; drt = [y1; vE; vD; vA] }
let d21 () : GTot dsc = { d18 with dys = YW.ms2 vK2 iw; dym = YW.ym2 vK2 iw; drt = [y2; y1; vE; vD; vA] }
let yS (o: nat) (st: wst) : GTot dsc =
  { dph = T.Sweeping (FWS.cur o); dst = st; dys = YW.ms2 vK2 iw; dym = YW.ym2 vK2 iw; drt = [vA; vE; y1; y2] }
let d22 () = yS xD st14
let d23 () = yS xK st15
let d24 () = yS xC st16
let d25 () = yS xB st17
let d26 () = yS xA st18
let d27 () = yS msize st19
let d28 () : GTot dsc = { yS msize st19 with dph = T.Idle }
let d29 () : GTot dsc = { yS msize st19 with dph = T.Idle; drt = [vK2; vA; vE; y1; y2] }

/// ---------------------------------------------------------------------------
/// Model facts this run adds
/// ---------------------------------------------------------------------------

#push-options "--fuel 5"
let stores_inc (_: unit)
  : Lemma (requires ff_room)
          (ensures R.storable_all byte_rep [vA] /\ no_young [vA] == true /\ L.length [vA] == 1 /\
                   no_young [i1] == true /\ storable_w vK2 /\ storable_w i1 /\ no_young [vK2] == true /\
                   R.storable_all byte_rep [vA; vE; y1; y2] /\ storable_w vE)
  = xs (); base_facts ();
    st_maj xA; st_maj xE; st_maj (xK + 2); st_yng 0; st_yng 2;
    assert_norm (1 < pow2 64); st_int 1
#pop-options

/// The barrier while marking: A.0 held B, white; B turns grey.
#push-options "--z3rlimit 40"
let dark_B (st: wst)
  : Lemma (requires ff_room /\ Some? st.ca /\ st.cb == Some M.White /\ st.a0 == vB)
          (ensures R.heq (BB.tdark true (mk st) xA 0) (mk (recol st xB M.Grey)))
  = xs ();
    blk st xA; blk st xB;
    assert (T.old_target (mk st) xA 0 == Some xB);
    recol_eq st xB M.Grey
#pop-options

/// E's colour: behind the cursor, white.
let colour_E (_: unit)
  : Lemma (requires ff_room) (ensures T.colour_at ffk (T.Sweeping (FWS.cur xD)) xE == M.White)
  = xs (); FWS.cur_v xD

/// ---------------------------------------------------------------------------
/// The configurations, event by event
/// ---------------------------------------------------------------------------

/// The first seven events are the sequential run's.
let same_prefix (i: nat)
  : Lemma (requires i <= 7) (ensures ci i == SQ.cs i)
  = assert_norm (take 0 es_inc == take 0 SQ.es_seq);
    assert_norm (take 1 es_inc == take 1 SQ.es_seq);
    assert_norm (take 2 es_inc == take 2 SQ.es_seq);
    assert_norm (take 3 es_inc == take 3 SQ.es_seq);
    assert_norm (take 4 es_inc == take 4 SQ.es_seq);
    assert_norm (take 5 es_inc == take 5 SQ.es_seq);
    assert_norm (take 6 es_inc == take 6 SQ.es_seq);
    assert_norm (take 7 es_inc == take 7 SQ.es_seq)

let h7 () : Lemma (requires ff_room) (ensures holds (ci 7) d7)
  = SQ.h7 (); same_prefix 7

#push-options "--z3rlimit 40"
let h8 () : Lemma (requires ff_room) (ensures holds (ci 8) d8)
  = h7 (); holds_brep (ci 7) d7; len_inc (); xs ();
    assert_norm (ev es_inc 7 == EStart);
    next 7 EStart;
    SS.roots_one (); SS.empty_ywords ();
    assert (SS.st_start st6);
    SS.start_pre st6 ym0 [vA];
    MK.start_inc st6 ym0;
    OK.recol_ok st6 xA M.Grey;
    recol_A st6 M.Grey;
    step_start (ci 7) d7 st7

let h9 () : Lemma (requires ff_room) (ensures holds (ci 9) d9)
  = h8 (); len_inc (); xs (); SQ.stores ();
    assert_norm (ev es_inc 8 == EAlloc 1 0 [vB]);
    next 8 (EAlloc 1 0 [vB]);
    alloc_D st7 M.Black vB;
    step_alloc (ci 8) d8 1 0 [vB] st8

let h10 () : Lemma (requires ff_room) (ensures holds (ci 10) d10)
  = h9 (); holds_brep (ci 9) d9; len_inc (); xs (); stores_inc ();
    assert_norm (ev es_inc 9 == EWrite (M.Major xA) 0 i1);
    next 9 (EWrite (M.Major xA) 0 i1);
    blk st8 xA; blk st8 xB;
    dark_B st8;
    recol_B st8 M.Grey;
    set_field_heq (BB.tdark true (mk st8) xA 0) (mk ({ st8 with cb = Some M.Grey })) xA 0 i1;
    set_a0 ({ st8 with cb = Some M.Grey }) i1;
    OK.recol_ok st8 xB M.Grey;
    OK.a0_ok ({ st8 with cb = Some M.Grey }) i1;
    step_write (ci 9) d9 xA 0 i1 st9

let h11 () : Lemma (requires ff_room) (ensures holds (ci 11) d10)
  = h10 (); len_inc ();
    assert_norm (ev es_inc 10 == EMinor);
    next 10 EMinor;
    step_minor0 (ci 10) d10

let low9 () : Lemma (requires ff_room)
  (ensures forall (o: nat). o < xB /\ M.is_block (mk st9) o ==> M.col_of (mk st9) o <> M.Grey) = xs ()
let low10 () : Lemma (requires ff_room)
  (ensures forall (o: nat). o < xA /\ M.is_block (mk st10) o ==> M.col_of (mk st10) o <> M.Grey) = xs ()
let low11 () : Lemma (requires ff_room)
  (ensures forall (o: nat). o < xK /\ M.is_block (mk st11) o ==> M.col_of (mk st11) o <> M.Grey) = xs ()

let h12 () : Lemma (requires ff_room) (ensures holds (ci 12) d12)
  = h11 (); holds_brep (ci 11) d10; len_inc (); xs ();
    assert_norm (ev es_inc 11 == ESlice);
    next 11 ESlice;
    blk st9 xB;
    MK.scan_B st9;
    low9 ();
    MK.slice_B st9;
    OK.recol_ok st9 xB M.Black;
    recol_B st9 M.Black;
    step_slice (ci 11) d10 xB st10

let h13 () : Lemma (requires ff_room) (ensures holds (ci 13) d13)
  = h12 (); holds_brep (ci 12) d12; len_inc (); xs ();
    assert_norm (ev es_inc 12 == ESlice);
    next 12 ESlice;
    blk st10 xA; blk st10 xB; res_k2 st10;
    MK.scan_A st10;
    low10 ();
    MK.slice_A st10;
    OK.recol_ok st10 xA M.Black;
    OK.recol_ok (recol st10 xA M.Black) xK M.Grey;
    recol_A st10 M.Black; recol_K ({ st10 with ca = Some M.Black }) M.Grey;
    step_slice (ci 12) d12 xA st11

let h14 () : Lemma (requires ff_room) (ensures holds (ci 14) d14)
  = h13 (); holds_brep (ci 13) d13; len_inc (); xs ();
    assert_norm (ev es_inc 13 == ESlice);
    next 13 ESlice;
    blk st11 xK;
    MK.scan_K st11;
    low11 ();
    MK.slice_K st11;
    OK.recol_ok st11 xK M.Black;
    recol_K st11 M.Black;
    step_slice (ci 13) d13 xK st12

let h15 () : Lemma (requires ff_room) (ensures holds (ci 15) d15)
  = h14 (); len_inc ();
    assert_norm (ev es_inc 14 == EHandover);
    next 14 EHandover;
    step_handover (ci 14) d14

let h16 () : Lemma (requires ff_room) (ensures holds (ci 16) d16)
  = h15 (); len_inc (); xs ();
    assert_norm (ev es_inc 15 == ESweep);
    next 15 ESweep;
    step_sweep_head (ci 15) d15

let h17 () : Lemma (requires ff_room) (ensures holds (ci 17) d17)
  = h16 (); len_inc (); xs (); stores_inc ();
    assert_norm (ev es_inc 16 == EAlloc 1 0 [vA]);
    next 16 (EAlloc 1 0 [vA]);
    colour_E ();
    alloc_E st12 M.White;
    step_alloc (ci 16) d16 1 0 [vA] st13

let h18 () : Lemma (requires ff_room) (ensures holds (ci 18) d18)
  = h17 (); holds_brep (ci 17) d17; len_inc (); xs (); stores_inc ();
    assert_norm (ev es_inc 17 == EWrite (M.Major xD) 0 vK2);
    next 17 (EWrite (M.Major xD) 0 vK2);
    blk st13 xD;
    set_d0 st13 vK2;
    OK.d0_ok st13 vK2;
    step_write (ci 17) d17 xD 0 vK2 st14

let h19 () : Lemma (requires ff_room) (ensures holds (ci 19) d18)
  = h18 (); len_inc ();
    assert_norm (ev es_inc 18 == EMinor);
    next 18 EMinor;
    step_minor0 (ci 18) d18

let h20 () : Lemma (requires ff_room) (ensures holds (ci 20) (d20 ()))
  = h19 (); len_inc (); SQ.stores ();
    assert_norm (ev es_inc 19 == EYoungAlloc 1 0 [vK2]);
    next 19 (EYoungAlloc 1 0 [vK2]);
    YW.yal1 vK2;
    step_yalloc (ci 19) d18 1 0 [vK2]

let h21 () : Lemma (requires ff_room) (ensures holds (ci 21) (d21 ()))
  = h20 (); len_inc (); SQ.stores ();
    assert_norm (ev es_inc 20 == EYoungAlloc 1 0 [iw]);
    next 20 (EYoungAlloc 1 0 [iw]);
    YW.yal2 vK2 iw;
    step_yalloc (ci 20) (d20 ()) 1 0 [iw]

let h22 () : Lemma (requires ff_room) (ensures holds (ci 22) (d22 ()))
  = h21 (); len_inc ();
    assert_norm (ev es_inc 21 == ERoots [vA; vE; y1; y2]);
    next 21 (ERoots [vA; vE; y1; y2]);
    step_roots (ci 21) (d21 ()) [vA; vE; y1; y2]

let h23 () : Lemma (requires ff_room) (ensures holds (ci 23) (d23 ()))
  = h22 (); len_inc (); xs ();
    assert_norm (ev es_inc 22 == ESweep);
    next 22 ESweep;
    blk st14 xD;
    recol_eq st14 xD M.White;
    recol_D st14 M.White;
    step_sweep_black (ci 22) (d22 ()) xD st15

let h24 () : Lemma (requires ff_room) (ensures holds (ci 24) (d24 ()))
  = h23 (); len_inc (); xs ();
    assert_norm (ev es_inc 23 == ESweep);
    next 23 ESweep;
    blk st15 xK;
    recol_eq st15 xK M.White;
    recol_K st15 M.White;
    step_sweep_black (ci 23) (d23 ()) xK st16

let h25 () : Lemma (requires ff_room) (ensures holds (ci 25) (d25 ()))
  = h24 (); holds_brep (ci 24) (d24 ()); len_inc (); xs ();
    assert_norm (ev es_inc 24 == ESweep);
    next 24 ESweep;
    blk st16 xC;
    free_C st16;
    OK.freed_ok st16;
    step_sweep_white (ci 24) (d24 ()) xC st17

let h26 () : Lemma (requires ff_room) (ensures holds (ci 26) (d26 ()))
  = h25 (); len_inc (); xs ();
    assert_norm (ev es_inc 25 == ESweep);
    next 25 ESweep;
    blk st17 xB;
    recol_eq st17 xB M.White;
    recol_B st17 M.White;
    step_sweep_black (ci 25) (d25 ()) xB st18

let h27 () : Lemma (requires ff_room) (ensures holds (ci 27) (d27 ()))
  = h26 (); len_inc (); xs ();
    assert_norm (ev es_inc 26 == ESweep);
    next 26 ESweep;
    blk st18 xA;
    recol_eq st18 xA M.White;
    recol_A st18 M.White;
    step_sweep_black (ci 26) (d26 ()) xA st19

let h28 () : Lemma (requires ff_room) (ensures holds (ci 28) (d28 ()))
  = h27 (); len_inc ();
    assert_norm (ev es_inc 27 == EEnd);
    next 27 EEnd;
    step_end (ci 27) (d27 ())

let h29 () : Lemma (requires ff_room) (ensures holds (ci 29) (d29 ()))
  = h28 (); len_inc (); xs ();
    assert_norm (ev es_inc 28 == ERead (M.Major xA) 1);
    next 28 (ERead (M.Major xA) 1);
    blk st19 xA;
    step_read (ci 28) (d28 ()) xA 1
#pop-options

/// ---------------------------------------------------------------------------
/// Every event is allowed
/// ---------------------------------------------------------------------------

/// The incremental style allows whatever the sequential one does.
let seq_inc (x: config fc) (e: event)
  : Lemma (requires ok_at Sequential x e) (ensures ok_at Incremental x e)
  = ()

let same_ev (i: nat)
  : Lemma (requires i < 7 /\ L.length es_inc == 30 /\ L.length SQ.es_seq == 25)
          (ensures ev es_inc i == ev SQ.es_seq i)
  = match i with
    | 0 -> assert_norm (ev es_inc 0 == ev SQ.es_seq 0)
    | 1 -> assert_norm (ev es_inc 1 == ev SQ.es_seq 1)
    | 2 -> assert_norm (ev es_inc 2 == ev SQ.es_seq 2)
    | 3 -> assert_norm (ev es_inc 3 == ev SQ.es_seq 3)
    | 4 -> assert_norm (ev es_inc 4 == ev SQ.es_seq 4)
    | 5 -> assert_norm (ev es_inc 5 == ev SQ.es_seq 5)
    | 6 -> assert_norm (ev es_inc 6 == ev SQ.es_seq 6)

let ok_prefix (i: nat)
  : Lemma (requires ff_room /\ i < 7 /\ L.length es_inc == 30) (ensures ok_at Incremental (ci i) (ev es_inc i))
  = SQ.len_seq ();
    SQ.seq_ok i;
    same_prefix i;
    same_ev i;
    seq_inc (ci i) (ev es_inc i)

#push-options "--fuel 6"
let mems_inc (_: unit)
  : Lemma (L.memP vA [vA] /\ L.memP vA [vD; vA] /\ L.memP vD [vD; vA] /\
           L.memP vA [vE; vD; vA] /\ L.memP vD [vE; vD; vA] /\ L.memP vE [vE; vD; vA] /\
           L.memP vA [y1; vE; vD; vA] /\ L.memP vA [y2; y1; vE; vD; vA] /\ L.memP vE [y2; y1; vE; vD; vA] /\
           L.memP y1 [y2; y1; vE; vD; vA] /\ L.memP y2 [y2; y1; vE; vD; vA] /\
           L.memP vA [vA; vE; y1; y2] /\ L.memP vA [vK2; vA; vE; y1; y2] /\
           L.memP y1 [vK2; vA; vE; y1; y2] /\ L.memP y2 [vK2; vA; vE; y1; y2])
  = ()

let roots4 (w: M.world) (a b c d: M.value)
  : Lemma (requires value_ok w a /\ value_ok w b /\ value_ok w c /\ value_ok w d)
          (ensures forall (u: M.value). L.memP u [a; b; c; d] ==> value_ok w u)
  = ()
#pop-options

#push-options "--z3rlimit 40"
let ok7 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 7) (ev es_inc 7))
  = h7 ();
    assert_norm (ev es_inc 7 == EStart);
    ok_start Incremental (ci 7) d7

let ok8 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 8) (ev es_inc 8))
  = h8 (); SQ.stores (); mems_inc (); xs ();
    assert_norm (ev es_inc 8 == EAlloc 1 0 [vB]);
    let w = wd d8 in
    blk st7 xA; blk st7 xB;
    reach_root w xA xA;
    reach_edge w xA 0 xB xB;
    vmaj_ok w xB xB;
    SQ.fill_one w 0 vB;
    ok_alloc Incremental (ci 8) d8 1 0 [vB]

let ok9 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 9) (ev es_inc 9))
  = h9 (); stores_inc (); mems_inc (); xs ();
    assert_norm (ev es_inc 9 == EWrite (M.Major xA) 0 i1);
    blk st8 xA;
    reach_root (wd d9) xA xA;
    ok_write Incremental (ci 9) d9 xA 0 i1

let ok10 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 10) (ev es_inc 10))
  = h10 ();
    assert_norm (ev es_inc 10 == EMinor);
    ok_minor Incremental (ci 10) d10

let ok11 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 11) (ev es_inc 11))
  = h11 (); xs ();
    assert_norm (ev es_inc 11 == ESlice);
    blk st9 xB;
    ok_slice Incremental (ci 11) d10 xB

let ok12 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 12) (ev es_inc 12))
  = h12 (); xs ();
    assert_norm (ev es_inc 12 == ESlice);
    blk st10 xA;
    ok_slice Incremental (ci 12) d12 xA

let ok13 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 13) (ev es_inc 13))
  = h13 (); xs ();
    assert_norm (ev es_inc 13 == ESlice);
    blk st11 xK;
    ok_slice Incremental (ci 13) d13 xK

let ok14 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 14) (ev es_inc 14))
  = h14 (); xs ();
    assert_norm (ev es_inc 14 == EHandover);
    assert (T.no_grey (mk st12));
    ok_handover Incremental (ci 14) d14

let ok15 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 15) (ev es_inc 15))
  = h15 ();
    assert_norm (ev es_inc 15 == ESweep);
    ok_sweep Incremental (ci 15) d15 0

let ok16 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 16) (ev es_inc 16))
  = h16 (); stores_inc (); mems_inc (); xs ();
    assert_norm (ev es_inc 16 == EAlloc 1 0 [vA]);
    blk st12 xA;
    reach_root (wd d16) xA xA;
    vmaj_ok (wd d16) xA xA;
    SQ.fill_one (wd d16) 0 vA;
    ok_alloc Incremental (ci 16) d16 1 0 [vA]

let ok17 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 17) (ev es_inc 17))
  = h17 (); stores_inc (); mems_inc (); xs ();
    assert_norm (ev es_inc 17 == EWrite (M.Major xD) 0 vK2);
    blk st13 xD;
    reach_root (wd d17) xD xD;
    SQ.k_reach st13 [vE; vD; vA] ym0;
    ok_write Incremental (ci 17) d17 xD 0 vK2

let ok18 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 18) (ev es_inc 18))
  = h18 ();
    assert_norm (ev es_inc 18 == EMinor);
    ok_minor Incremental (ci 18) d18

let ok19 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 19) (ev es_inc 19))
  = h19 (); SQ.stores (); mems_inc ();
    assert_norm (ev es_inc 19 == EYoungAlloc 1 0 [vK2]);
    SQ.k_reach st14 [vE; vD; vA] ym0;
    SQ.fill_one (wd d18) 0 vK2;
    YW.yal1 vK2;
    ok_yalloc Incremental (ci 19) d18 1 0 [vK2]

let ok20 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 20) (ev es_inc 20))
  = h20 (); SQ.stores (); SQ.ints ();
    assert_norm (ev es_inc 20 == EYoungAlloc 1 0 [iw]);
    SQ.fill_ints (wd (d20 ())) 0 [iw];
    YW.yal2 vK2 iw;
    ok_yalloc Incremental (ci 20) (d20 ()) 1 0 [iw]

let ok21 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 21) (ev es_inc 21))
  = h21 (); stores_inc (); mems_inc (); xs ();
    assert_norm (ev es_inc 21 == ERoots [vA; vE; y1; y2]);
    let w = wd (d21 ()) in
    blk st14 xA; blk st14 xE;
    reach_root w xA xA;
    reach_root w xE xE;
    vmaj_ok w xA xA;
    vmaj_ok w xE xE;
    YW.yblocks vK2 iw;
    yreach_root w 0 0;
    yreach_root w 2 2;
    vyng_ok w 0 0;
    vyng_ok w 2 2;
    roots4 w vA vE y1 y2;
    ok_roots Incremental (ci 21) (d21 ()) [vA; vE; y1; y2]

let ok22 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 22) (ev es_inc 22))
  = h22 (); xs ();
    assert_norm (ev es_inc 22 == ESweep);
    ok_sweep Incremental (ci 22) (d22 ()) xD

let ok23 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 23) (ev es_inc 23))
  = h23 (); xs ();
    assert_norm (ev es_inc 23 == ESweep);
    ok_sweep Incremental (ci 23) (d23 ()) xK

let ok24 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 24) (ev es_inc 24))
  = h24 (); xs ();
    assert_norm (ev es_inc 24 == ESweep);
    ok_sweep Incremental (ci 24) (d24 ()) xC

let ok25 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 25) (ev es_inc 25))
  = h25 (); xs ();
    assert_norm (ev es_inc 25 == ESweep);
    ok_sweep Incremental (ci 25) (d25 ()) xB

let ok26 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 26) (ev es_inc 26))
  = h26 (); xs ();
    assert_norm (ev es_inc 26 == ESweep);
    ok_sweep Incremental (ci 26) (d26 ()) xA

let ok27 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 27) (ev es_inc 27))
  = h27 ();
    assert_norm (ev es_inc 27 == EEnd);
    ok_end Incremental (ci 27) (d27 ())

let ok28 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 28) (ev es_inc 28))
  = h28 (); mems_inc (); xs ();
    assert_norm (ev es_inc 28 == ERead (M.Major xA) 1);
    blk st19 xA;
    reach_root (wd (d28 ())) xA xA;
    ok_read Incremental (ci 28) (d28 ()) xA 1

let ok29 () : Lemma (requires ff_room /\ L.length es_inc == 30) (ensures ok_at Incremental (ci 29) (ev es_inc 29))
  = h29 ();
    assert_norm (ev es_inc 29 == EMinor);
    ok_minor Incremental (ci 29) (d29 ())
#pop-options

let inc_ok (i: nat)
  : Lemma (requires ff_room /\ i < 30) (ensures i < L.length es_inc /\ ok_at Incremental (ci i) (ev es_inc i))
  = len_inc ();
    if i < 7 then ok_prefix i
    else match i with
    | 7 -> ok7 () | 8 -> ok8 () | 9 -> ok9 () | 10 -> ok10 () | 11 -> ok11 () | 12 -> ok12 ()
    | 13 -> ok13 () | 14 -> ok14 () | 15 -> ok15 () | 16 -> ok16 () | 17 -> ok17 () | 18 -> ok18 ()
    | 19 -> ok19 () | 20 -> ok20 () | 21 -> ok21 () | 22 -> ok22 () | 23 -> ok23 () | 24 -> ok24 ()
    | 25 -> ok25 () | 26 -> ok26 () | 27 -> ok27 () | 28 -> ok28 () | 29 -> ok29 ()

/// **The incremental run is allowed.**
let inc_run_ok () : Lemma (requires ff_room) (ensures run_ok fc Incremental msize ywords es_inc)
  = len_inc ();
    let f (i: nat) : Lemma (i < L.length es_inc ==>
                            (let x = at fc msize ywords es_inc i in
                             let e = ev es_inc i in
                             enabled fc x e /\ style_ok Incremental x e /\ mutator_ok x e))
      = if i < 30 then inc_ok i in
    FStar.Classical.forall_intro f

/// **Every hypothesis of `gc_correct` and `gc_correct_local` holds of the
/// incremental run.**
let ff_vacuity_incremental ()
  : Lemma (requires ff_room)
          (ensures components_ok fc /\ run_ok fc Incremental msize ywords es_inc /\
                   run_hyps fc msize ywords es_inc)
  = FC.ff_components_ok ();
    inc_run_ok ();
    run_hyps_of_ok fc msize ywords es_inc

let inc_every_event () : Lemma (SQ.every_event es_inc) = assert_norm (SQ.every_event es_inc)

/// ---------------------------------------------------------------------------
/// Non-triviality
/// ---------------------------------------------------------------------------

#push-options "--fuel 2"
let start_w0 ()
  : Lemma (requires ff_room)
          (ensures (let w = wd d7 in
                    M.reachable w xA /\ M.reachable w xB /\ M.reachable w xK /\ ~(M.reachable w xC) /\
                    M.is_block w.M.maj xC /\ M.col_of w.M.maj xC == M.White /\ L.memP vA w.M.roots))
  = let w = wd d7 in
    xs ();
    blk st6 xA; blk st6 xB; blk st6 xC; res_k2 st6;
    reach_root w xA xA;
    reach_edge w xA 0 xB xB;
    reach_edge w xA 1 (xK + 2) xK;
    SS.roots_one (); SS.empty_ywords ();
    SS.c_unreachable st6 ym0 [vA]
#pop-options

/// **At the cycle's start: the root A, the reachable A, B and K (through A's
/// fields), and C, in use and unreachable.**
#push-options "--z3rlimit 40"
let inc_nontrivial ()
  : Lemma (requires ff_room)
          (ensures (let x = ci 7 in
                    let w = vw x in
                    L.memP vA w.M.roots /\ M.reachable w xA /\ M.reachable w xB /\ M.reachable w xK /\
                    T.in_use fc.a x.ast x.w.cmaj w.M.maj xC == true /\ ~(M.reachable w xC)))
  = h7 ();
    let x = ci 7 in
    let w0 = wd d7 in
    start_w0 ();
    views_wd x d7;
    holds_def x d7;
    reachable_wheq w0 (vw x) xA;
    reachable_wheq w0 (vw x) xB;
    reachable_wheq w0 (vw x) xK;
    reachable_wheq w0 (vw x) xC;
    assert ((cabs x.w.cmaj).M.hd xC == (mk st6).M.hd xC)
#pop-options

let dark_model ()
  : Lemma (requires ff_room)
          (ensures M.field (mk st8) xA 0 == vB /\ M.col_of (mk st8) xB == M.White /\ M.col_of (mk st9) xB == M.Grey)
  = xs ()

let heq_reads (h h': M.mheap) (o i x: nat)
  : Lemma (requires R.heq h h') (ensures M.field h o i == M.field h' o i /\ M.col_of h x == M.col_of h' x)
  = ()

/// **The barrier darkens**: the write at 9, while marking, overwrites A.0
/// (B, white) and B turns grey.
let inc_darkens ()
  : Lemma (requires ff_room /\ L.length es_inc == 30)
          (ensures ev es_inc 9 == EWrite (M.Major xA) 0 i1 /\ T.Marking? (ci 9).ph /\
                   M.field (mj (ci 9)) xA 0 == vB /\
                   M.col_of (mj (ci 9)) xB == M.White /\ M.col_of (mj (ci 10)) xB == M.Grey)
  = assert_norm (ev es_inc 9 == EWrite (M.Major xA) 0 i1);
    h9 (); h10 ();
    holds_def (ci 9) d9;
    mj_wd (ci 9) d9; mj_wd (ci 10) d10;
    dark_model ();
    heq_reads (mj (ci 9)) (mk st8) xA 0 xB;
    heq_reads (mj (ci 10)) (mk st9) xA 0 xB

/// The program runs while marking (8, 9) and while sweeping (16, 17, 19-21);
/// a minor collection runs in each phase (10, 18, 29).
let inc_interleaves ()
  : Lemma (requires ff_room /\ L.length es_inc == 30)
          (ensures T.Marking? (ci 8).ph /\ EAlloc? (ev es_inc 8) /\ T.Marking? (ci 9).ph /\ EWrite? (ev es_inc 9) /\
                   T.Sweeping? (ci 16).ph /\ EAlloc? (ev es_inc 16) /\ T.Sweeping? (ci 17).ph /\ EWrite? (ev es_inc 17) /\
                   T.Sweeping? (ci 19).ph /\ EYoungAlloc? (ev es_inc 19) /\ T.Sweeping? (ci 21).ph /\ ERoots? (ev es_inc 21) /\
                   T.Marking? (ci 10).ph /\ ev es_inc 10 == EMinor /\ T.Sweeping? (ci 18).ph /\ ev es_inc 18 == EMinor /\
                   T.Idle? (ci 29).ph /\ ev es_inc 29 == EMinor)
  = assert_norm (EAlloc? (ev es_inc 8) /\ EWrite? (ev es_inc 9) /\ EAlloc? (ev es_inc 16) /\ EWrite? (ev es_inc 17) /\
                 EYoungAlloc? (ev es_inc 19) /\ ERoots? (ev es_inc 21) /\ ev es_inc 10 == EMinor /\
                 ev es_inc 18 == EMinor /\ ev es_inc 29 == EMinor);
    h8 (); h9 (); h10 (); h16 (); h17 (); h18 (); h19 (); h21 (); h29 ();
    holds_def (ci 8) d8; holds_def (ci 9) d9; holds_def (ci 10) d10; holds_def (ci 16) d16;
    holds_def (ci 17) d17; holds_def (ci 18) d18; holds_def (ci 19) d18; holds_def (ci 21) (d21 ());
    holds_def (ci 29) (d29 ())

#push-options "--fuel 6"
let infix_w0 ()
  : Lemma (requires ff_room)
          (ensures (let w = wd (d29 ()) in
                    M.yreachable w 0 /\ M.yreachable w 2 /\
                    M.field w.M.yng 0 0 == vK2 /\ M.field w.M.yng 2 0 == iw /\
                    M.resolve w.M.maj (xK + 2) == Some xK))
  = let w = wd (d29 ()) in
    xs ();
    res_k2 st19;
    YW.yblocks vK2 iw;
    assert (L.memP y1 [vK2; vA; vE; y1; y2] /\ L.memP y2 [vK2; vA; vE; y1; y2]);
    yreach_root w 0 0;
    yreach_root w 2 2
#pop-options

/// **The last minor collection sees Y1 (an infix pointer into the old
/// closure K, in use) and Y2 (an integer that reads as an infix header),
/// both reachable from the roots.**
#push-options "--z3rlimit 40"
let inc_infix_cases ()
  : Lemma (requires ff_room /\ L.length es_inc == 30)
          (ensures (let x = ci 29 in
                    let w = vw x in
                    ev es_inc 29 == EMinor /\
                    M.yreachable w 0 /\ M.yreachable w 2 /\
                    M.field w.M.yng 0 0 == M.VPtr (M.Major (xK + 2)) /\
                    M.resolve w.M.maj (xK + 2) == Some xK /\ T.in_use fc.a x.ast x.w.cmaj w.M.maj xK == true /\
                    M.field w.M.yng 2 0 == M.infix_word 2 /\ Some? (M.infix_hdr (M.field w.M.yng 2 0))))
  = h29 ();
    assert_norm (ev es_inc 29 == EMinor);
    let x = ci 29 in
    let w0 = wd (d29 ()) in
    infix_w0 ();
    xs (); blk st19 xK;
    views_wd x (d29 ());
    holds_def x (d29 ());
    yreachable_wheq w0 (vw x) 0;
    yreachable_wheq w0 (vw x) 2;
    resolve_heq w0.M.maj (vw x).M.maj (xK + 2);
    assert_norm (M.infix_hdr (M.infix_word 2) == Some 2);
    assert ((cabs x.w.cmaj).M.hd xK == (mk st19).M.hd xK)
#pop-options
