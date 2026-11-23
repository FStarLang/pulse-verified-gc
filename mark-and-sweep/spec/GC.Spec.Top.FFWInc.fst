/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWInc - the first-fit collector's incremental witness run
/// ---------------------------------------------------------------------------
///
/// Design doc §14, §15.  A run of the first-fit collector (`FFComps.fc`), in
/// the incremental style, from the allocator's initial heap, under `ff_room`:
///   0-6   as the sequential run (GC.Spec.Top.FFWSeq): A, B, C, K allocated
///         and filled, A.0 := B, A.1 := an infix pointer into K, roots [A];
///   7     the cycle starts (A grey; A, B, K reachable, C unreachable);
///   8     while marking: D allocated, black, D.0 = B;
///   9     while marking: A.0 := 1, the barrier darkens B (white to grey);
///   10-11 while marking: Y1 (holding the infix pointer into K) and Y2 (holding
///         an integer that reads as an infix header) allocated young, roots;
///   12    a minor collection while marking: Y2 and Y1 promoted through
///         first-fit (P1, P2, black), the roots rewritten;
///   13-15 mark slices (B, A greying K, K);
///   16    hand-over;
///   17    a sweep step (the free block);
///   18    while sweeping: E allocated, white (behind the cursor), E.0 = A;
///   19    while sweeping: D.0 := the infix pointer into K;
///   20-21 Y1 and Y2 again (Y3, Y4), young;
///   22    a minor collection while sweeping: promoted (P3, P4, white: behind
///         the cursor), the roots rewritten;
///   23    the roots become [A; E];
///   24-30 sweep steps: P2, P1, D, K whitened; C freed; B, A whitened;
///   31    the cycle ends;
///   32    a read of A.1 (the infix pointer) into a root;
///   33    a minor collection while idle (empty nursery).
/// Every event is allowed (`inc_run_ok`); with the components' contracts every
/// hypothesis of `gc_correct` and `gc_correct_local` holds
/// (`ff_vacuity_incremental`).  At both promoting collections `minor_pre`
/// holds for every world representing the configuration (`minor_pre_12`,
/// `minor_pre_22`), and the result is computed (`promoted_12`, `promoted_22`).

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
module FM2 = GC.Spec.Top.FFWMinor2
module MK = GC.Spec.Top.FFWMark
module SS = GC.Spec.Top.FFWStart
module OK = GC.Spec.Top.FFWOk
module YW = GC.Spec.Top.FFWYoung
module SQ = GC.Spec.Top.FFWSeq
module BB = GC.Spec.Top.ByteBarrier
module FC = GC.Spec.Top.FFComps
module FMd = GC.Spec.Top.FFWModel
module F = GC.Spec.Top.PagesFwd

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
let vP1 : M.value = M.VPtr (M.Major xP1)
let vP2 : M.value = M.VPtr (M.Major xP2)
let vP3 : M.value = M.VPtr (M.Major xP3)
let vP4 : M.value = M.VPtr (M.Major xP4)
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
  EYoungAlloc 1 0 [vK2];                     (* 10: Y1 *)
  EYoungAlloc 1 0 [iw];                      (* 11: Y2 *)
  EMinor;                                    (* 12: while marking, promotes Y2, Y1 *)
  ESlice;                                    (* 13: B *)
  ESlice;                                    (* 14: A *)
  ESlice;                                    (* 15: K *)
  EHandover;                                 (* 16 *)
  ESweep;                                    (* 17: the free block *)
  EAlloc 1 0 [vA];                           (* 18: E, white *)
  EWrite (M.Major xD) 0 vK2;                 (* 19 *)
  EYoungAlloc 1 0 [vK2];                     (* 20: Y3 *)
  EYoungAlloc 1 0 [iw];                      (* 21: Y4 *)
  EMinor;                                    (* 22: while sweeping, promotes Y4, Y3 *)
  ERoots [vA; vE];                           (* 23 *)
  ESweep;                                    (* 24: P2 *)
  ESweep;                                    (* 25: P1 *)
  ESweep;                                    (* 26: D *)
  ESweep;                                    (* 27: K *)
  ESweep;                                    (* 28: C freed *)
  ESweep;                                    (* 29: B *)
  ESweep;                                    (* 30: A *)
  EEnd;                                      (* 31 *)
  ERead (M.Major xA) 1;                      (* 32: the infix pointer into a root *)
  EMinor                                     (* 33: while idle *)
]

let len_inc () : Lemma (L.length es_inc == 34) = assert_norm (L.length es_inc == 34)

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
let st10 = { st9 with f = sub msize 18; cp1 = Some M.Black; cp2 = Some M.Black }
let st11 = { st10 with cb = Some M.Black }
let st12 = { st11 with ca = Some M.Black; ck = Some M.Grey }
let st13 = { st12 with ck = Some M.Black }
let st14 = { st13 with f = sub msize 20; ce = Some M.White }
let st15 = { st14 with d0 = vK2 }
let st16 = { st15 with f = sub msize 24; cp3 = Some M.White; cp4 = Some M.White }
let st17 = { st16 with cp2 = Some M.White }
let st18 = { st17 with cp1 = Some M.White }
let st19 = { st18 with cd = Some M.White }
let st20 = { st19 with ck = Some M.White }
let st21 = { st20 with cc = Some M.Blue; c0 = st20.lk; lk = vC }
let st22 = { st21 with cb = Some M.White }
let st23 = { st22 with ca = Some M.White }

let ym0 = SQ.ym0
let dI (st: wst) (rs: list M.value) : dsc = { dph = T.Idle; dst = st; dys = FM0.ms0; dym = ym0; drt = rs }
let dM (st: wst) (rs: list M.value) : dsc = { dph = T.Marking; dst = st; dys = FM0.ms0; dym = ym0; drt = rs }
let dS (o: nat) (st: wst) (rs: list M.value) : dsc =
  { dph = T.Sweeping (FWS.cur o); dst = st; dys = FM0.ms0; dym = ym0; drt = rs }
let y1d (d: dsc) : GTot dsc = { d with dys = YW.ms1 vK2; dym = YW.ym1 vK2; drt = y1 :: d.drt }
let y2d (d: dsc) : GTot dsc = { d with dys = YW.ms2 vK2 iw; dym = YW.ym2 vK2 iw; drt = y2 :: y1 :: d.drt }

let rs13 : list M.value = [vP1; vP2; vD; vA]

let d7 = dI st6 [vA]
let d8 = dM st7 [vA]
let d9 = dM st8 [vD; vA]
let d10 = dM st9 [vD; vA]
let d11 () = y1d d10
let d12 () = y2d d10
let d13 = dM st10 rs13
let d14 = dM st11 rs13
let d15 = dM st12 rs13
let d16 = dM st13 rs13
let d17 = dS 0 st13 rs13
let d18 = dS xP2 st13 rs13
let d19 = dS xP2 st14 (vE :: rs13)
let d20 = dS xP2 st15 (vE :: rs13)
let d21 () = y1d d20
let d22 () = y2d d20
let d23 = dS xP2 st16 (vP3 :: vP4 :: vE :: rs13)
let d24 = dS xP2 st16 [vA; vE]
let d25 = dS xP1 st17 [vA; vE]
let d26 = dS xD st18 [vA; vE]
let d27 = dS xK st19 [vA; vE]
let d28 = dS xC st20 [vA; vE]
let d29 = dS xB st21 [vA; vE]
let d30 = dS xA st22 [vA; vE]
let d31 = dS msize st23 [vA; vE]
let d32 = dI st23 [vA; vE]
let d33 = dI st23 [vK2; vA; vE]

/// ---------------------------------------------------------------------------
/// Facts this run adds
/// ---------------------------------------------------------------------------

#push-options "--fuel 6"
let stores_inc (_: unit)
  : Lemma (requires ff_room)
          (ensures R.storable_all byte_rep [vA] /\ no_young [vA] == true /\ L.length [vA] == 1 /\
                   no_young [i1] == true /\ storable_w vK2 /\ storable_w i1 /\ storable_w iw /\ no_young [vK2] == true /\
                   R.storable_all byte_rep [vA; vE] /\ storable_w vE /\
                   no_young [vD; vA] == true /\ no_young (vE :: rs13) == true)
  = xs (); base_facts ();
    st_maj xA; st_maj xE; st_maj (xK + 2); st_yng 0; st_yng 2; SQ.stores ();
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

/// Behind the cursor at P2: white.
let colour_behind (o: nat)
  : Lemma (requires ff_room /\ o < xP2) (ensures T.colour_at ffk (T.Sweeping (FWS.cur xP2)) o == M.White)
  = xs (); FWS.cur_v xP2

/// The values the run's closed forms hold are no nursery address.
let hv_states (_: unit)
  : Lemma (requires ff_room)
          (ensures FM2.st_hv st9 /\ FM2.st_hv st15 /\ FM2.hv vK2 /\ FM2.hv iw)
  = assert_norm (FM2.hv iw)

let low10 () : Lemma (requires ff_room)
  (ensures forall (o: nat). o < xB /\ M.is_block (mk st10) o ==> M.col_of (mk st10) o <> M.Grey) = xs ()
let low11 () : Lemma (requires ff_room)
  (ensures forall (o: nat). o < xA /\ M.is_block (mk st11) o ==> M.col_of (mk st11) o <> M.Grey) = xs ()
let low12 () : Lemma (requires ff_room)
  (ensures forall (o: nat). o < xK /\ M.is_block (mk st12) o ==> M.col_of (mk st12) o <> M.Grey) = xs ()

/// The promotions, in closed form.
let promo12 (_: unit)
  : Lemma (requires ff_room)
          (ensures st9.f == sub msize 14 /\
                   R.heq (FM2.m2 T.Marking vK2 iw (mk st9) st9.f) (mk st10))
  = xs ();
    promo_M st9 M.Black M.Black

let promo22 (_: unit)
  : Lemma (requires ff_room)
          (ensures st15.f == sub msize 20 /\
                   R.heq (FM2.m2 (T.Sweeping (FWS.cur xP2)) vK2 iw (mk st15) st15.f) (mk st16))
  = xs ();
    colour_behind (msize - 21);
    colour_behind (msize - 23);
    promo_S st15 M.White M.White

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

let h11 () : Lemma (requires ff_room) (ensures holds (ci 11) (d11 ()))
  = h10 (); len_inc (); SQ.stores ();
    assert_norm (ev es_inc 10 == EYoungAlloc 1 0 [vK2]);
    next 10 (EYoungAlloc 1 0 [vK2]);
    YW.yal1 vK2;
    step_yalloc (ci 10) d10 1 0 [vK2]

let h12 () : Lemma (requires ff_room) (ensures holds (ci 12) (d12 ()))
  = h11 (); len_inc (); SQ.stores ();
    assert_norm (ev es_inc 11 == EYoungAlloc 1 0 [iw]);
    next 11 (EYoungAlloc 1 0 [iw]);
    YW.yal2 vK2 iw;
    step_yalloc (ci 11) (d11 ()) 1 0 [iw]

let h13 () : Lemma (requires ff_room) (ensures holds (ci 13) d13)
  = h12 (); len_inc (); xs (); stores_inc (); hv_states ();
    assert_norm (ev es_inc 12 == EMinor);
    next 12 EMinor;
    FM2.mk_hv st9;
    promo12 ();
    FM2.step_minor2 (ci 12) (d12 ()) vK2 iw [vD; vA] st10

let h14 () : Lemma (requires ff_room) (ensures holds (ci 14) d14)
  = h13 (); holds_brep (ci 13) d13; len_inc (); xs ();
    assert_norm (ev es_inc 13 == ESlice);
    next 13 ESlice;
    blk st10 xB;
    MK.scan_B st10;
    low10 ();
    MK.slice_B st10;
    OK.recol_ok st10 xB M.Black;
    recol_B st10 M.Black;
    step_slice (ci 13) d13 xB st11

let h15 () : Lemma (requires ff_room) (ensures holds (ci 15) d15)
  = h14 (); holds_brep (ci 14) d14; len_inc (); xs ();
    assert_norm (ev es_inc 14 == ESlice);
    next 14 ESlice;
    blk st11 xA; blk st11 xB; res_k2 st11;
    MK.scan_A st11;
    low11 ();
    MK.slice_A st11;
    OK.recol_ok st11 xA M.Black;
    OK.recol_ok (recol st11 xA M.Black) xK M.Grey;
    recol_A st11 M.Black; recol_K ({ st11 with ca = Some M.Black }) M.Grey;
    step_slice (ci 14) d14 xA st12

let h16 () : Lemma (requires ff_room) (ensures holds (ci 16) d16)
  = h15 (); holds_brep (ci 15) d15; len_inc (); xs ();
    assert_norm (ev es_inc 15 == ESlice);
    next 15 ESlice;
    blk st12 xK;
    MK.scan_K st12;
    low12 ();
    MK.slice_K st12;
    OK.recol_ok st12 xK M.Black;
    recol_K st12 M.Black;
    step_slice (ci 15) d15 xK st13

let h17 () : Lemma (requires ff_room) (ensures holds (ci 17) d17)
  = h16 (); len_inc ();
    assert_norm (ev es_inc 16 == EHandover);
    next 16 EHandover;
    step_handover (ci 16) d16

let h18 () : Lemma (requires ff_room) (ensures holds (ci 18) d18)
  = h17 (); len_inc (); xs ();
    assert_norm (ev es_inc 17 == ESweep);
    next 17 ESweep;
    step_sweep_head (ci 17) d17

let h19 () : Lemma (requires ff_room) (ensures holds (ci 19) d19)
  = h18 (); len_inc (); xs (); stores_inc ();
    assert_norm (ev es_inc 18 == EAlloc 1 0 [vA]);
    next 18 (EAlloc 1 0 [vA]);
    colour_behind (msize - 19);
    alloc_E st13 M.White;
    step_alloc (ci 18) d18 1 0 [vA] st14

let h20 () : Lemma (requires ff_room) (ensures holds (ci 20) d20)
  = h19 (); holds_brep (ci 19) d19; len_inc (); xs (); stores_inc ();
    assert_norm (ev es_inc 19 == EWrite (M.Major xD) 0 vK2);
    next 19 (EWrite (M.Major xD) 0 vK2);
    blk st14 xD;
    set_d0 st14 vK2;
    OK.d0_ok st14 vK2;
    step_write (ci 19) d19 xD 0 vK2 st15

let h21 () : Lemma (requires ff_room) (ensures holds (ci 21) (d21 ()))
  = h20 (); len_inc (); SQ.stores ();
    assert_norm (ev es_inc 20 == EYoungAlloc 1 0 [vK2]);
    next 20 (EYoungAlloc 1 0 [vK2]);
    YW.yal1 vK2;
    step_yalloc (ci 20) d20 1 0 [vK2]

let h22 () : Lemma (requires ff_room) (ensures holds (ci 22) (d22 ()))
  = h21 (); len_inc (); SQ.stores ();
    assert_norm (ev es_inc 21 == EYoungAlloc 1 0 [iw]);
    next 21 (EYoungAlloc 1 0 [iw]);
    YW.yal2 vK2 iw;
    step_yalloc (ci 21) (d21 ()) 1 0 [iw]

let h23 () : Lemma (requires ff_room) (ensures holds (ci 23) d23)
  = h22 (); len_inc (); xs (); stores_inc (); hv_states ();
    assert_norm (ev es_inc 22 == EMinor);
    next 22 EMinor;
    FM2.mk_hv st15;
    promo22 ();
    FM2.step_minor2 (ci 22) (d22 ()) vK2 iw (vE :: rs13) st16

let h24 () : Lemma (requires ff_room) (ensures holds (ci 24) d24)
  = h23 (); len_inc ();
    assert_norm (ev es_inc 23 == ERoots [vA; vE]);
    next 23 (ERoots [vA; vE]);
    step_roots (ci 23) d23 [vA; vE]

let h25 () : Lemma (requires ff_room) (ensures holds (ci 25) d25)
  = h24 (); len_inc (); xs ();
    assert_norm (ev es_inc 24 == ESweep);
    next 24 ESweep;
    blk st16 xP2;
    recol_eq st16 xP2 M.White;
    recol_P2 st16 M.White;
    step_sweep_black (ci 24) d24 xP2 st17

let h26 () : Lemma (requires ff_room) (ensures holds (ci 26) d26)
  = h25 (); len_inc (); xs ();
    assert_norm (ev es_inc 25 == ESweep);
    next 25 ESweep;
    blk st17 xP1;
    recol_eq st17 xP1 M.White;
    recol_P1 st17 M.White;
    step_sweep_black (ci 25) d25 xP1 st18

let h27 () : Lemma (requires ff_room) (ensures holds (ci 27) d27)
  = h26 (); len_inc (); xs ();
    assert_norm (ev es_inc 26 == ESweep);
    next 26 ESweep;
    blk st18 xD;
    recol_eq st18 xD M.White;
    recol_D st18 M.White;
    step_sweep_black (ci 26) d26 xD st19

let h28 () : Lemma (requires ff_room) (ensures holds (ci 28) d28)
  = h27 (); len_inc (); xs ();
    assert_norm (ev es_inc 27 == ESweep);
    next 27 ESweep;
    blk st19 xK;
    recol_eq st19 xK M.White;
    recol_K st19 M.White;
    step_sweep_black (ci 27) d27 xK st20

let h29 () : Lemma (requires ff_room) (ensures holds (ci 29) d29)
  = h28 (); holds_brep (ci 28) d28; len_inc (); xs ();
    assert_norm (ev es_inc 28 == ESweep);
    next 28 ESweep;
    assert_norm (st20.cc == Some M.White);
    blk st20 xC;
    free_C st20;
    OK.freed_ok st20;
    step_sweep_white (ci 28) d28 xC st21

let h30 () : Lemma (requires ff_room) (ensures holds (ci 30) d30)
  = h29 (); len_inc (); xs ();
    assert_norm (ev es_inc 29 == ESweep);
    next 29 ESweep;
    blk st21 xB;
    recol_eq st21 xB M.White;
    recol_B st21 M.White;
    step_sweep_black (ci 29) d29 xB st22

let h31 () : Lemma (requires ff_room) (ensures holds (ci 31) d31)
  = h30 (); len_inc (); xs ();
    assert_norm (ev es_inc 30 == ESweep);
    next 30 ESweep;
    blk st22 xA;
    recol_eq st22 xA M.White;
    recol_A st22 M.White;
    step_sweep_black (ci 30) d30 xA st23

let h32 () : Lemma (requires ff_room) (ensures holds (ci 32) d32)
  = h31 (); len_inc ();
    assert_norm (ev es_inc 31 == EEnd);
    next 31 EEnd;
    step_end (ci 31) d31

let h33 () : Lemma (requires ff_room) (ensures holds (ci 33) d33)
  = h32 (); len_inc (); xs ();
    assert_norm (ev es_inc 32 == ERead (M.Major xA) 1);
    next 32 (ERead (M.Major xA) 1);
    blk st23 xA;
    assert_norm (st23.a1 == vK2 /\ Some? st23.ca);
    assert (M.field (mk st23) xA 1 == vK2);
    step_read (ci 32) d32 xA 1
#pop-options

/// ---------------------------------------------------------------------------
/// The allocator's invariant, event by event, up to both promotions
/// ---------------------------------------------------------------------------

module IV = GC.Spec.Top.FFWInv

let ivc (i: nat) : prop = IV.ivx (ci i)

#push-options "--fuel 4"
let snd_ints (x: config fc) (d: dsc) (vs: list M.value)
  : Lemma (requires L.for_all M.VInt? vs == true)
          (ensures forall (v: M.value). L.memP v vs ==> T.sound_value fc.a d.dph x.ast x.w.cmaj (mk d.dst) v)
  = let rec aux (l: list M.value) : Lemma (requires L.for_all M.VInt? l == true)
                                          (ensures forall (v: M.value). L.memP v l ==> M.VInt? v) (decreases l)
      = match l with [] -> () | _ :: tl -> aux tl in
    aux vs

let snd_one (x: config fc) (d: dsc) (v: M.value)
  : Lemma (requires T.sound_value fc.a d.dph x.ast x.w.cmaj (mk d.dst) v)
          (ensures forall (u: M.value). L.memP u [v] ==> T.sound_value fc.a d.dph x.ast x.w.cmaj (mk d.dst) u)
  = ()
#pop-options

/// A pointer to a block in use, not white while sweeping (read in `m`,
/// which agrees with the description's heap on that block).
#push-options "--z3rlimit 40"
let snd_ptr (x: config fc) (d: dsc) (m: M.mheap) (a: nat) (t: nat)
  : Lemma (requires holds x d /\ M.resolve m a == Some t /\ M.is_block m t /\ M.is_block (mk d.dst) t /\
                    M.col_of m t == M.col_of (mk d.dst) t /\ M.col_of (mk d.dst) t <> M.Blue /\
                    (T.Sweeping? d.dph ==> M.col_of (mk d.dst) t <> M.White))
          (ensures T.sound_value fc.a d.dph x.ast x.w.cmaj m (M.VPtr (M.Major a)))
  = IV.in_use_model x d t
#pop-options

let iv0 () : Lemma (requires ff_room) (ensures ivc 0)
  = IV.inv_init es_inc

#push-options "--z3rlimit 40"
let iv1 () : Lemma (requires ff_room) (ensures ivc 1)
  = iv0 (); same_prefix 0; same_prefix 1; SQ.h0 (); SQ.h1 (); SQ.len_seq (); xs (); SQ.stores (); SQ.ints ();
    assert_norm (ev SQ.es_seq 0 == EAlloc 2 0 [i1; i1]);
    SQ.next 0 (EAlloc 2 0 [i1; i1]);
    alloc_A st0 M.White;
    snd_ints (SQ.cs 0) (SQ.dI st0 []) [i1; i1];
    IV.inv_alloc (SQ.cs 0) (SQ.dI st0 []) SQ.d1 2 0 [i1; i1] SQ.st1

let iv2 () : Lemma (requires ff_room) (ensures ivc 2)
  = iv1 (); same_prefix 1; same_prefix 2; SQ.h1 (); SQ.h2 (); SQ.len_seq (); xs (); SQ.stores (); SQ.ints ();
    assert_norm (ev SQ.es_seq 1 == EAlloc 1 0 [i1]);
    SQ.next 1 (EAlloc 1 0 [i1]);
    alloc_B SQ.st1 M.White;
    snd_ints (SQ.cs 1) SQ.d1 [i1];
    IV.inv_alloc (SQ.cs 1) SQ.d1 SQ.d2 1 0 [i1] SQ.st2

let iv3 () : Lemma (requires ff_room) (ensures ivc 3)
  = iv2 (); same_prefix 2; same_prefix 3; SQ.h2 (); SQ.h3 (); SQ.len_seq (); xs (); SQ.stores ();
    assert_norm (ev SQ.es_seq 2 == EAlloc 1 0 [vB]);
    SQ.next 2 (EAlloc 1 0 [vB]);
    alloc_C SQ.st2 M.White vB;
    blk SQ.st2 xB;
    snd_ptr (SQ.cs 2) SQ.d2 (mk SQ.st2) xB xB;
    snd_one (SQ.cs 2) SQ.d2 vB;
    IV.inv_alloc (SQ.cs 2) SQ.d2 SQ.d3 1 0 [vB] SQ.st3

let iv4 () : Lemma (requires ff_room) (ensures ivc 4)
  = iv3 (); same_prefix 3; same_prefix 4; SQ.h3 (); SQ.h4 (); SQ.len_seq (); xs (); SQ.stores (); SQ.ints ();
    assert_norm (ev SQ.es_seq 3 == EAlloc 3 M.closure_tag [i1; iw; i1]);
    SQ.next 3 (EAlloc 3 M.closure_tag [i1; iw; i1]);
    alloc_K SQ.st3 M.White;
    snd_ints (SQ.cs 3) SQ.d3 [i1; iw; i1];
    IV.inv_alloc (SQ.cs 3) SQ.d3 SQ.d4 3 M.closure_tag [i1; iw; i1] SQ.st4
#pop-options

/// The writes' frames.
#push-options "--z3rlimit 40"
let rel5 () : Lemma (requires ff_room)
  (ensures T.inv_frame_rel fc.a T.Idle (SQ.cs 4).ast (SQ.cs 4).w.cmaj (mk SQ.st4) (mk SQ.st5))
  = SQ.h4 (); xs ();
    blk SQ.st5 xB; blk SQ.st4 xB;
    snd_ptr (SQ.cs 4) SQ.d4 (mk SQ.st5) xB xB;
    blk SQ.st4 xA; IV.in_use_model (SQ.cs 4) SQ.d4 xA;
    IV.rel_of (SQ.cs 4) SQ.d4 T.Idle (mk SQ.st5) (xA + 1) xA

let rel6 () : Lemma (requires ff_room)
  (ensures T.inv_frame_rel fc.a T.Idle (SQ.cs 5).ast (SQ.cs 5).w.cmaj (mk SQ.st5) (mk SQ.st6))
  = SQ.h5 (); xs ();
    blk SQ.st5 xK; blk SQ.st6 xK; res_k2 SQ.st6;
    snd_ptr (SQ.cs 5) SQ.d5 (mk SQ.st6) (xK + 2) xK;
    blk SQ.st5 xA; IV.in_use_model (SQ.cs 5) SQ.d5 xA;
    IV.rel_of (SQ.cs 5) SQ.d5 T.Idle (mk SQ.st6) (xA + 2) xA

let iv5 () : Lemma (requires ff_room) (ensures ivc 5)
  = iv4 (); same_prefix 4; same_prefix 5; SQ.h4 (); SQ.h5 (); SQ.len_seq ();
    assert_norm (ev SQ.es_seq 4 == EWrite (M.Major xA) 0 vB);
    SQ.next 4 (EWrite (M.Major xA) 0 vB);
    rel5 ();
    IV.inv_write (SQ.cs 4) SQ.d4 SQ.d5 xA 0 vB

let iv6 () : Lemma (requires ff_room) (ensures ivc 6)
  = iv5 (); same_prefix 5; same_prefix 6; SQ.h5 (); SQ.h6 (); SQ.len_seq ();
    assert_norm (ev SQ.es_seq 5 == EWrite (M.Major xA) 1 vK2);
    SQ.next 5 (EWrite (M.Major xA) 1 vK2);
    rel6 ();
    IV.inv_write (SQ.cs 5) SQ.d5 SQ.d6 xA 1 vK2

let iv7 () : Lemma (requires ff_room) (ensures ivc 7)
  = iv6 (); same_prefix 6; same_prefix 7; SQ.len_seq ();
    assert_norm (ev SQ.es_seq 6 == ERoots [vA]);
    SQ.next 6 (ERoots [vA]);
    IV.inv_same (SQ.cs 6) (ERoots [vA])

let rel8 () : Lemma (requires ff_room)
  (ensures T.inv_frame_rel fc.a T.Marking (ci 7).ast (ci 7).w.cmaj (mk st6) (mk st7))
  = h7 (); xs ();
    IV.rel_of (ci 7) d7 T.Marking (mk st7) 0 0

let iv8 () : Lemma (requires ff_room) (ensures ivc 8)
  = iv7 (); h7 (); h8 (); len_inc ();
    assert_norm (ev es_inc 7 == EStart);
    next 7 EStart;
    rel8 ();
    IV.inv_start (ci 7) d7 d8

let iv9 () : Lemma (requires ff_room) (ensures ivc 9)
  = iv8 (); h8 (); h9 (); len_inc (); xs (); SQ.stores ();
    assert_norm (ev es_inc 8 == EAlloc 1 0 [vB]);
    next 8 (EAlloc 1 0 [vB]);
    alloc_D st7 M.Black vB;
    blk st7 xB;
    snd_ptr (ci 8) d8 (mk st7) xB xB;
    snd_one (ci 8) d8 vB;
    IV.inv_alloc (ci 8) d8 d9 1 0 [vB] st8

let rel10 () : Lemma (requires ff_room)
  (ensures T.inv_frame_rel fc.a T.Marking (ci 9).ast (ci 9).w.cmaj (mk st8) (mk st9))
  = h9 (); xs ();
    blk st8 xA; blk st8 xB; IV.in_use_model (ci 9) d9 xA;
    IV.rel_of (ci 9) d9 T.Marking (mk st9) (xA + 1) xA

let iv10 () : Lemma (requires ff_room) (ensures ivc 10)
  = iv9 (); h9 (); h10 (); len_inc ();
    assert_norm (ev es_inc 9 == EWrite (M.Major xA) 0 i1);
    next 9 (EWrite (M.Major xA) 0 i1);
    rel10 ();
    IV.inv_write (ci 9) d9 d10 xA 0 i1

let iv12 () : Lemma (requires ff_room) (ensures ivc 12)
  = iv10 (); len_inc ();
    assert_norm (ev es_inc 10 == EYoungAlloc 1 0 [vK2] /\ ev es_inc 11 == EYoungAlloc 1 0 [iw]);
    next 10 (EYoungAlloc 1 0 [vK2]);
    IV.inv_same (ci 10) (EYoungAlloc 1 0 [vK2]);
    next 11 (EYoungAlloc 1 0 [iw]);
    IV.inv_same (ci 11) (EYoungAlloc 1 0 [iw])
#pop-options

/// ---------------------------------------------------------------------------
/// The minor collection while marking: its precondition and its result
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let young_sound_at (x: config fc) (d: dsc) (st: wst)
  : Lemma (requires holds x d /\ ff_room /\ d.dst == st /\ d.dym == YW.ym2 vK2 iw /\ Some? st.ck /\
                    (T.Sweeping? d.dph ==> st.ck =!= Some M.White) /\ st.ck =!= Some M.Blue)
          (ensures forall (y i b: nat). M.ptr_field d.dym y i /\ M.field d.dym y i == M.VPtr (M.Major b) ==>
                     T.sound_value fc.a x.ph x.ast x.w.cmaj (mk d.dst) (M.VPtr (M.Major b)))
  = hv_states ();
    FM2.ym2_ok vK2 iw;
    xs ();
    blk st xK; res_k2 st;
    holds_def x d;
    snd_ptr x d (mk st) (xK + 2) xK;
    assert_norm (iw =!= M.VPtr (M.Major 0) /\ (forall (b: nat). iw =!= M.VPtr (M.Major b)))
#pop-options

/// **`minor_pre` at 12**, for every world representing the configuration.
#push-options "--z3rlimit 40"
let minor_pre_12 ()
  : Lemma (requires ff_room)
          (ensures forall (w: M.world). views (ci 12) w ==>
                     T.minor_pre fc.a (ci 12).ph (ci 12).ast (ci 12).w.cmaj w)
  = h12 (); iv12 (); hv_states ();
    let x = ci 12 in
    let d = d12 () in
    FM2.mk_hv st9;
    FM2.ym2_ok vK2 iw;
    young_sound_at x d st9;
    views_wd x d;
    let one (w: M.world) : Lemma (requires views x w) (ensures T.minor_pre fc.a x.ph x.ast x.w.cmaj w)
      = IV.mpre x d w in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

#push-options "--fuel 3"
let fwd2_vals (f: nat) : Lemma (requires 3 <= f) (ensures F.fwd_of (FM2.cps2 f) 2 == Some (f - 1) /\ F.fwd_of (FM2.cps2 f) 0 == Some (f - 3)) = ()
#pop-options

/// The promotion's hypotheses, from a configuration's description.
let pre2_at (x: config fc) (d: dsc)
  : Lemma (requires holds x d /\ ff_room /\ d.dym == YW.ym2 vK2 iw /\ 7 <= d.dst.f /\
                    (mk d.dst).M.hd 0 == Some (GC.Spec.Top.FFWAlloc.free_hdr d.dst.f) /\
                    FM2.hv vK2 /\ FM2.hv iw /\ storable_w vK2 /\ storable_w iw)
          (ensures FM2.pre2 x.w.cyng vK2 iw x.w.cmaj (x.ast <: ffst).fp (mk d.dst) d.dst.f)
  = holds_def x d;
    FM2.pre2_def x.w.cyng vK2 iw x.w.cmaj (x.ast <: ffst).fp (mk d.dst) d.dst.f

/// **The collection at 12, computed**: `Done`; Y2 promoted once to P1 and Y1
/// to P2 through first-fit, both black (marking); P1's field is Y2's integer,
/// unchanged, P2's the infix pointer into K; the roots Y2, Y1 rewritten to
/// P1, P2; the heap otherwise unchanged.
#push-options "--z3rlimit 40"
let promoted_12 ()
  : Lemma (requires ff_room)
          (ensures (match fc.n.T.collect (ci 12).ph (ci 12).ast (ci 12).w with
                    | T.Done h' _ rs fwd ->
                      brepr (mk st10) h' /\ fwd 2 == Some xP1 /\ fwd 0 == Some xP2 /\
                      rs == [vP1; vP2; vD; vA] /\
                      M.col_of (mk st10) xP1 == M.Black /\ M.col_of (mk st10) xP2 == M.Black /\
                      M.field (mk st10) xP1 0 == M.infix_word 2 /\
                      M.field (mk st10) xP2 0 == M.VPtr (M.Major (xK + 2))
                    | T.OutOfRoom -> False))
  = h12 (); hv_states (); stores_inc (); xs ();
    let x = ci 12 in
    let d = d12 () in
    FM2.mk_hv st9;
    promo12 ();
    holds_def x d;
    FMd.okm_def (mk st9);
    fwd2_vals st9.f;
    assert ((mk st9).M.hd 0 == Some (GC.Spec.Top.FFWAlloc.free_hdr st9.f));
    pre2_at x d;
    FM2.pcollect_two x.ph x.ast x.w vK2 iw (mk st9) st9.f [vD; vA];
    FM2.roots_fwd x.w.cyng vK2 iw st9.f [vD; vA]
#pop-options

/// ---------------------------------------------------------------------------
/// The invariant on to the collection while sweeping
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let iv13 () : Lemma (requires ff_room) (ensures ivc 13)
  = iv12 (); h12 (); hv_states (); stores_inc (); len_inc ();
    let x = ci 12 in
    let d = d12 () in
    FM2.mk_hv st9;
    FM2.ym2_ok vK2 iw;
    young_sound_at x d st9;
    IV.mpre x d (wd d);
    FM2.done2 x d vK2 iw [vD; vA];
    assert_norm (ev es_inc 12 == EMinor);
    next 12 EMinor;
    IV.inv_minor x d

let rel_slice (i: nat) (d d': dsc)
  : Lemma (requires holds (ci i) d /\ d.dph == T.Marking /\
                    (mk d'.dst).M.size == (mk d.dst).M.size /\
                    (forall (y: nat). M.is_block (mk d'.dst) y == M.is_block (mk d.dst) y /\
                                      M.wz_of (mk d'.dst) y == M.wz_of (mk d.dst) y /\
                                      M.tag_of (mk d'.dst) y == M.tag_of (mk d.dst) y) /\
                    (forall (y: nat). M.col_of (mk d'.dst) y =!= M.col_of (mk d.dst) y ==>
                       M.is_block (mk d.dst) y /\ M.col_of (mk d.dst) y <> M.Blue /\ M.dark (M.col_of (mk d'.dst) y)) /\
                    (forall (w: nat). (mk d'.dst).M.body w == (mk d.dst).M.body w))
          (ensures T.inv_frame_rel fc.a d.dph (ci i).ast (ci i).w.cmaj (mk d.dst) (mk d'.dst))
  = IV.rel_of (ci i) d T.Marking (mk d'.dst) 0 0

let iv14 () : Lemma (requires ff_room) (ensures ivc 14)
  = iv13 (); h13 (); h14 (); len_inc (); xs ();
    assert_norm (ev es_inc 13 == ESlice);
    next 13 ESlice;
    rel_slice 13 d13 d14;
    IV.inv_slice (ci 13) d13 d14

let iv15 () : Lemma (requires ff_room) (ensures ivc 15)
  = iv14 (); h14 (); h15 (); len_inc (); xs ();
    assert_norm (ev es_inc 14 == ESlice);
    next 14 ESlice;
    rel_slice 14 d14 d15;
    IV.inv_slice (ci 14) d14 d15

let iv16 () : Lemma (requires ff_room) (ensures ivc 16)
  = iv15 (); h15 (); h16 (); len_inc (); xs ();
    assert_norm (ev es_inc 15 == ESlice);
    next 15 ESlice;
    rel_slice 15 d15 d16;
    IV.inv_slice (ci 15) d15 d16

/// At hand-over: no grey, and no dark block points to a white one.
let ng13 () : Lemma (requires ff_room) (ensures T.no_grey (mk st13)) = xs ()

#push-options "--z3rlimit 40"
let dc13_one (o i a t: nat)
  : Lemma (requires ff_room /\ M.is_block (mk st13) o /\ M.dark (M.col_of (mk st13) o) /\ M.ptr_field (mk st13) o i /\
                    M.field (mk st13) o i == M.VPtr (M.Major a) /\ M.resolve (mk st13) a == Some t)
          (ensures M.col_of (mk st13) t =!= M.White)
  = xs ();
    blk st13 xB; res_k2 st13;
    assert_norm (M.infix_word 2 == M.VInt 2297)
#pop-options

let dc13 () : Lemma (requires ff_room) (ensures T.dark_closed (mk st13))
  = FStar.Classical.forall_intro_4 (fun o i a t -> FStar.Classical.move_requires (dc13_one o i a) t)

let iv17 () : Lemma (requires ff_room) (ensures ivc 17)
  = iv16 (); h16 (); len_inc ();
    assert_norm (ev es_inc 16 == EHandover);
    next 16 EHandover;
    ng13 (); dc13 ();
    IV.inv_handover (ci 16) d16

let iv18 () : Lemma (requires ff_room) (ensures ivc 18)
  = iv17 (); h17 (); len_inc (); xs ();
    assert_norm (ev es_inc 17 == ESweep);
    next 17 ESweep;
    ng13 ();
    not_done 0;
    IV.inv_sweep (ci 17) d17 (FWS.cur 0)

let iv19 () : Lemma (requires ff_room) (ensures ivc 19)
  = iv18 (); h18 (); h19 (); len_inc (); xs (); stores_inc ();
    assert_norm (ev es_inc 18 == EAlloc 1 0 [vA]);
    next 18 (EAlloc 1 0 [vA]);
    colour_behind (msize - 19);
    alloc_E st13 M.White;
    blk st13 xA;
    snd_ptr (ci 18) d18 (mk st13) xA xA;
    snd_one (ci 18) d18 vA;
    IV.inv_alloc (ci 18) d18 d19 1 0 [vA] st14

let rel20 () : Lemma (requires ff_room)
  (ensures T.inv_frame_rel fc.a (T.Sweeping (FWS.cur xP2)) (ci 19).ast (ci 19).w.cmaj (mk st14) (mk st15))
  = h19 (); xs ();
    holds_def (ci 19) d19;
    blk st15 xK; blk st14 xK; res_k2 st15;
    snd_ptr (ci 19) d19 (mk st15) (xK + 2) xK;
    IV.in_use_model (ci 19) d19 xD;
    FWS.cur_v xP2;
    IV.rel_of (ci 19) d19 (T.Sweeping (FWS.cur xP2)) (mk st15) (xD + 1) xD

let iv20 () : Lemma (requires ff_room) (ensures ivc 20)
  = iv19 (); h19 (); h20 (); len_inc ();
    assert_norm (ev es_inc 19 == EWrite (M.Major xD) 0 vK2);
    next 19 (EWrite (M.Major xD) 0 vK2);
    rel20 ();
    IV.inv_write (ci 19) d19 d20 xD 0 vK2

let iv22 () : Lemma (requires ff_room) (ensures ivc 22)
  = iv20 (); len_inc ();
    assert_norm (ev es_inc 20 == EYoungAlloc 1 0 [vK2] /\ ev es_inc 21 == EYoungAlloc 1 0 [iw]);
    next 20 (EYoungAlloc 1 0 [vK2]);
    IV.inv_same (ci 20) (EYoungAlloc 1 0 [vK2]);
    next 21 (EYoungAlloc 1 0 [iw]);
    IV.inv_same (ci 21) (EYoungAlloc 1 0 [iw])

/// **`minor_pre` at 22**, while sweeping, for every world representing the
/// configuration.
let minor_pre_22 ()
  : Lemma (requires ff_room)
          (ensures forall (w: M.world). views (ci 22) w ==>
                     T.minor_pre fc.a (ci 22).ph (ci 22).ast (ci 22).w.cmaj w)
  = h22 (); iv22 (); hv_states ();
    let x = ci 22 in
    let d = d22 () in
    FM2.mk_hv st15;
    FM2.ym2_ok vK2 iw;
    young_sound_at x d st15;
    views_wd x d;
    let one (w: M.world) : Lemma (requires views x w) (ensures T.minor_pre fc.a x.ph x.ast x.w.cmaj w)
      = IV.mpre x d w in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// The copies at 22, read off the closed form.
let reads16 (_: unit)
  : Lemma (requires ff_room)
          (ensures M.col_of (mk st16) xP3 == M.White /\ M.col_of (mk st16) xP4 == M.White /\
                   M.field (mk st16) xP3 0 == M.infix_word 2 /\
                   M.field (mk st16) xP4 0 == M.VPtr (M.Major (xK + 2)))
  = xs ();
    assert_norm (st16.cp3 == Some M.White /\ st16.cp4 == Some M.White)

/// **The collection at 22, computed**: Y4 (Y2's twin) to P3 and Y3 to P4,
/// both white (behind the sweep's cursor), the fields copied, the roots
/// rewritten.
let promoted_22 ()
  : Lemma (requires ff_room)
          (ensures (match fc.n.T.collect (ci 22).ph (ci 22).ast (ci 22).w with
                    | T.Done h' _ rs fwd ->
                      brepr (mk st16) h' /\ fwd 2 == Some xP3 /\ fwd 0 == Some xP4 /\
                      rs == vP3 :: vP4 :: vE :: rs13 /\
                      M.col_of (mk st16) xP3 == M.White /\ M.col_of (mk st16) xP4 == M.White /\
                      M.field (mk st16) xP3 0 == M.infix_word 2 /\
                      M.field (mk st16) xP4 0 == M.VPtr (M.Major (xK + 2))
                    | T.OutOfRoom -> False))
  = h22 (); hv_states (); stores_inc (); xs ();
    let x = ci 22 in
    let d = d22 () in
    FM2.mk_hv st15;
    promo22 ();
    holds_def x d;
    FMd.okm_def (mk st15);
    fwd2_vals st15.f;
    assert ((mk st15).M.hd 0 == Some (GC.Spec.Top.FFWAlloc.free_hdr st15.f));
    pre2_at x d;
    FM2.pcollect_two x.ph x.ast x.w vK2 iw (mk st15) st15.f (vE :: rs13);
    FM2.roots_fwd x.w.cyng vK2 iw st15.f (vE :: rs13);
    reads16 ()
#pop-options

/// ---------------------------------------------------------------------------
/// Every event is allowed
/// ---------------------------------------------------------------------------

let seq_inc (x: config fc) (e: event)
  : Lemma (requires ok_at Sequential x e) (ensures ok_at Incremental x e)
  = ()

let same_ev (i: nat)
  : Lemma (requires i < 7 /\ L.length es_inc == 34 /\ L.length SQ.es_seq == 25)
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
  : Lemma (requires ff_room /\ i < 7 /\ L.length es_inc == 34) (ensures ok_at Incremental (ci i) (ev es_inc i))
  = SQ.len_seq ();
    SQ.seq_ok i;
    same_prefix i;
    same_ev i;
    seq_inc (ci i) (ev es_inc i)

#push-options "--fuel 9"
let mems_inc (_: unit)
  : Lemma (L.memP vA [vA] /\ L.memP vA [vD; vA] /\ L.memP vD [vD; vA] /\
           L.memP vA (vE :: rs13) /\ L.memP vD (vE :: rs13) /\ L.memP vA rs13 /\
           L.memP vA (vP3 :: vP4 :: vE :: rs13) /\ L.memP vE (vP3 :: vP4 :: vE :: rs13) /\
           L.memP vA [vA; vE] /\ L.memP vA [y1; vD; vA] /\ L.memP vA (y1 :: vE :: rs13))
  = ()
#pop-options

let ln = L.length es_inc

#push-options "--z3rlimit 40"
let ok7 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 7) (ev es_inc 7))
  = h7 (); assert_norm (ev es_inc 7 == EStart); ok_start Incremental (ci 7) d7

let ok8 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 8) (ev es_inc 8))
  = h8 (); SQ.stores (); mems_inc (); xs ();
    assert_norm (ev es_inc 8 == EAlloc 1 0 [vB]);
    let w = wd d8 in
    blk st7 xA; blk st7 xB;
    reach_root w xA xA;
    reach_edge w xA 0 xB xB;
    vmaj_ok w xB xB;
    SQ.fill_one w 0 vB;
    ok_alloc Incremental (ci 8) d8 1 0 [vB]

let ok9 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 9) (ev es_inc 9))
  = h9 (); stores_inc (); mems_inc (); xs ();
    assert_norm (ev es_inc 9 == EWrite (M.Major xA) 0 i1);
    blk st8 xA;
    reach_root (wd d9) xA xA;
    ok_write Incremental (ci 9) d9 xA 0 i1

let ok10 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 10) (ev es_inc 10))
  = h10 (); SQ.stores (); mems_inc ();
    assert_norm (ev es_inc 10 == EYoungAlloc 1 0 [vK2]);
    SQ.k_reach st9 [vD; vA] ym0;
    SQ.fill_one (wd d10) 0 vK2;
    YW.yal1 vK2;
    ok_yalloc Incremental (ci 10) d10 1 0 [vK2]

let ok11 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 11) (ev es_inc 11))
  = h11 (); SQ.stores (); SQ.ints ();
    assert_norm (ev es_inc 11 == EYoungAlloc 1 0 [iw]);
    SQ.fill_ints (wd (d11 ())) 0 [iw];
    YW.yal2 vK2 iw;
    ok_yalloc Incremental (ci 11) (d11 ()) 1 0 [iw]

let ok12 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 12) (ev es_inc 12))
  = h12 (); assert_norm (ev es_inc 12 == EMinor); ok_minor Incremental (ci 12) (d12 ())

let ok13 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 13) (ev es_inc 13))
  = h13 (); xs (); assert_norm (ev es_inc 13 == ESlice); blk st10 xB; ok_slice Incremental (ci 13) d13 xB

let ok14 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 14) (ev es_inc 14))
  = h14 (); xs (); assert_norm (ev es_inc 14 == ESlice); blk st11 xA; ok_slice Incremental (ci 14) d14 xA

let ok15 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 15) (ev es_inc 15))
  = h15 (); xs (); assert_norm (ev es_inc 15 == ESlice); blk st12 xK; ok_slice Incremental (ci 15) d15 xK

let ok16 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 16) (ev es_inc 16))
  = h16 (); ng13 (); assert_norm (ev es_inc 16 == EHandover); ok_handover Incremental (ci 16) d16

let ok17 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 17) (ev es_inc 17))
  = h17 (); assert_norm (ev es_inc 17 == ESweep); ok_sweep Incremental (ci 17) d17 0

let ok18 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 18) (ev es_inc 18))
  = h18 (); stores_inc (); mems_inc (); xs ();
    assert_norm (ev es_inc 18 == EAlloc 1 0 [vA]);
    blk st13 xA;
    reach_root (wd d18) xA xA;
    vmaj_ok (wd d18) xA xA;
    SQ.fill_one (wd d18) 0 vA;
    ok_alloc Incremental (ci 18) d18 1 0 [vA]

let ok19 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 19) (ev es_inc 19))
  = h19 (); stores_inc (); mems_inc (); xs ();
    assert_norm (ev es_inc 19 == EWrite (M.Major xD) 0 vK2);
    blk st14 xD;
    reach_root (wd d19) xD xD;
    SQ.k_reach st14 (vE :: rs13) ym0;
    ok_write Incremental (ci 19) d19 xD 0 vK2

let ok20 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 20) (ev es_inc 20))
  = h20 (); SQ.stores (); mems_inc ();
    assert_norm (ev es_inc 20 == EYoungAlloc 1 0 [vK2]);
    SQ.k_reach st15 (vE :: rs13) ym0;
    SQ.fill_one (wd d20) 0 vK2;
    YW.yal1 vK2;
    ok_yalloc Incremental (ci 20) d20 1 0 [vK2]

let ok21 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 21) (ev es_inc 21))
  = h21 (); SQ.stores (); SQ.ints ();
    assert_norm (ev es_inc 21 == EYoungAlloc 1 0 [iw]);
    SQ.fill_ints (wd (d21 ())) 0 [iw];
    YW.yal2 vK2 iw;
    ok_yalloc Incremental (ci 21) (d21 ()) 1 0 [iw]

let ok22 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 22) (ev es_inc 22))
  = h22 (); assert_norm (ev es_inc 22 == EMinor); ok_minor Incremental (ci 22) (d22 ())

#push-options "--fuel 3"
let roots2 (w: M.world) (a b: M.value)
  : Lemma (requires value_ok w a /\ value_ok w b) (ensures forall (u: M.value). L.memP u [a; b] ==> value_ok w u)
  = ()
#pop-options

let ok23 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 23) (ev es_inc 23))
  = h23 (); stores_inc (); mems_inc (); xs ();
    assert_norm (ev es_inc 23 == ERoots [vA; vE]);
    let w = wd d23 in
    blk st16 xA; blk st16 xE;
    reach_root w xA xA; reach_root w xE xE;
    vmaj_ok w xA xA; vmaj_ok w xE xE;
    roots2 w vA vE;
    ok_roots Incremental (ci 23) d23 [vA; vE]

let ok24 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 24) (ev es_inc 24))
  = h24 (); xs (); assert_norm (ev es_inc 24 == ESweep); ok_sweep Incremental (ci 24) d24 xP2
let ok25 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 25) (ev es_inc 25))
  = h25 (); xs (); assert_norm (ev es_inc 25 == ESweep); ok_sweep Incremental (ci 25) d25 xP1
let ok26 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 26) (ev es_inc 26))
  = h26 (); xs (); assert_norm (ev es_inc 26 == ESweep); ok_sweep Incremental (ci 26) d26 xD
let ok27 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 27) (ev es_inc 27))
  = h27 (); xs (); assert_norm (ev es_inc 27 == ESweep); ok_sweep Incremental (ci 27) d27 xK
let ok28 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 28) (ev es_inc 28))
  = h28 (); xs (); assert_norm (ev es_inc 28 == ESweep); ok_sweep Incremental (ci 28) d28 xC
let ok29 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 29) (ev es_inc 29))
  = h29 (); xs (); assert_norm (ev es_inc 29 == ESweep); ok_sweep Incremental (ci 29) d29 xB
let ok30 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 30) (ev es_inc 30))
  = h30 (); xs (); assert_norm (ev es_inc 30 == ESweep); ok_sweep Incremental (ci 30) d30 xA
let ok31 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 31) (ev es_inc 31))
  = h31 (); assert_norm (ev es_inc 31 == EEnd); ok_end Incremental (ci 31) d31

let ok32 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 32) (ev es_inc 32))
  = h32 (); mems_inc (); xs ();
    assert_norm (ev es_inc 32 == ERead (M.Major xA) 1);
    blk st23 xA;
    reach_root (wd d32) xA xA;
    ok_read Incremental (ci 32) d32 xA 1

let ok33 () : Lemma (requires ff_room /\ ln == 34) (ensures ok_at Incremental (ci 33) (ev es_inc 33))
  = h33 (); assert_norm (ev es_inc 33 == EMinor); ok_minor Incremental (ci 33) d33
#pop-options

let inc_ok (i: nat)
  : Lemma (requires ff_room /\ i < 34) (ensures i < L.length es_inc /\ ok_at Incremental (ci i) (ev es_inc i))
  = len_inc ();
    if i < 7 then ok_prefix i
    else match i with
    | 7 -> ok7 () | 8 -> ok8 () | 9 -> ok9 () | 10 -> ok10 () | 11 -> ok11 () | 12 -> ok12 ()
    | 13 -> ok13 () | 14 -> ok14 () | 15 -> ok15 () | 16 -> ok16 () | 17 -> ok17 () | 18 -> ok18 ()
    | 19 -> ok19 () | 20 -> ok20 () | 21 -> ok21 () | 22 -> ok22 () | 23 -> ok23 () | 24 -> ok24 ()
    | 25 -> ok25 () | 26 -> ok26 () | 27 -> ok27 () | 28 -> ok28 () | 29 -> ok29 () | 30 -> ok30 ()
    | 31 -> ok31 () | 32 -> ok32 () | 33 -> ok33 ()

/// **The incremental run is allowed.**
let inc_run_ok () : Lemma (requires ff_room) (ensures run_ok fc Incremental msize ywords es_inc)
  = len_inc ();
    let f (i: nat) : Lemma (i < L.length es_inc ==>
                            (let x = at fc msize ywords es_inc i in
                             let e = ev es_inc i in
                             enabled fc x e /\ style_ok Incremental x e /\ mutator_ok x e))
      = if i < 34 then inc_ok i in
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

/// **At the cycle's start: the root A, the reachable A, B and K, and C, in
/// use and unreachable.**
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
/// (B, white) and B is grey after it.
let inc_darkens ()
  : Lemma (requires ff_room /\ L.length es_inc == 34)
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

/// The program runs while marking (8-11) and while sweeping (18-21, 23); a
/// minor collection runs in each phase (12, 22, 33).
let inc_interleaves ()
  : Lemma (requires ff_room /\ L.length es_inc == 34)
          (ensures T.Marking? (ci 8).ph /\ EAlloc? (ev es_inc 8) /\ T.Marking? (ci 9).ph /\ EWrite? (ev es_inc 9) /\
                   T.Marking? (ci 10).ph /\ EYoungAlloc? (ev es_inc 10) /\
                   T.Marking? (ci 12).ph /\ ev es_inc 12 == EMinor /\
                   T.Sweeping? (ci 18).ph /\ EAlloc? (ev es_inc 18) /\ T.Sweeping? (ci 19).ph /\ EWrite? (ev es_inc 19) /\
                   T.Sweeping? (ci 20).ph /\ EYoungAlloc? (ev es_inc 20) /\
                   T.Sweeping? (ci 22).ph /\ ev es_inc 22 == EMinor /\
                   T.Sweeping? (ci 23).ph /\ ERoots? (ev es_inc 23) /\
                   T.Idle? (ci 33).ph /\ ev es_inc 33 == EMinor)
  = assert_norm (EAlloc? (ev es_inc 8) /\ EWrite? (ev es_inc 9) /\ EYoungAlloc? (ev es_inc 10) /\
                 ev es_inc 12 == EMinor /\ EAlloc? (ev es_inc 18) /\ EWrite? (ev es_inc 19) /\
                 EYoungAlloc? (ev es_inc 20) /\ ev es_inc 22 == EMinor /\ ERoots? (ev es_inc 23) /\
                 ev es_inc 33 == EMinor);
    h8 (); h9 (); h10 (); h12 (); h18 (); h19 (); h20 (); h22 (); h23 (); h33 ();
    holds_def (ci 8) d8; holds_def (ci 9) d9; holds_def (ci 10) d10; holds_def (ci 12) (d12 ());
    holds_def (ci 18) d18; holds_def (ci 19) d19; holds_def (ci 20) d20; holds_def (ci 22) (d22 ());
    holds_def (ci 23) d23; holds_def (ci 33) d33

#push-options "--fuel 6"
let infix_w0 ()
  : Lemma (requires ff_room)
          (ensures (let w = wd (d12 ()) in
                    M.yreachable w 0 /\ M.yreachable w 2 /\
                    M.field w.M.yng 0 0 == vK2 /\ M.field w.M.yng 2 0 == iw /\
                    M.resolve w.M.maj (xK + 2) == Some xK))
  = let w = wd (d12 ()) in
    xs ();
    res_k2 st9;
    YW.yblocks vK2 iw;
    assert (L.memP y1 [y2; y1; vD; vA] /\ L.memP y2 [y2; y1; vD; vA]);
    yreach_root w 0 0;
    yreach_root w 2 2
#pop-options

/// **The collection at 12 sees Y1 (an infix pointer into the old closure K,
/// in use) and Y2 (an integer that reads as an infix header), both
/// reachable from the roots** (and promotes them: `promoted_12`).
#push-options "--z3rlimit 40"
let inc_infix_cases ()
  : Lemma (requires ff_room /\ L.length es_inc == 34)
          (ensures (let x = ci 12 in
                    let w = vw x in
                    ev es_inc 12 == EMinor /\ T.Marking? x.ph /\
                    M.yreachable w 0 /\ M.yreachable w 2 /\
                    M.field w.M.yng 0 0 == M.VPtr (M.Major (xK + 2)) /\
                    M.resolve w.M.maj (xK + 2) == Some xK /\ T.in_use fc.a x.ast x.w.cmaj w.M.maj xK == true /\
                    M.field w.M.yng 2 0 == M.infix_word 2 /\ Some? (M.infix_hdr (M.field w.M.yng 2 0))))
  = h12 ();
    assert_norm (ev es_inc 12 == EMinor);
    let x = ci 12 in
    let w0 = wd (d12 ()) in
    infix_w0 ();
    xs (); blk st9 xK;
    views_wd x (d12 ());
    holds_def x (d12 ());
    wheq_sym (vw x) w0;
    yreachable_wheq w0 (vw x) 0;
    yreachable_wheq w0 (vw x) 2;
    resolve_heq w0.M.maj (vw x).M.maj (xK + 2);
    assert_norm (M.infix_hdr (M.infix_word 2) == Some 2);
    assert ((cabs x.w.cmaj).M.hd xK == (mk st9).M.hd xK)
#pop-options
