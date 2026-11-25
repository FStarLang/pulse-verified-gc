/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWPre - the pages witness runs' common first events
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  Both pages witness runs (GC.Spec.Top.PWSeq, PWInc) start
/// on the page allocator's initial heap with, all idle:
///   0-3  A (two fields), B (one), C (one, holding B) and K (a closure of
///        three fields, its second the infix header of offset 2), allocated
///        and filled through the page allocator;
///   4    A.0 := B;
///   5    B.0 := K + 2, an infix pointer into K;
///   6    the roots become [A].
/// Then A, B and K are reachable (K only through B's infix pointer) and C,
/// in use, is not.  Where the allocator puts each block is its own answer
/// (`PWAlloc.aaddr`); the runs never compute it.
///
/// The runs hold under one explicit hypothesis, `pw_room`: at least 12
/// pages (the budget: one page per allocation, two per minor collection)
/// and a nursery of at least 4 words (two one-field young blocks).

module GC.Spec.Top.PWPre

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
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module RA = GC.Spec.Top.RunApp
module PWA = GC.Spec.Top.PWAlloc
module PWMu = GC.Spec.Top.PWMut
module PWF = GC.Spec.Top.PWFold
module PWM = GC.Spec.Top.PWMinor
module TR = GC.Spec.Top.Transp

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The hypothesis.
let pw_room : prop = 12 <= n_pages /\ 4 <= ywords

/// ---------------------------------------------------------------------------
/// Values
/// ---------------------------------------------------------------------------

let i1 : M.value = M.VInt 1
let iw : M.value = M.infix_word 2

let st_vals () : Lemma (storable_w i1 /\ storable_w iw /\ iw == M.VInt 2297)
  = assert_norm (M.infix_word 2 == M.VInt 2297);
    assert_norm (2297 < pow2 64);
    assert_norm (1 < pow2 64);
    odd_storable 2297;
    odd_storable 1

/// A pointer to a block in use, of at least one field, can be stored.
let st_blk (x: config pc) (o: nat)
  : Lemma (requires iu x o == true /\ M.wz_of (mx x) o >= 1) (ensures storable_w (M.VPtr (M.Major o)))
  = iu_def x o;
    major_storable o

let st_k2 (x: config pc) (d: dsc) (k: nat)
  : Lemma (requires holds x d /\ PWM.kdesc d k) (ensures storable_w (M.VPtr (M.Major (k + 2))))
  = holds_elim x d;
    blk x d k;
    assert (M.covers (mx x) k (k + 3));
    major_storable (k + 2)

/// ---------------------------------------------------------------------------
/// The configurations
/// ---------------------------------------------------------------------------

let x0 () : GTot (config pc) = init_config pc msize ywords

let e0 : event = EAlloc 2 0 [i1; i1]
let xA () : GTot nat = PWA.aaddr (x0 ()) 2 0
let x1 () : GTot (config pc) = step pc (x0 ()) e0
let d1 () : GTot dsc = PWA.dalloc (x0 ()) d0 2 0 [i1; i1]
let vA () : GTot M.value = M.VPtr (M.Major (xA ()))

let e1 : event = EAlloc 1 0 [i1]
let xB () : GTot nat = PWA.aaddr (x1 ()) 1 0
let x2 () : GTot (config pc) = step pc (x1 ()) e1
let d2 () : GTot dsc = PWA.dalloc (x1 ()) (d1 ()) 1 0 [i1]
let vB () : GTot M.value = M.VPtr (M.Major (xB ()))

let e2 () : GTot event = EAlloc 1 0 [vB ()]
let xC () : GTot nat = PWA.aaddr (x2 ()) 1 0
let x3 () : GTot (config pc) = step pc (x2 ()) (e2 ())
let d3 () : GTot dsc = PWA.dalloc (x2 ()) (d2 ()) 1 0 [vB ()]
let vC () : GTot M.value = M.VPtr (M.Major (xC ()))

let e3 : event = EAlloc 3 M.closure_tag [i1; iw; i1]
let xK () : GTot nat = PWA.aaddr (x3 ()) 3 M.closure_tag
let x4 () : GTot (config pc) = step pc (x3 ()) e3
let d4 () : GTot dsc = PWA.dalloc (x3 ()) (d3 ()) 3 M.closure_tag [i1; iw; i1]
let vK2 () : GTot M.value = M.VPtr (M.Major (xK () + 2))
let vK () : GTot M.value = M.VPtr (M.Major (xK ()))

let e4 () : GTot event = EWrite (M.Major (xA ())) 0 (vB ())
let x5 () : GTot (config pc) = step pc (x4 ()) (e4 ())
let d5 () : GTot dsc = PWMu.dwrite (x4 ()) (d4 ()) (xA ()) 0 (vB ())

let e5 () : GTot event = EWrite (M.Major (xB ())) 0 (vK2 ())
let x6 () : GTot (config pc) = step pc (x5 ()) (e5 ())
let d6 () : GTot dsc = PWMu.dwrite (x5 ()) (d5 ()) (xB ()) 0 (vK2 ())

let e6 () : GTot event = ERoots [vA ()]
let x7 () : GTot (config pc) = step pc (x6 ()) (e6 ())
let d7 () : GTot dsc = { d6 () with drt = [vA ()] }

/// The blocks, as described at 7.
let bA : bd = { bw = 2; bt = 0; bc = M.White; blv = true; bf = [M.VInt 0; i1] }
let blkA (b: M.value) : bd = { bw = 2; bt = 0; bc = M.White; blv = true; bf = [b; i1] }
let blkB (k2: M.value) : bd = { bw = 1; bt = 0; bc = M.White; blv = true; bf = [k2] }
let blkC (b: M.value) : bd = { bw = 1; bt = 0; bc = M.White; blv = true; bf = [b] }
let bK : bd = { bw = 3; bt = M.closure_tag; bc = M.White; blv = true; bf = [i1; iw; i1] }

/// ---------------------------------------------------------------------------
/// Short lists
/// ---------------------------------------------------------------------------

#push-options "--fuel 4"
let l1 (u: M.value)
  : Lemma ((forall (v: M.value). L.memP v [u] ==> v == u) /\ L.length [u] == 1 /\ L.index [u] 0 == u /\
           vi [u] 0 == u /\ GC.Spec.Top.FFWStep.no_young [u] == not (M.VPtr? u && M.Young? (M.VPtr?._0 u)))
  = ()

let l2 (u v: M.value)
  : Lemma ((forall (w: M.value). L.memP w [u; v] ==> w == u \/ w == v) /\ L.length [u; v] == 2 /\
           vi [u; v] 0 == u /\ vi [u; v] 1 == v /\ L.index [u; v] 0 == u /\ L.index [u; v] 1 == v /\
           GC.Spec.Top.FFWStep.no_young [u; v] ==
             (not (M.VPtr? u && M.Young? (M.VPtr?._0 u)) && not (M.VPtr? v && M.Young? (M.VPtr?._0 v))))
  = ()

let l3 (u v w: M.value)
  : Lemma ((forall (z: M.value). L.memP z [u; v; w] ==> z == u \/ z == v \/ z == w) /\ L.length [u; v; w] == 3 /\
           vi [u; v; w] 0 == u /\ vi [u; v; w] 1 == v /\ vi [u; v; w] 2 == w /\
           L.index [u; v; w] 0 == u /\ L.index [u; v; w] 1 == v /\ L.index [u; v; w] 2 == w /\
           GC.Spec.Top.FFWStep.no_young [u; v; w] ==
             (not (M.VPtr? u && M.Young? (M.VPtr?._0 u)) && not (M.VPtr? v && M.Young? (M.VPtr?._0 v)) &&
              not (M.VPtr? w && M.Young? (M.VPtr?._0 w))))
  = ()

let mem_hd (v: M.value) (l: list M.value) : Lemma (L.memP v (v :: l)) = ()
let mem_tl (u v: M.value) (l: list M.value) : Lemma (requires L.memP v l) (ensures L.memP v (u :: l)) = ()

let setv0 (u v w: M.value) : Lemma (PWMu.setv [u; v] 0 w == [w; v] /\ PWMu.setv [u] 0 w == [w]) = ()
#pop-options

/// ---------------------------------------------------------------------------
/// One event of the program, on a description
/// ---------------------------------------------------------------------------

/// Sequential: the program runs only while idle.
let sty_ok (sty: style) (d: dsc) : bool = Incremental? sty || DI? d.dk

let style_d (sty: style) (x: config pc) (d: dsc) (e: event)
  : Lemma (requires holds x d /\ sty_ok sty d) (ensures style_ok sty x e)
  = holds_elim x d

/// An allocation.
let alloc_ev (sty: style) (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires PWA.apre x d sz tag vs /\ sty_ok sty d /\ mutator_ok_w pc (wd x d) (EAlloc sz tag vs))
          (ensures holds (step pc x (EAlloc sz tag vs)) (PWA.dalloc x d sz tag vs) /\
                   iu x (PWA.aaddr x sz tag) == false /\
                   RA.conds pc sty x (EAlloc sz tag vs) /\ TR.alloc_succeeds x (EAlloc sz tag vs))
  = PWA.step_alloc x d sz tag vs;
    PWA.a_parts x sz tag;
    enabled_plain x d (EAlloc sz tag vs);
    style_d sty x d (EAlloc sz tag vs);
    conds_of sty x d (EAlloc sz tag vs)

/// A write to a major block.
let write_ev (sty: style) (x: config pc) (d: dsc) (o i: nat) (v: M.value)
  : Lemma (requires PWMu.wpre x d o i v /\ sty_ok sty d /\ mutator_ok_w pc (wd x d) (EWrite (M.Major o) i v))
          (ensures holds (step pc x (EWrite (M.Major o) i v)) (PWMu.dwrite x d o i v) /\
                   RA.conds pc sty x (EWrite (M.Major o) i v) /\ TR.alloc_succeeds x (EWrite (M.Major o) i v))
  = PWMu.step_write x d o i v;
    enabled_plain x d (EWrite (M.Major o) i v);
    style_d sty x d (EWrite (M.Major o) i v);
    conds_of sty x d (EWrite (M.Major o) i v)

/// A change of roots.
let roots_ev (sty: style) (x: config pc) (d: dsc) (rs: list M.value)
  : Lemma (requires cok /\ holds x d /\ sty_ok sty d /\ mutator_ok_w pc (wd x d) (ERoots rs))
          (ensures holds (step pc x (ERoots rs)) ({ d with drt = rs }) /\
                   RA.conds pc sty x (ERoots rs) /\ TR.alloc_succeeds x (ERoots rs))
  = PWMu.step_roots x d rs;
    enabled_plain x d (ERoots rs);
    style_d sty x d (ERoots rs);
    conds_of sty x d (ERoots rs)

/// A read of a major block's field.
let read_ev (sty: style) (x: config pc) (d: dsc) (o i: nat)
  : Lemma (requires cok /\ holds x d /\ Some? (d.db o) /\ usable d (Some?.v (d.db o)) /\ i < (Some?.v (d.db o)).bw /\
                    sty_ok sty d /\ mutator_ok_w pc (wd x d) (ERead (M.Major o) i))
          (ensures holds (step pc x (ERead (M.Major o) i)) ({ d with drt = vi (Some?.v (d.db o)).bf i :: d.drt }) /\
                   RA.conds pc sty x (ERead (M.Major o) i) /\ TR.alloc_succeeds x (ERead (M.Major o) i))
  = PWMu.step_read x d o i;
    enabled_plain x d (ERead (M.Major o) i);
    style_d sty x d (ERead (M.Major o) i);
    conds_of sty x d (ERead (M.Major o) i)

/// A young allocation.
let yalloc_ev (sty: style) (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
              (o: nat) (ms': GC.Gen.MinorHeap.minor_state)
  : Lemma (requires cok /\ holds x d /\ GC.Spec.Top.Young.yalloc d.dys sz tag vs == Some (o, ms') /\
                    tag <> M.infix_tag /\ L.length vs == sz /\ (forall (v: M.value). L.memP v vs ==> storable_w v) /\
                    sty_ok sty d /\ mutator_ok_w pc (wd x d) (EYoungAlloc sz tag vs))
          (ensures holds (step pc x (EYoungAlloc sz tag vs))
                         ({ d with dys = ms'; dym = M.young_alloc d.dym o sz tag vs;
                                   drt = M.VPtr (M.Young o) :: d.drt }) /\
                   RA.conds pc sty x (EYoungAlloc sz tag vs) /\ TR.alloc_succeeds x (EYoungAlloc sz tag vs))
  = PWMu.step_yalloc x d sz tag vs o ms';
    enabled_yalloc x d sz tag vs o ms';
    style_d sty x d (EYoungAlloc sz tag vs);
    conds_of sty x d (EYoungAlloc sz tag vs)

/// The program's obligations for a write to a block it reaches.
let mut_write (x: config pc) (d: dsc) (o i: nat) (v: M.value)
  : Lemma (requires holds x d /\ Some? (d.db o) /\ usable d (Some?.v (d.db o)) /\
                    (Some?.v (d.db o)).bt <> M.closure_tag /\ i < (Some?.v (d.db o)).bw /\
                    M.reachable (wd x d) o /\ value_ok (wd x d) v /\ storable_w v)
          (ensures mutator_ok_w pc (wd x d) (EWrite (M.Major o) i v))
  = blk x d o

/// ---------------------------------------------------------------------------
/// Events 0-6
/// ---------------------------------------------------------------------------

/// Both styles, while idle.
let both (x: config pc) (e: event) : prop = RA.conds pc Sequential x e /\ RA.conds pc Incremental x e

/// A described block the program may use: in use, its fields.
let ublk (x: config pc) (d: dsc) (o: nat)
  : Lemma (requires holds x d /\ Some? (d.db o) /\ usable d (Some?.v (d.db o)))
          (ensures iu x o == true /\ M.is_block (mx x) o /\ M.resolve (mx x) o == Some o /\
                   M.wz_of (mx x) o == (Some?.v (d.db o)).bw)
  = blk x d o

#push-options "--z3rlimit 40"
let h1 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x1 ()) (d1 ()) /\ both (x0 ()) e0 /\ TR.alloc_succeeds (x0 ()) e0)
  = init_holds ();
    PWF.smax ();
    st_vals ();
    l2 i1 i1;
    holds_elim (x0 ()) d0;
    assert (PWA.apre (x0 ()) d0 2 0 [i1; i1]);
    assert (mutator_ok_w pc (wd (x0 ()) d0) e0);
    alloc_ev Sequential (x0 ()) d0 2 0 [i1; i1];
    alloc_ev Incremental (x0 ()) d0 2 0 [i1; i1]

let h2 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x2 ()) (d2 ()) /\ both (x1 ()) e1 /\ TR.alloc_succeeds (x1 ()) e1 /\ xB () <> xA ())
  = h1 ();
    PWF.smax ();
    st_vals ();
    l1 i1;
    holds_elim (x1 ()) (d1 ());
    ublk (x1 ()) (d1 ()) (xA ());
    assert (PWA.apre (x1 ()) (d1 ()) 1 0 [i1]);
    assert (mutator_ok_w pc (wd (x1 ()) (d1 ())) e1);
    alloc_ev Sequential (x1 ()) (d1 ()) 1 0 [i1];
    alloc_ev Incremental (x1 ()) (d1 ()) 1 0 [i1]

let h3 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x3 ()) (d3 ()) /\ both (x2 ()) (e2 ()) /\ TR.alloc_succeeds (x2 ()) (e2 ()) /\
           xC () <> xA () /\ xC () <> xB ())
  = h2 ();
    PWF.smax ();
    let x = x2 () in
    let d = d2 () in
    holds_elim x d;
    ublk x d (xA ());
    ublk x d (xB ());
    l1 (vB ());
    st_blk x (xB ());
    assert (d.drt == vB () :: (d1 ()).drt);
    mem_hd (vB ()) (d1 ()).drt;
    reach_r x d (xB ());
    sound_p x d (xB ()) (xB ());
    assert (PWA.apre x d 1 0 [vB ()]);
    assert (mutator_ok_w pc (wd x d) (e2 ()));
    alloc_ev Sequential x d 1 0 [vB ()];
    alloc_ev Incremental x d 1 0 [vB ()]

#push-options "--fuel 1"
let rec nyl (l: list M.value)
  : Lemma (requires forall (v: M.value). L.memP v l ==> M.VInt? v)
          (ensures GC.Spec.Top.FFWStep.no_young l == true) (decreases l)
  = match l with [] -> () | _ :: tl -> nyl tl
#pop-options

/// Integer fields: what an allocation of them needs.
let ints_pre (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires cok /\ holds x d /\ d.dj < n_pages /\ sz + 1 <= small_max /\ tag <> M.infix_tag /\
                    L.length vs == sz /\
                    (forall (v: M.value). L.memP v vs ==> M.VInt? v /\ storable_w v))
          (ensures PWA.apre x d sz tag vs /\ mutator_ok_w pc (wd x d) (EAlloc sz tag vs))
  = let ny (v: M.value) : Lemma (L.memP v vs ==> not (M.VPtr? v && M.Young? (M.VPtr?._0 v))) = () in
    nyl vs;
    let ix (i: nat) : Lemma (i < L.length vs ==> M.VInt? (L.index vs i))
      = if i < L.length vs then L.lemma_index_memP vs i in
    FStar.Classical.forall_intro ix

let h4 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x4 ()) (d4 ()) /\ both (x3 ()) e3 /\ TR.alloc_succeeds (x3 ()) e3 /\
           xK () <> xA () /\ xK () <> xB () /\ xK () <> xC ())
  = h3 ();
    PWF.smax ();
    st_vals ();
    let x = x3 () in
    let d = d3 () in
    holds_elim x d;
    ublk x d (xA ());
    ublk x d (xB ());
    ublk x d (xC ());
    l3 i1 iw i1;
    ints_pre x d 3 M.closure_tag [i1; iw; i1];
    alloc_ev Sequential x d 3 M.closure_tag [i1; iw; i1];
    alloc_ev Incremental x d 3 M.closure_tag [i1; iw; i1]
#pop-options

#push-options "--z3rlimit 40"
let h5 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x5 ()) (d5 ()) /\ both (x4 ()) (e4 ()) /\ TR.alloc_succeeds (x4 ()) (e4 ()))
  = h4 (); h3 (); h2 ();
    let x = x4 () in
    let d = d4 () in
    holds_elim x d;
    ublk x d (xA ());
    ublk x d (xB ());
    l1 (vB ());
    st_blk x (xB ());
    assert (d.drt == [vK (); vC (); vB (); vA ()]);
    mem_hd (vA ()) [];
    mem_tl (vB ()) (vA ()) [vA ()];
    mem_tl (vC ()) (vA ()) [vB (); vA ()];
    mem_tl (vK ()) (vA ()) [vC (); vB (); vA ()];
    mem_hd (vB ()) [vA ()];
    mem_tl (vC ()) (vB ()) [vB (); vA ()];
    mem_tl (vK ()) (vB ()) [vC (); vB (); vA ()];
    reach_r x d (xA ());
    reach_r x d (xB ());
    res_mw_blk x (xA ()) 0 (vB ()) (xB ());
    sound_mw x d (xA ()) 0 (vB ()) (xB ()) (xB ());
    assert (PWMu.wpre x d (xA ()) 0 (vB ()));
    mut_write x d (xA ()) 0 (vB ());
    write_ev Sequential x d (xA ()) 0 (vB ());
    write_ev Incremental x d (xA ()) 0 (vB ())
#pop-options

/// The blocks at 5 and 6, from the descriptions.
let kd5 () : Lemma (requires pw_room /\ cok) (ensures PWM.kdesc (d5 ()) (xK ()))
  = h4 (); h3 (); h2 ();
    holds_elim (x4 ()) (d4 ());
    assert (PWMu.dt (x4 ()) (xA ()) 0 == None);
    assert ((d4 ()).db (xK ()) == Some ({ bw = 3; bt = M.closure_tag; bc = T.colour_at pk (x3 ()).ph (xK ());
                                          blv = true; bf = [i1; iw; i1] }));
    assert ((d5 ()).db (xK ()) == (d4 ()).db (xK ()));
    l3 i1 iw i1

/// The descriptions' blocks, explicitly.
let db4_def (y: nat) : GTot (option bd) =
  if y = xK () then Some bK
  else if y = xC () then Some (blkC (vB ()))
  else if y = xB () then Some (blkB i1)
  else if y = xA () then Some (blkA i1)
  else None

let db6_def (y: nat) : GTot (option bd) =
  if y = xK () then Some bK
  else if y = xC () then Some (blkC (vB ()))
  else if y = xB () then Some (blkB (vK2 ()))
  else if y = xA () then Some (blkA (vB ()))
  else None

let db4 (y: nat) : Lemma (requires pw_room /\ cok) (ensures (d4 ()).db y == db4_def y)
  = h1 (); h2 (); h3 (); h4 ();
    holds_elim (x1 ()) (d1 ()); holds_elim (x2 ()) (d2 ()); holds_elim (x3 ()) (d3 ())

let db6 (y: nat) : Lemma (requires pw_room /\ cok) (ensures (d6 ()).db y == db6_def y)
  = h2 (); h3 (); h4 (); h5 ();
    db4 y;
    holds_elim (x4 ()) (d4 ());
    holds_elim (x5 ()) (d5 ());
    assert (PWMu.dt (x4 ()) (xA ()) 0 == None);
    assert (PWMu.dt (x5 ()) (xB ()) 0 == None);
    setv0 i1 i1 (vB ());
    setv0 i1 i1 (vK2 ())

#push-options "--z3rlimit 40"
let h6 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x6 ()) (d6 ()) /\ both (x5 ()) (e5 ()) /\ TR.alloc_succeeds (x5 ()) (e5 ()))
  = h5 (); h4 (); h3 (); h2 ();
    let x = x5 () in
    let d = d5 () in
    holds_elim x d;
    kd5 ();
    ublk x d (xB ());
    ublk x d (xK ());
    blk x d (xK ());
    l1 (vK2 ());
    l3 i1 iw i1;
    st_k2 x d (xK ());
    assert (d.drt == [vK (); vC (); vB (); vA ()]);
    mem_hd (vB ()) [vA ()];
    mem_tl (vC ()) (vB ()) [vB (); vA ()];
    mem_tl (vK ()) (vB ()) [vC (); vB (); vA ()];
    mem_hd (vK ()) [vC (); vB (); vA ()];
    reach_r x d (xB ());
    reach_r x d (xK ());
    res_infix (mx x) (xK ());
    res_mw_infix x d (xB ()) 0 (vK2 ()) (xK ());
    sound_mw x d (xB ()) 0 (vK2 ()) (xK () + 2) (xK ());
    assert (PWMu.wpre x d (xB ()) 0 (vK2 ()));
    mut_write x d (xB ()) 0 (vK2 ());
    write_ev Sequential x d (xB ()) 0 (vK2 ());
    write_ev Incremental x d (xB ()) 0 (vK2 ())

let h7 () : Lemma (requires pw_room /\ cok)
  (ensures holds (x7 ()) (d7 ()) /\ both (x6 ()) (e6 ()) /\ TR.alloc_succeeds (x6 ()) (e6 ()))
  = h6 (); h4 (); h3 (); h2 ();
    let x = x6 () in
    let d = d6 () in
    holds_elim x d;
    db6 (xA ());
    ublk x d (xA ());
    l1 (vA ());
    st_blk x (xA ());
    assert (d.drt == [vK (); vC (); vB (); vA ()]);
    mem_hd (vA ()) [];
    mem_tl (vB ()) (vA ()) [vA ()];
    mem_tl (vC ()) (vA ()) [vB (); vA ()];
    mem_tl (vK ()) (vA ()) [vC (); vB (); vA ()];
    reach_r x d (xA ());
    assert (mutator_ok_w pc (wd x d) (e6 ()));
    roots_ev Sequential x d [vA ()];
    roots_ev Incremental x d [vA ()]
#pop-options

/// ---------------------------------------------------------------------------
/// Descriptions, pointwise
/// ---------------------------------------------------------------------------

let holds_ext (x: config pc) (d d': dsc)
  : Lemma (requires holds x d /\ d'.dk == d.dk /\ d'.dys == d.dys /\ d'.dym == d.dym /\ d'.drt == d.drt /\
                    d'.dj == d.dj /\ (forall (y: nat). d'.db y == d.db y))
          (ensures holds x d')
  = holds_elim x d;
    let bl (y: nat) : Lemma (Some? (d'.db y) ==> bk x d' y (Some?.v (d'.db y)))
      = if Some? (d.db y) then holds_blk x d y in
    FStar.Classical.forall_intro bl;
    let des (y: nat) : Lemma (iu x y == true ==> Some? (d'.db y))
      = if iu x y then holds_iu x d y in
    FStar.Classical.forall_intro des;
    holds_intro x d'

/// The runs' descriptions: A, B, K (live) and C (garbage, possibly gone),
/// each with its colour.
let dd (dk: phk) (cA cB cK: M.colour) (hasC: bool) (rs: list M.value) (j: nat)
       (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap) : GTot dsc =
  { dk = dk; dys = ys; dym = ym; drt = rs; dj = j;
    db = (fun (y: nat) ->
      if y = xK () then Some ({ bK with bc = cK })
      else if y = xC () then (if hasC then Some ({ blkC (vB ()) with blv = false }) else None)
      else if y = xB () then Some ({ blkB (vK2 ()) with bc = cB })
      else if y = xA () then Some ({ blkA (vB ()) with bc = cA })
      else None) }

/// **At 7, the cycle may start**: A is a root; A, B and K are reachable,
/// K only through B's infix pointer; C is in use and unreachable.
let d7c () : GTot dsc = dd DI M.White M.White M.White true [vA ()] 4 ms0 (M.empty_heap ywords)

let reach7_set (o: nat) : prop = o == xA () \/ o == xB () \/ o == xK ()

let h7c () : Lemma (requires pw_room /\ cok) (ensures holds (x7 ()) (d7c ()))
  = h7 (); h4 (); h3 (); h2 ();
    relabel (x7 ()) (d7 ()) (xC ()) false;
    let d' = relab (d7 ()) (xC ()) false in
    let pt (y: nat) : Lemma ((d7c ()).db y == d'.db y) = db6 y in
    FStar.Classical.forall_intro pt;
    holds_ext (x7 ()) d' (d7c ())

/// The live blocks of `dd`.
let bof (cA cB cK: M.colour) (o: nat) : GTot bd =
  if o = xK () then { bK with bc = cK }
  else if o = xB () then { blkB (vK2 ()) with bc = cB }
  else { blkA (vB ()) with bc = cA }

let distinct () : Lemma (requires pw_room /\ cok)
  (ensures xB () <> xA () /\ xC () <> xA () /\ xC () <> xB () /\ xK () <> xA () /\ xK () <> xB () /\ xK () <> xC ())
  = h2 (); h3 (); h4 ()

let db_dd (dk: phk) (cA cB cK: M.colour) (hasC: bool) (rs: list M.value) (j: nat)
          (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap) (o: nat)
  : Lemma (requires pw_room /\ cok /\ (o == xA () \/ o == xB () \/ o == xK ()))
          (ensures (dd dk cA cB cK hasC rs j ys ym).db o == Some (bof cA cB cK o))
  = distinct ()

/// The pointer fields of the runs' live blocks, and where they lead.
let fields_dd (x: config pc) (cA cB cK: M.colour) (o i a o': nat)
  : Lemma (requires pw_room /\ cok /\ (o == xA () \/ o == xB () \/ o == xK ()) /\
                    i < (bof cA cB cK o).bw /\ vi (bof cA cB cK o).bf i == M.VPtr (M.Major a) /\
                    M.resolve (mx x) a == Some o' /\
                    M.is_block (mx x) (xB ()) /\ M.is_block (mx x) (xK ()) /\ M.well_formed (mx x) /\
                    M.tag_of (mx x) (xK ()) == M.closure_tag /\ M.wz_of (mx x) (xK ()) == 3 /\
                    M.field (mx x) (xK ()) 1 == iw)
          (ensures (o == xA () /\ o' == xB ()) \/ (o == xB () /\ o' == xK ()))
  = distinct ();
    st_vals ();
    l2 (vB ()) i1; l1 (vK2 ()); l3 i1 iw i1;
    if o = xA () then begin
      assert ((bof cA cB cK o).bf == [vB (); i1]);
      assert (i < 2);
      if i = 1 then assert (vi [vB (); i1] 1 == i1)
    end
    else if o = xB () then begin
      assert ((bof cA cB cK o).bf == [vK2 ()]);
      assert (a == xK () + 2);
      res_infix (mx x) (xK ())
    end
    else begin
      assert ((bof cA cB cK o).bf == [i1; iw; i1]);
      assert (i < 3)
    end

/// **The reachable blocks** of a configuration described by `dd`, with the
/// roots and nursery given: exactly those reached from A through B to K.
let reach_dd (x: config pc) (dk: phk) (cA cB cK: M.colour) (hasC: bool) (rs: list M.value) (j: nat)
             (ys: GC.Gen.MinorHeap.minor_state) (ym: M.mheap)
  : Lemma (requires pw_room /\ cok /\ holds x (dd dk cA cB cK hasC rs j ys ym) /\
                    (forall (o: nat). M.outside_ref (wd x (dd dk cA cB cK hasC rs j ys ym)) o ==> reach7_set o))
          (ensures forall (o: nat). M.reachable (wd x (dd dk cA cB cK hasC rs j ys ym)) o ==> reach7_set o)
  = let d = dd dk cA cB cK hasC rs j ys ym in
    distinct ();
    holds_elim x d;
    db_dd dk cA cB cK hasC rs j ys ym (xB ());
    db_dd dk cA cB cK hasC rs j ys ym (xK ());
    db_dd dk cA cB cK hasC rs j ys ym (xA ());
    blk x d (xB ()); blk x d (xK ()); blk x d (xA ());
    l3 i1 iw i1;
    let cl (o i a o': nat)
      : Lemma (reach7_set o /\ i < (Some?.v (d.db o)).bw /\ M.scannable (Some?.v (d.db o)).bt /\
               vi (Some?.v (d.db o)).bf i == M.VPtr (M.Major a) /\ M.resolve (mx x) a == Some o' ==> reach7_set o')
      = if FStar.IndefiniteDescription.strong_excluded_middle
             (reach7_set o /\ i < (Some?.v (d.db o)).bw /\
              vi (Some?.v (d.db o)).bf i == M.VPtr (M.Major a) /\ M.resolve (mx x) a == Some o')
        then begin
          db_dd dk cA cB cK hasC rs j ys ym o;
          fields_dd x cA cB cK o i a o'
        end in
    FStar.Classical.forall_intro_4 cl;
    reach_closed x d reach7_set
