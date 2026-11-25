/// ---------------------------------------------------------------------------
/// GC.Spec.Top.T1Rep - T1, part 2: the stop-the-world replay; T1
/// ---------------------------------------------------------------------------
///
/// Design doc §16.18.  The replay starts with `es` up to the cycle's start
/// and a whole stop-the-world cycle (T2's `stw_exists`), then performs the
/// program's events one by one, through its own renaming (`T1Ext`).  An
/// allocation it has no room for: a major one runs a whole cycle, a minor
/// collection and a whole cycle; a young one a whole cycle and a minor
/// collection.  If the minor collection runs out of room, the replay stops
/// (S3); if the allocation then still fails, it stops (S1, S2).  Each
/// program event is one the original run performed on the same reference
/// store (`good`), so the replay can perform it.  `t1_run2`: both parts
/// of T1 for one run (assembled in GC.Spec.Top.T1).

module GC.Spec.Top.T1Rep

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.RInv
open GC.Spec.Top.Point
open GC.Spec.Top.Stw
open GC.Spec.Top.Transp
open GC.Spec.Top.TrRef
open GC.Spec.Top.TrVis
open GC.Spec.Top.T1Run
open GC.Spec.Top.T1Re
open GC.Spec.Top.T1Tr
open GC.Spec.Top.T1Ext
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module C = FStar.Classical
module ID = FStar.IndefiniteDescription
module RF = GC.Spec.Top.RunFacts
module RA = GC.Spec.Top.RunApp
module T2 = GC.Spec.Top.T2

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Chunks
/// ---------------------------------------------------------------------------

let flat_nil () : Lemma (flat [] == []) = assert_norm (flat [] == [])

let rec flat_app (cs1 cs2: list chunk)
  : Lemma (ensures flat (L.append cs1 cs2) == L.append (flat cs1) (flat cs2)) (decreases cs1)
  = match cs1 with
    | [] -> ()
    | CProg _ :: tl -> flat_app tl cs2
    | CMinor :: tl -> flat_app tl cs2
    | CCycle a b :: tl -> flat_app tl cs2; LP.append_assoc (stw_tail a b) (flat tl) (flat cs2)

let flat_one (ch: chunk)
  : Lemma (flat [ch] == (match ch with CProg e -> [e] | CMinor -> [EMinor] | CCycle a b -> stw_tail a b))
  = flat_nil ();
    match ch with CCycle a b -> LP.append_l_nil (stw_tail a b) | _ -> ()

#push-options "--fuel 2"
let cons_app (#t: Type) (x: t) (l: list t) : Lemma (L.append [x] l == x :: l) = ()
let mem_one (#t: Type) (x y: t) : Lemma (L.memP x [y] <==> x == y) = ()
#pop-options

let pre0 (es: list event) (s a b: nat) : list event = L.append (take s es) (stw_tail a b)

let es_of (es: list event) (s a b: nat) (cs: list chunk) : list event = L.append (pre0 es s a b) (flat cs)

let es_snoc (es: list event) (s a b: nat) (cs: list chunk) (ch: chunk)
  : Lemma (es_of es s a b (L.append cs [ch]) == L.append (es_of es s a b cs) (flat [ch]))
  = flat_app cs [ch];
    LP.append_assoc (pre0 es s a b) (flat cs) (flat [ch])

let chunks_ok (cs: list chunk) : prop =
  forall (ch: chunk). L.memP ch cs /\ CProg? ch ==> is_mutator_event (CProg?.e ch)

let chunks_snoc (cs: list chunk) (ch: chunk)
  : Lemma (requires chunks_ok cs /\ (CProg? ch ==> is_mutator_event (CProg?.e ch)))
          (ensures chunks_ok (L.append cs [ch]))
  = let f (ch': chunk) : Lemma (L.memP ch' (L.append cs [ch]) ==> L.memP ch' cs \/ ch' == ch)
      = LP.append_memP cs [ch] ch'; mem_one ch' ch in
    C.forall_intro f

/// ---------------------------------------------------------------------------
/// The replay's state
/// ---------------------------------------------------------------------------

/// Every event of the program is legal, names only what it reaches, and
/// was performed by the original run.
let good (c: comps) (prog: list revent) : prop =
  rok_all prog /\
  (forall (m: nat). m < L.length prog ==> names_reach (rat prog m) (rev_at prog m) /\ wit c (rat prog m) (rev_at prog m))

/// The replay after its chunks `cs`, at program event `m` (perhaps stopped).
let lst0 (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming) : prop =
  s <= L.length es /\ mc es s <= m /\ m <= L.length prog /\ chunks_ok cs /\
  core c sty n ny (es_of es s a b cs) (take m prog) io /\ Idle? (last_x c n ny (es_of es s a b cs)).ph

let lst (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming) : prop =
  lst0 c sty n ny es s prog a b cs m io /\ idle_ok (last_x c n ny (es_of es s a b cs))

/// **The replay, done or stuck.**
let fin (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming)
  : Lemma (requires lst0 c sty n ny es s prog a b cs m io /\
                    (let e2 = es_of es s a b cs in
                     m == L.length prog \/ stuck (last_x c n ny e2) (io (L.length e2)) (rev_at prog m) e2))
          (ensures stw_replay c sty n ny es s prog)
  = let e2 = es_of es s a b cs in
    let q = flat cs in
    T2.run_pre_elim c sty n ny e2;
    RA.take_len m prog;
    tr_done c n ny e2 (take m prog) io;
    assert (replay_events q);
    introduce exists (a' b': nat) (q': list event) (m': nat) (io': nat -> renaming).
      (let es2 = L.append (L.append (take s es) (stw_tail a' b')) q' in
       replay_events q' /\
       run_ok c sty n ny es2 /\ no_fail c n ny es2 /\
       mc es s <= m' /\ m' <= L.length prog /\
       transparent c n ny es2 (take m' prog) io' /\
       (m' == L.length prog \/
        stuck (at c n ny es2 (L.length es2)) (io' (L.length es2)) (rev_at prog m') es2))
    with a b q m io
    and ()

/// ---------------------------------------------------------------------------
/// One chunk more
/// ---------------------------------------------------------------------------

let st_trans (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming)
  : Lemma (requires good c prog /\ lst c sty n ny es s prog a b cs m io /\ m < L.length prog)
          (ensures (let e2 = es_of es s a b cs in
                    let x = last_x c n ny e2 in
                    exists (e: event). is_mutator_event e /\ mutator_ok x e /\
                      ev_corr (io (L.length e2)) (wv x) (rat prog m) e (rev_at prog m)))
  = trans_at c sty n ny (es_of es s a b cs) prog m io

let st_prog (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming) (e: event)
  : Lemma (requires components_ok c /\ good c prog /\ lst c sty n ny es s prog a b cs m io /\ m < L.length prog /\
                    (let e2 = es_of es s a b cs in
                     let x = last_x c n ny e2 in
                     is_mutator_event e /\ mutator_ok x e /\ enabled c x e /\ alloc_succeeds x e /\
                     ev_corr (io (L.length e2)) (wv x) (rat prog m) e (rev_at prog m)))
          (ensures exists (io': nat -> renaming). lst c sty n ny es s prog a b (L.append cs [CProg e]) (m + 1) io')
  = let e2 = es_of es s a b cs in
    prog_chunk c sty n ny e2 prog m io e;
    es_snoc es s a b cs (CProg e);
    flat_one (CProg e);
    chunks_snoc cs (CProg e)

let st_cyc (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming)
  : Lemma (requires components_ok c /\ lst c sty n ny es s prog a b cs m io)
          (ensures exists (a1 b1: nat) (io': nat -> renaming).
                     lst c sty n ny es s prog a b (L.append cs [CCycle a1 b1]) m io')
  = let e2 = es_of es s a b cs in
    cyc_chunk c sty n ny e2 (take m prog) io;
    eliminate exists (a1 b1: nat) (io': nat -> renaming).
      core c sty n ny (L.append e2 (stw_tail a1 b1)) (take m prog) io' /\
      idle_ok (last_x c n ny (L.append e2 (stw_tail a1 b1)))
    with begin
      es_snoc es s a b cs (CCycle a1 b1);
      flat_one (CCycle a1 b1);
      chunks_snoc cs (CCycle a1 b1);
      assert (lst c sty n ny es s prog a b (L.append cs [CCycle a1 b1]) m io')
    end

let st_min (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming)
  : Lemma (requires components_ok c /\ lst c sty n ny es s prog a b cs m io)
          (ensures exists (io': nat -> renaming). lst0 c sty n ny es s prog a b (L.append cs [CMinor]) m io')
  = let e2 = es_of es s a b cs in
    min_chunk c sty n ny e2 (take m prog) io;
    es_snoc es s a b cs CMinor;
    flat_one CMinor;
    chunks_snoc cs CMinor

/// ---------------------------------------------------------------------------
/// How the replay ends
/// ---------------------------------------------------------------------------

let ends_m (es: list event) (s a b: nat) (cs: list chunk)
  : Lemma (ends_with (es_of es s a b (L.append cs [CMinor])) [EMinor])
  = es_snoc es s a b cs CMinor;
    flat_one CMinor

let ends_cm (es: list event) (s a b: nat) (cs: list chunk) (a1 b1: nat)
  : Lemma (ends_with (es_of es s a b (L.append (L.append cs [CCycle a1 b1]) [CMinor])) (L.append (stw_tail a1 b1) [EMinor]))
  = es_snoc es s a b (L.append cs [CCycle a1 b1]) CMinor;
    es_snoc es s a b cs (CCycle a1 b1);
    flat_one (CCycle a1 b1);
    flat_one CMinor;
    LP.append_assoc (es_of es s a b cs) (stw_tail a1 b1) [EMinor]

let ends_mc (es: list event) (s a b: nat) (cs: list chunk) (a2 b2: nat)
  : Lemma (ends_with (es_of es s a b (L.append (L.append cs [CMinor]) [CCycle a2 b2])) (EMinor :: stw_tail a2 b2))
  = es_snoc es s a b (L.append cs [CMinor]) (CCycle a2 b2);
    es_snoc es s a b cs CMinor;
    flat_one (CCycle a2 b2);
    flat_one CMinor;
    LP.append_assoc (es_of es s a b cs) [EMinor] (stw_tail a2 b2);
    cons_app EMinor (stw_tail a2 b2)

/// What the replay reaches from `m`: the end, or program event `m + 1`.
let goal (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat) (m: nat) : prop =
  stw_replay c sty n ny es s prog \/
  (exists (cs': list chunk) (io': nat -> renaming). lst c sty n ny es s prog a b cs' (m + 1) io')

/// The program event at hand, if the replay can perform it now.
let try_prog (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming) (e: event)
  : Lemma (requires components_ok c /\ good c prog /\ lst c sty n ny es s prog a b cs m io /\ m < L.length prog /\
                    (let e2 = es_of es s a b cs in
                     let x = last_x c n ny e2 in
                     is_mutator_event e /\ mutator_ok x e /\ enabled c x e /\ alloc_succeeds x e /\
                     ev_corr (io (L.length e2)) (wv x) (rat prog m) e (rev_at prog m)))
          (ensures goal c sty n ny es s prog a b m)
  = st_prog c sty n ny es s prog a b cs m io e

/// ---------------------------------------------------------------------------
/// Events that need no room
/// ---------------------------------------------------------------------------

let en_plain (c: comps) (x: config c) (rn: renaming) (w: world) (r: rstore) (e: event) (re: revent)
  : Lemma (requires idle_ok x /\ ev_corr rn w r e re /\ ~(RAlloc? re))
          (ensures enabled c x e /\ alloc_succeeds x e)
  = ()

let next_plain (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming)
  : Lemma (requires components_ok c /\ good c prog /\ lst c sty n ny es s prog a b cs m io /\ m < L.length prog /\
                    ~(RAlloc? (rev_at prog m)))
          (ensures goal c sty n ny es s prog a b m)
  = let e2 = es_of es s a b cs in
    let x = last_x c n ny e2 in
    st_trans c sty n ny es s prog a b cs m io;
    eliminate exists (e: event). is_mutator_event e /\ mutator_ok x e /\
                                 ev_corr (io (L.length e2)) (wv x) (rat prog m) e (rev_at prog m)
    with begin
      en_plain c x (io (L.length e2)) (wv x) (rat prog m) e (rev_at prog m);
      try_prog c sty n ny es s prog a b cs m io e
    end

/// ---------------------------------------------------------------------------
/// A major allocation
/// ---------------------------------------------------------------------------

let en_major (c: comps) (x: config c) (rn: renaming) (w: world) (r: rstore) (e: event) (re: revent)
  : Lemma (requires idle_ok x /\ ev_corr rn w r e re /\ RAlloc? re /\ RAlloc?.young re == false)
          (ensures enabled c x e)
  = ()

let s1_stuck (c: comps) (x: config c) (rn: renaming) (r: rstore) (e: event) (re: revent) (es2: list event)
  : Lemma (requires x.stopped == false /\ rok r re /\ RAlloc? re /\ RAlloc?.young re == false /\
                    ev_corr rn (wv x) r e re /\ ~(alloc_succeeds x e) /\
                    (exists (a2 b2: nat). ends_with es2 (EMinor :: stw_tail a2 b2)))
          (ensures stuck x rn re es2)
  = match e with
    | EAlloc sz tag vs -> let (_, _, res) = c.a.alloc x.ph x.w.cmaj x.ast sz tag in (match res with NoRoom -> () | Ok _ -> ())

let s3_stuck (c: comps) (x: config c) (rn: renaming) (r: rstore) (re: revent) (es2: list event)
  : Lemma (requires x.stopped == true /\ rok r re /\ RAlloc? re /\
                    (exists (a1 b1: nat). ends_with es2 (L.append (stw_tail a1 b1) [EMinor])))
          (ensures stuck x rn re es2)
  = ()

/// After a whole cycle, a minor collection and a whole cycle: perform it,
/// or (S1).
let maj_last (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming)
  : Lemma (requires components_ok c /\ good c prog /\ lst c sty n ny es s prog a b cs m io /\ m < L.length prog /\
                    RAlloc? (rev_at prog m) /\ RAlloc?.young (rev_at prog m) == false /\
                    (exists (a2 b2: nat). ends_with (es_of es s a b cs) (EMinor :: stw_tail a2 b2)))
          (ensures goal c sty n ny es s prog a b m)
  = let e2 = es_of es s a b cs in
    let x = last_x c n ny e2 in
    st_trans c sty n ny es s prog a b cs m io;
    eliminate exists (e: event). is_mutator_event e /\ mutator_ok x e /\
                                 ev_corr (io (L.length e2)) (wv x) (rat prog m) e (rev_at prog m)
    with begin
      if ID.strong_excluded_middle (alloc_succeeds x e) then begin
        en_major c x (io (L.length e2)) (wv x) (rat prog m) e (rev_at prog m);
        try_prog c sty n ny es s prog a b cs m io e
      end else begin
        assert (rok (rat prog m) (rev_at prog m));
        s1_stuck c x (io (L.length e2)) (rat prog m) e (rev_at prog m) e2;
        fin c sty n ny es s prog a b cs m io
      end
    end

/// After a whole cycle and a minor collection: stopped (S3), or a whole
/// cycle more.
let maj_mid (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (a1 b1: nat) (m: nat) (io: nat -> renaming)
  : Lemma (requires (let cs2 = L.append (L.append cs [CCycle a1 b1]) [CMinor] in
                     components_ok c /\ good c prog /\ lst0 c sty n ny es s prog a b cs2 m io /\ m < L.length prog /\
                     RAlloc? (rev_at prog m) /\ RAlloc?.young (rev_at prog m) == false))
          (ensures goal c sty n ny es s prog a b m)
  = let cs1 = L.append cs [CCycle a1 b1] in
    let cs2 = L.append cs1 [CMinor] in
    let x = last_x c n ny (es_of es s a b cs2) in
    if x.stopped then begin
      ends_cm es s a b cs a1 b1;
      assert (rok (rat prog m) (rev_at prog m));
      s3_stuck c x (io (L.length (es_of es s a b cs2))) (rat prog m) (rev_at prog m) (es_of es s a b cs2);
      fin c sty n ny es s prog a b cs2 m io
    end else begin
      st_cyc c sty n ny es s prog a b cs2 m io;
      eliminate exists (a2 b2: nat) (io': nat -> renaming). lst c sty n ny es s prog a b (L.append cs2 [CCycle a2 b2]) m io'
      with begin
        ends_mc es s a b cs1 a2 b2;
        maj_last c sty n ny es s prog a b (L.append cs2 [CCycle a2 b2]) m io'
      end
    end

let next_major (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming)
  : Lemma (requires components_ok c /\ good c prog /\ lst c sty n ny es s prog a b cs m io /\ m < L.length prog /\
                    RAlloc? (rev_at prog m) /\ RAlloc?.young (rev_at prog m) == false)
          (ensures goal c sty n ny es s prog a b m)
  = let e2 = es_of es s a b cs in
    let x = last_x c n ny e2 in
    st_trans c sty n ny es s prog a b cs m io;
    eliminate exists (e: event). is_mutator_event e /\ mutator_ok x e /\
                                 ev_corr (io (L.length e2)) (wv x) (rat prog m) e (rev_at prog m)
    with begin
      if ID.strong_excluded_middle (alloc_succeeds x e) then begin
        en_major c x (io (L.length e2)) (wv x) (rat prog m) e (rev_at prog m);
        try_prog c sty n ny es s prog a b cs m io e
      end else begin
        st_cyc c sty n ny es s prog a b cs m io;
        eliminate exists (a1 b1: nat) (io1: nat -> renaming). lst c sty n ny es s prog a b (L.append cs [CCycle a1 b1]) m io1
        with begin
          st_min c sty n ny es s prog a b (L.append cs [CCycle a1 b1]) m io1;
          eliminate exists (io2: nat -> renaming).
            lst0 c sty n ny es s prog a b (L.append (L.append cs [CCycle a1 b1]) [CMinor]) m io2
          with maj_mid c sty n ny es s prog a b cs a1 b1 m io2
        end
      end
    end

/// ---------------------------------------------------------------------------
/// A young allocation
/// ---------------------------------------------------------------------------

let s2_of (c: comps) (rn: renaming) (w: world) (r: rstore) (x: config c) (e: event) (tag: tag_t) (rvs: list rval)
  : Lemma (requires inj rn w /\ clean rn w r /\ ev_corr rn w r e (RAlloc true tag rvs) /\ ~(enabled c x e) /\
                    x.stopped == false)
          (ensures forall (vs: list value). vcorr_list rn w (scannable tag) vs rvs ==>
                     None? (c.r.yalloc x.w.cyng (L.length rvs) tag vs))
  = match e with
    | EYoungAlloc sz tag' vs0 ->
      let f (vs: list value) : Lemma (vcorr_list rn w (scannable tag) vs rvs ==> vs == vs0)
        = if ID.strong_excluded_middle (vcorr_list rn w (scannable tag) vs rvs)
          then vlist_unique rn w (scannable tag) vs vs0 rvs in
      C.forall_intro f

/// After a whole cycle and a minor collection, not stopped: perform it, or
/// (S2).
let yng_last (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming)
  : Lemma (requires components_ok c /\ good c prog /\ lst c sty n ny es s prog a b cs m io /\ m < L.length prog /\
                    RAlloc? (rev_at prog m) /\ RAlloc?.young (rev_at prog m) == true /\
                    ends_with (es_of es s a b cs) [EMinor])
          (ensures goal c sty n ny es s prog a b m)
  = let e2 = es_of es s a b cs in
    let x = last_x c n ny e2 in
    let rn = io (L.length e2) in
    st_trans c sty n ny es s prog a b cs m io;
    eliminate exists (e: event). is_mutator_event e /\ mutator_ok x e /\
                                 ev_corr rn (wv x) (rat prog m) e (rev_at prog m)
    with begin
      if ID.strong_excluded_middle (enabled c x e) then try_prog c sty n ny es s prog a b cs m io e
      else begin
        let RAlloc _ tag rvs = rev_at prog m in
        RA.take_len m prog;
        rat_take prog m m;
        core_end c sty n ny e2 (take m prog) io;
        s2_of c rn (wv x) (rat prog m) x e tag rvs;
        fin c sty n ny es s prog a b cs m io
      end
    end

let yng_mid (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (a1 b1: nat) (m: nat) (io: nat -> renaming)
  : Lemma (requires (let cs2 = L.append (L.append cs [CCycle a1 b1]) [CMinor] in
                     components_ok c /\ good c prog /\ lst0 c sty n ny es s prog a b cs2 m io /\ m < L.length prog /\
                     RAlloc? (rev_at prog m) /\ RAlloc?.young (rev_at prog m) == true))
          (ensures goal c sty n ny es s prog a b m)
  = let cs1 = L.append cs [CCycle a1 b1] in
    let cs2 = L.append cs1 [CMinor] in
    let x = last_x c n ny (es_of es s a b cs2) in
    if x.stopped then begin
      ends_cm es s a b cs a1 b1;
      assert (rok (rat prog m) (rev_at prog m));
      s3_stuck c x (io (L.length (es_of es s a b cs2))) (rat prog m) (rev_at prog m) (es_of es s a b cs2);
      fin c sty n ny es s prog a b cs2 m io
    end else begin
      ends_m es s a b cs1;
      yng_last c sty n ny es s prog a b cs2 m io
    end

let next_young (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming)
  : Lemma (requires components_ok c /\ good c prog /\ lst c sty n ny es s prog a b cs m io /\ m < L.length prog /\
                    RAlloc? (rev_at prog m) /\ RAlloc?.young (rev_at prog m) == true)
          (ensures goal c sty n ny es s prog a b m)
  = let e2 = es_of es s a b cs in
    let x = last_x c n ny e2 in
    st_trans c sty n ny es s prog a b cs m io;
    eliminate exists (e: event). is_mutator_event e /\ mutator_ok x e /\
                                 ev_corr (io (L.length e2)) (wv x) (rat prog m) e (rev_at prog m)
    with begin
      if ID.strong_excluded_middle (enabled c x e) then try_prog c sty n ny es s prog a b cs m io e
      else begin
        st_cyc c sty n ny es s prog a b cs m io;
        eliminate exists (a1 b1: nat) (io1: nat -> renaming). lst c sty n ny es s prog a b (L.append cs [CCycle a1 b1]) m io1
        with begin
          st_min c sty n ny es s prog a b (L.append cs [CCycle a1 b1]) m io1;
          eliminate exists (io2: nat -> renaming).
            lst0 c sty n ny es s prog a b (L.append (L.append cs [CCycle a1 b1]) [CMinor]) m io2
          with yng_mid c sty n ny es s prog a b cs a1 b1 m io2
        end
      end
    end

/// ---------------------------------------------------------------------------
/// The loop
/// ---------------------------------------------------------------------------

let next (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming)
  : Lemma (requires components_ok c /\ good c prog /\ lst c sty n ny es s prog a b cs m io /\ m < L.length prog)
          (ensures goal c sty n ny es s prog a b m)
  = match rev_at prog m with
    | RAlloc false _ _ -> next_major c sty n ny es s prog a b cs m io
    | RAlloc true _ _ -> next_young c sty n ny es s prog a b cs m io
    | _ -> next_plain c sty n ny es s prog a b cs m io

let rec loop (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (a b: nat)
    (cs: list chunk) (m: nat) (io: nat -> renaming)
  : Lemma (requires components_ok c /\ good c prog /\ lst c sty n ny es s prog a b cs m io)
          (ensures stw_replay c sty n ny es s prog)
          (decreases (L.length prog - m))
  = if m = L.length prog then fin c sty n ny es s prog a b cs m io
    else begin
      next c sty n ny es s prog a b cs m io;
      if ID.strong_excluded_middle (stw_replay c sty n ny es s prog) then ()
      else
        eliminate exists (cs': list chunk) (io': nat -> renaming). lst c sty n ny es s prog a b cs' (m + 1) io'
        with loop c sty n ny es s prog a b cs' (m + 1) io'
    end

/// ---------------------------------------------------------------------------
/// The start: `es` up to `s`, then a whole cycle
/// ---------------------------------------------------------------------------

let pre0_nofail (c: comps) (n ny: nat) (es: list event) (s a b: nat)
  : Lemma (requires no_fail c n ny es /\ s <= L.length es) (ensures no_fail c n ny (pre0 es s a b))
  = let e2 = pre0 es s a b in
    T2.stw_ev es s a b 0;
    let f (i: nat) : Lemma (i < L.length e2 ==> alloc_succeeds (at c n ny e2 i) (ev e2 i))
      = if i < L.length e2 then begin
          if i < s then begin
            RA.at_pre c n ny es s (stw_tail a b) i;
            RA.ev_pre es s (stw_tail a b) i
          end else T2.stw_ev es s a b (i - s)
        end in
    C.forall_intro f

let pre0_coll (es: list event) (s a b: nat)
  : Lemma (requires s <= L.length es)
          (ensures s <= L.length (pre0 es s a b) /\
                   (forall (i: nat). s <= i /\ i < L.length (pre0 es s a b) ==> ~(is_mutator_event (ev (pre0 es s a b) i))))
  = T2.stw_ev es s a b 0;
    let f (i: nat) : Lemma (s <= i /\ i < L.length (pre0 es s a b) ==> ~(is_mutator_event (ev (pre0 es s a b) i)))
      = if s <= i && i < L.length (pre0 es s a b) then T2.stw_ev es s a b (i - s) in
    C.forall_intro f

let init (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) (io0: nat -> renaming) (a b: nat)
  : Lemma (requires run_pre c sty n ny es /\ no_fail c n ny es /\ tr_upto c n ny es (L.length es) prog io0 /\
                    s <= L.length es /\ run_pre c sty n ny (pre0 es s a b))
          (ensures exists (io: nat -> renaming). lst c sty n ny es s prog a b [] (mc es s) io)
  = let e2 = pre0 es s a b in
    let p = take (mc es s) prog in
    flat_nil ();
    LP.append_l_nil e2;
    assert (es_of es s a b [] == e2);
    pre0_nofail c n ny es s a b;
    tr_cut c n ny es (L.length es) prog io0 s;
    tr_pre c n ny es s (stw_tail a b) s p io0;
    pre0_coll es s a b;
    tr_coll_run c sty n ny e2 s (L.length e2) p io0;
    cyc_end c sty n ny es s a b;
    mc_mono es s (L.length es)

/// ---------------------------------------------------------------------------
/// The program the original run performed
/// ---------------------------------------------------------------------------

let rec mc_hit (es: list event) (t m: nat)
  : Lemma (requires t <= L.length es /\ m < mc es t)
          (ensures exists (i: nat). i < t /\ is_mutator_event (ev es i) /\ mc es i == m) (decreases t)
  = if t = 0 then mc_zero es
    else begin
      mc_succ es (t - 1);
      if m < mc es (t - 1) then mc_hit es (t - 1) m
    end

let good_at (c: comps) (sty: style) (n ny: nat) (es: list event) (prog: list revent) (io: nat -> renaming) (m: nat)
  : Lemma (requires run_pre c sty n ny es /\ tr_upto c n ny es (L.length es) prog io /\ m < L.length prog)
          (ensures rok (rat prog m) (rev_at prog m) /\ wit c (rat prog m) (rev_at prog m))
  = reveal_opaque (`%tu_pt) tu_pt; reveal_opaque (`%tu_ev) tu_ev;
    mc_hit es (L.length es) m;
    eliminate exists (i: nat). i < L.length es /\ is_mutator_event (ev es i) /\ mc es i == m
    with begin
      let x = at c n ny es i in
      assert (tu_pt c n ny es prog io i);
      assert (tu_ev c n ny es prog io i);
      scorr_eq (io i) x (rat prog m);
      at_i c sty n ny es i;
      assert (src (io i) (wv x) (rat prog m))
    end

let good_of (c: comps) (sty: style) (n ny: nat) (es: list event) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires run_pre c sty n ny es /\ tr_upto c n ny es (L.length es) prog io /\ names_reachable prog)
          (ensures good c prog)
  = let f (m: nat) : Lemma (m < L.length prog ==> rok (rat prog m) (rev_at prog m) /\ wit c (rat prog m) (rev_at prog m))
      = if m < L.length prog then good_at c sty n ny es prog io m in
    C.forall_intro f

/// **The stop-the-world replay of a cycle.**
let replay_of (c: comps) (sty: style) (n ny: nat) (es: list event) (s j: nat) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires components_ok c /\ run_pre c sty n ny es /\ no_fail c n ny es /\
                    tr_upto c n ny es (L.length es) prog io /\ names_reachable prog /\ is_cycle es s j)
          (ensures stw_replay c sty n ny es s prog)
  = good_of c sty n ny es prog io;
    T2.run_pre_elim c sty n ny es;
    T2.stw_exists c sty n ny es s j;
    eliminate exists (a b: nat). run_pre c sty n ny (T2.es2 es s a b) /\ run_pre c sty n ny es
    with begin
      init c sty n ny es s prog io a b;
      eliminate exists (io1: nat -> renaming). lst c sty n ny es s prog a b [] (mc es s) io1
      with loop c sty n ny es s prog a b [] (mc es s) io1
    end

/// ---------------------------------------------------------------------------
/// T1, for one run
/// ---------------------------------------------------------------------------

/// **Both parts of T1, for one run.**
let t1_run2 (c: comps) (sty: style) (n ny: nat) (es: list event)
  : Lemma (requires components_ok c /\ run_ok c sty n ny es /\ no_fail c n ny es)
          (ensures exists (prog: list revent) (io: nat -> renaming).
                     transparent c n ny es prog io /\
                     (names_reachable prog ==>
                        (forall (s j: nat). is_cycle es s j ==> stw_replay c sty n ny es s prog)))
  = RF.run_hyps_of_ok c n ny es;
    run_pre_intro c sty n ny es;
    tr_all c sty n ny es (L.length es);
    eliminate exists (prog: list revent) (io: nat -> renaming). tr_upto c n ny es (L.length es) prog io
    with begin
      tr_done c n ny es prog io;
      let f (s j: nat) : Lemma (names_reachable prog ==> is_cycle es s j ==> stw_replay c sty n ny es s prog)
        = if ID.strong_excluded_middle (names_reachable prog /\ is_cycle es s j)
          then replay_of c sty n ny es s j prog io in
      C.forall_intro_2 f
    end
