/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWOps - the witness runs' model updates, in closed form
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  Each event of the first-fit witness runs updates the
/// model heap `mk st` (GC.Spec.Top.FFWState) to `mk st'` for a record `st'`
/// read off the event: an allocation and its Fill, a recolouring, a field
/// written, the sweep freeing C, the mark's start and slices.  Each lemma
/// here is that equation (`R.heq`), word by word, under `ff_room`.

module GC.Spec.Top.FFWOps

open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.FFWModel
open GC.Spec.Top.FFWState
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module FWA = GC.Spec.Top.FFWAlloc
module FWS = GC.Spec.Top.FFWSweep
module TM = GC.Spec.Top.ToyMark
module BB = GC.Spec.Top.ByteBarrier

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Allocation and Fill
/// ---------------------------------------------------------------------------

let alloc_view (m: M.mheap) (f: nat) (sz: nat{sz + 2 <= f}) (tag: M.tag_t) (col: M.colour) (vs: list M.value)
  : Lemma (let m' = M.fill (FWA.split m f sz tag col) (f - sz) vs in
           m'.M.size == m.M.size /\
           (forall (x: nat). m'.M.hd x == (if x = 0 then Some (FWA.free_hdr (f - sz - 1))
                                           else if x = f - sz then Some ({ M.wz = sz; M.tag = tag; M.col = col })
                                           else m.M.hd x)) /\
           (forall (w: nat). m'.M.body w == (if f - sz < w && w - (f - sz) - 1 < L.length vs then L.index vs (w - (f - sz) - 1)
                                             else if w = f - sz then M.VInt 0 else m.M.body w)))
  = FWA.split_def m f sz tag col

#push-options "--fuel 2 --z3rlimit 40"
let alloc_A (st: wst) (col: M.colour)
  : Lemma (requires ff_room /\ st.f == sub msize 1 /\ st.ca == None)
          (ensures R.heq (M.fill (FWA.split (mk st) st.f 2 0 col) (st.f - 2) [M.VInt 1; M.VInt 1])
                         (mk ({ st with f = sub msize 4; ca = Some col; a0 = M.VInt 1; a1 = M.VInt 1 })))
  = xs (); alloc_view (mk st) st.f 2 0 col [M.VInt 1; M.VInt 1]

let alloc_B (st: wst) (col: M.colour)
  : Lemma (requires ff_room /\ st.f == sub msize 4 /\ st.cb == None)
          (ensures R.heq (M.fill (FWA.split (mk st) st.f 1 0 col) (st.f - 1) [M.VInt 1])
                         (mk ({ st with f = sub msize 6; cb = Some col })))
  = xs (); alloc_view (mk st) st.f 1 0 col [M.VInt 1]

let alloc_C (st: wst) (col: M.colour) (v: M.value)
  : Lemma (requires ff_room /\ st.f == sub msize 6 /\ st.cc == None)
          (ensures R.heq (M.fill (FWA.split (mk st) st.f 1 0 col) (st.f - 1) [v])
                         (mk ({ st with f = sub msize 8; cc = Some col; c0 = v })))
  = xs (); alloc_view (mk st) st.f 1 0 col [v]

#push-options "--fuel 4"
/// K, read pointwise (the whole equation at once is fragile across seeds).
let alloc_K_hd (st: wst) (col: M.colour) (x: nat)
  : Lemma (requires ff_room /\ st.f == sub msize 8 /\ st.ck == None)
          (ensures (M.fill (FWA.split (mk st) st.f 3 M.closure_tag col) (st.f - 3)
                           [M.VInt 1; M.infix_word 2; M.VInt 1]).M.hd x ==
                   (mk ({ st with f = sub msize 12; ck = Some col })).M.hd x)
  = xs (); alloc_view (mk st) st.f 3 M.closure_tag col [M.VInt 1; M.infix_word 2; M.VInt 1]

let alloc_K_bd (st: wst) (col: M.colour) (w: nat)
  : Lemma (requires ff_room /\ st.f == sub msize 8 /\ st.ck == None)
          (ensures (M.fill (FWA.split (mk st) st.f 3 M.closure_tag col) (st.f - 3)
                           [M.VInt 1; M.infix_word 2; M.VInt 1]).M.body w ==
                   (mk ({ st with f = sub msize 12; ck = Some col })).M.body w)
  = xs (); alloc_view (mk st) st.f 3 M.closure_tag col [M.VInt 1; M.infix_word 2; M.VInt 1]

let alloc_K (st: wst) (col: M.colour)
  : Lemma (requires ff_room /\ st.f == sub msize 8 /\ st.ck == None)
          (ensures R.heq (M.fill (FWA.split (mk st) st.f 3 M.closure_tag col) (st.f - 3)
                                 [M.VInt 1; M.infix_word 2; M.VInt 1])
                         (mk ({ st with f = sub msize 12; ck = Some col })))
  = alloc_view (mk st) st.f 3 M.closure_tag col [M.VInt 1; M.infix_word 2; M.VInt 1];
    FStar.Classical.forall_intro (FStar.Classical.move_requires (alloc_K_hd st col));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (alloc_K_bd st col))
#pop-options

let alloc_D (st: wst) (col: M.colour) (v: M.value)
  : Lemma (requires ff_room /\ st.f == sub msize 12 /\ st.cd == None)
          (ensures R.heq (M.fill (FWA.split (mk st) st.f 1 0 col) (st.f - 1) [v])
                         (mk ({ st with f = sub msize 14; cd = Some col; d0 = v })))
  = xs (); alloc_view (mk st) st.f 1 0 col [v]

let alloc_E (st: wst) (col: M.colour)
  : Lemma (requires ff_room /\ st.f == sub msize 18 /\ st.ce == None)
          (ensures R.heq (M.fill (FWA.split (mk st) st.f 1 0 col) (st.f - 1) [M.VPtr (M.Major xA)])
                         (mk ({ st with f = sub msize 20; ce = Some col })))
  = xs (); alloc_view (mk st) st.f 1 0 col [M.VPtr (M.Major xA)]
#pop-options

/// ---------------------------------------------------------------------------
/// Recolouring
/// ---------------------------------------------------------------------------

let recol (st: wst) (x: nat) (c: M.colour) : wst =
  if x = xP1 then { st with cp1 = Some c }
  else if x = xP2 then { st with cp2 = Some c }
  else if x = xP3 then { st with cp3 = Some c }
  else if x = xP4 then { st with cp4 = Some c }
  else if x = xA then { st with ca = Some c }
  else if x = xB then { st with cb = Some c }
  else if x = xC then { st with cc = Some c }
  else if x = xK then { st with ck = Some c }
  else if x = xD then { st with cd = Some c }
  else if x = xE then { st with ce = Some c }
  else st

let present (st: wst) (x: nat) : bool =
  (x = xA && Some? st.ca) || (x = xB && Some? st.cb) || (x = xC && Some? st.cc) ||
  (x = xK && Some? st.ck) || (x = xD && Some? st.cd) || (x = xE && Some? st.ce) ||
  (x = xP1 && Some? st.cp1) || (x = xP2 && Some? st.cp2) || (x = xP3 && Some? st.cp3) || (x = xP4 && Some? st.cp4)

#push-options "--z3rlimit 40"
let recol_eq (st: wst) (x: nat) (c: M.colour)
  : Lemma (requires ff_room /\ present st x) (ensures R.heq (M.set_col (mk st) x c) (mk (recol st x c)))
  = xs ()
#pop-options

/// ---------------------------------------------------------------------------
/// Fields written
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let set_a0 (st: wst) (v: M.value)
  : Lemma (requires ff_room /\ Some? st.ca) (ensures R.heq (M.set_field (mk st) xA 0 v) (mk ({ st with a0 = v })))
  = xs ()

let set_a1 (st: wst) (v: M.value)
  : Lemma (requires ff_room /\ Some? st.ca) (ensures R.heq (M.set_field (mk st) xA 1 v) (mk ({ st with a1 = v })))
  = xs ()

let set_d0 (st: wst) (v: M.value)
  : Lemma (requires ff_room /\ Some? st.cd) (ensures R.heq (M.set_field (mk st) xD 0 v) (mk ({ st with d0 = v })))
  = xs ()
#pop-options

let set_field_heq (h h': M.mheap) (o i: nat) (v: M.value)
  : Lemma (requires R.heq h h') (ensures R.heq (M.set_field h o i v) (M.set_field h' o i v))
  = ()

/// ---------------------------------------------------------------------------
/// The sweep frees C
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let free_C (st: wst)
  : Lemma (requires ff_room /\ Some? st.cc)
          (ensures R.heq (FWS.freed (mk st) xC)
                         (mk ({ st with cc = Some M.Blue; c0 = st.lk; lk = M.VPtr (M.Major xC) })))
  = xs ()
#pop-options

/// ---------------------------------------------------------------------------
/// Reading the closed form
/// ---------------------------------------------------------------------------

let blk (st: wst) (x: nat)
  : Lemma (requires ff_room /\ present st x) (ensures M.is_block (mk st) x /\ M.resolve (mk st) x == Some x)
  = xs ()

/// The infix pointer into K resolves to K.
let res_k2 (st: wst)
  : Lemma (requires ff_room /\ Some? st.ck) (ensures M.resolve (mk st) (xK + 2) == Some xK)
  = xs ();
    assert_norm (M.infix_hdr (M.infix_word 2) == Some 2)

/// ---------------------------------------------------------------------------
/// Recolouring, as records
/// ---------------------------------------------------------------------------

let recol_A (st: wst) (c: M.colour) : Lemma (requires ff_room) (ensures recol st xA c == { st with ca = Some c }) = xs ()
let recol_B (st: wst) (c: M.colour) : Lemma (requires ff_room) (ensures recol st xB c == { st with cb = Some c }) = xs ()
let recol_C (st: wst) (c: M.colour) : Lemma (requires ff_room) (ensures recol st xC c == { st with cc = Some c }) = xs ()
let recol_K (st: wst) (c: M.colour) : Lemma (requires ff_room) (ensures recol st xK c == { st with ck = Some c }) = xs ()
let recol_D (st: wst) (c: M.colour) : Lemma (requires ff_room) (ensures recol st xD c == { st with cd = Some c }) = xs ()
let recol_E (st: wst) (c: M.colour) : Lemma (requires ff_room) (ensures recol st xE c == { st with ce = Some c }) = xs ()
let recol_P1 (st: wst) (c: M.colour) : Lemma (requires ff_room) (ensures recol st xP1 c == { st with cp1 = Some c }) = xs ()
let recol_P2 (st: wst) (c: M.colour) : Lemma (requires ff_room) (ensures recol st xP2 c == { st with cp2 = Some c }) = xs ()
let recol_P3 (st: wst) (c: M.colour) : Lemma (requires ff_room) (ensures recol st xP3 c == { st with cp3 = Some c }) = xs ()
let recol_P4 (st: wst) (c: M.colour) : Lemma (requires ff_room) (ensures recol st xP4 c == { st with cp4 = Some c }) = xs ()

/// ---------------------------------------------------------------------------
/// The two promotions of a minor collection
/// ---------------------------------------------------------------------------

/// Two one-field blocks carved from the top of the bottom block: the first
/// (`w1`) at `f - 1`, the second (`w2`) at `f - 3`.
let two (m: M.mheap) (f: nat{7 <= f}) (k1 k2: M.colour) (w1 w2: M.value) : M.mheap =
  M.fill (FWA.split (M.fill (FWA.split m f 1 0 k1) (f - 1) [w1]) (f - 2) 1 0 k2) (f - 3) [w2]

#push-options "--fuel 2 --z3rlimit 40"
let two_view (m: M.mheap) (f: nat{7 <= f}) (k1 k2: M.colour) (w1 w2: M.value)
  : Lemma (let m' = two m f k1 k2 w1 w2 in
           m'.M.size == m.M.size /\
           (forall (x: nat). m'.M.hd x == (if x = 0 then Some (FWA.free_hdr (f - 4))
                                           else if x = f - 1 then Some ({ M.wz = 1; M.tag = 0; M.col = k1 })
                                           else if x = f - 3 then Some ({ M.wz = 1; M.tag = 0; M.col = k2 })
                                           else m.M.hd x)) /\
           (forall (w: nat). m'.M.body w == (if w = f then w1 else if w = f - 2 then w2
                                             else if w = f - 1 || w = f - 3 then M.VInt 0 else m.M.body w)))
  = FWA.split_def m f 1 0 k1;
    FWA.split_def (M.fill (FWA.split m f 1 0 k1) (f - 1) [w1]) (f - 2) 1 0 k2

let promo_hd (st: wst) (f f': nat) (k1 k2: M.colour) (st': wst) (x: nat)
  : Lemma (requires 7 <= f /\ f' == f - 4 /\ st.f == f /\ st'.f == f' /\
                    (forall (y: nat). y <> 0 /\ y <> f - 1 /\ y <> f - 3 ==> mhd st' y == mhd st y) /\
                    mhd st' (f - 1) == Some ({ M.wz = 1; M.tag = 0; M.col = k1 }) /\
                    mhd st' (f - 3) == Some ({ M.wz = 1; M.tag = 0; M.col = k2 }))
          (ensures (two (mk st) f k1 k2 (M.infix_word 2) (M.VPtr (M.Major (xK + 2)))).M.hd x == (mk st').M.hd x)
  = two_view (mk st) f k1 k2 (M.infix_word 2) (M.VPtr (M.Major (xK + 2)))

let promo_bd (st: wst) (f: nat) (k1 k2: M.colour) (st': wst) (w: nat)
  : Lemma (requires 7 <= f /\
                    (forall (u: nat). u <> f /\ u <> f - 2 /\ u <> f - 1 /\ u <> f - 3 ==> mbody st' u == mbody st u) /\
                    mbody st' f == M.infix_word 2 /\ mbody st' (f - 2) == M.VPtr (M.Major (xK + 2)) /\
                    mbody st' (f - 1) == M.VInt 0 /\ mbody st' (f - 3) == M.VInt 0)
          (ensures (two (mk st) f k1 k2 (M.infix_word 2) (M.VPtr (M.Major (xK + 2)))).M.body w == (mk st').M.body w)
  = two_view (mk st) f k1 k2 (M.infix_word 2) (M.VPtr (M.Major (xK + 2)))

let promo_M_facts (st: wst) (k1 k2: M.colour)
  : Lemma (requires ff_room /\ st.f == sub msize 14 /\ st.cp1 == None /\ st.cp2 == None)
          (ensures (let st' = { st with f = sub msize 18; cp1 = Some k1; cp2 = Some k2 } in
                    (forall (y: nat). y <> 0 /\ y <> st.f - 1 /\ y <> st.f - 3 ==> mhd st' y == mhd st y) /\
                    mhd st' (st.f - 1) == Some ({ M.wz = 1; M.tag = 0; M.col = k1 }) /\
                    mhd st' (st.f - 3) == Some ({ M.wz = 1; M.tag = 0; M.col = k2 }) /\
                    (forall (u: nat). u <> st.f /\ u <> st.f - 2 /\ u <> st.f - 1 /\ u <> st.f - 3 ==> mbody st' u == mbody st u) /\
                    mbody st' st.f == M.infix_word 2 /\ mbody st' (st.f - 2) == M.VPtr (M.Major (xK + 2)) /\
                    mbody st' (st.f - 1) == M.VInt 0 /\ mbody st' (st.f - 3) == M.VInt 0))
  = xs ()

let promo_S_facts (st: wst) (k1 k2: M.colour)
  : Lemma (requires ff_room /\ st.f == sub msize 20 /\ st.cp3 == None /\ st.cp4 == None)
          (ensures (let st' = { st with f = sub msize 24; cp3 = Some k1; cp4 = Some k2 } in
                    (forall (y: nat). y <> 0 /\ y <> st.f - 1 /\ y <> st.f - 3 ==> mhd st' y == mhd st y) /\
                    mhd st' (st.f - 1) == Some ({ M.wz = 1; M.tag = 0; M.col = k1 }) /\
                    mhd st' (st.f - 3) == Some ({ M.wz = 1; M.tag = 0; M.col = k2 }) /\
                    (forall (u: nat). u <> st.f /\ u <> st.f - 2 /\ u <> st.f - 1 /\ u <> st.f - 3 ==> mbody st' u == mbody st u) /\
                    mbody st' st.f == M.infix_word 2 /\ mbody st' (st.f - 2) == M.VPtr (M.Major (xK + 2)) /\
                    mbody st' (st.f - 1) == M.VInt 0 /\ mbody st' (st.f - 3) == M.VInt 0))
  = xs ()

let promo_M (st: wst) (k1 k2: M.colour)
  : Lemma (requires ff_room /\ st.f == sub msize 14 /\ st.cp1 == None /\ st.cp2 == None)
          (ensures R.heq (two (mk st) st.f k1 k2 (M.infix_word 2) (M.VPtr (M.Major (xK + 2))))
                         (mk ({ st with f = sub msize 18; cp1 = Some k1; cp2 = Some k2 })))
  = let st' = { st with f = sub msize 18; cp1 = Some k1; cp2 = Some k2 } in
    xs ();
    promo_M_facts st k1 k2;
    FStar.Classical.forall_intro (promo_hd st st.f (st.f - 4) k1 k2 st');
    FStar.Classical.forall_intro (promo_bd st st.f k1 k2 st');
    two_view (mk st) st.f k1 k2 (M.infix_word 2) (M.VPtr (M.Major (xK + 2)))

let promo_S (st: wst) (k1 k2: M.colour)
  : Lemma (requires ff_room /\ st.f == sub msize 20 /\ st.cp3 == None /\ st.cp4 == None)
          (ensures R.heq (two (mk st) st.f k1 k2 (M.infix_word 2) (M.VPtr (M.Major (xK + 2))))
                         (mk ({ st with f = sub msize 24; cp3 = Some k1; cp4 = Some k2 })))
  = let st' = { st with f = sub msize 24; cp3 = Some k1; cp4 = Some k2 } in
    xs ();
    promo_S_facts st k1 k2;
    FStar.Classical.forall_intro (promo_hd st st.f (st.f - 4) k1 k2 st');
    FStar.Classical.forall_intro (promo_bd st st.f k1 k2 st');
    two_view (mk st) st.f k1 k2 (M.infix_word 2) (M.VPtr (M.Major (xK + 2)))
#pop-options
