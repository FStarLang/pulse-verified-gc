/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWMark - the mark on the witness heaps, and reachability
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  On the first-fit witness heaps (`FFWState.mk st`):
///   - the start greys the blocks the roots point to (`start_eq`);
///   - a slice blackens the lowest grey block and greys its white targets
///     (`slice_leaf` for B and K, whose fields are words of bytes; `slice_A`
///     for A, whose second field is an infix pointer into K);
///   - at the cycle's start, A, B and K are reachable and C is not
///     (`reach_set`, `reach_A`, `reach_B`, `reach_K`).

module GC.Spec.Top.FFWMark

open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.FFWState
open GC.Spec.Top.FFWOps
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module TM = GC.Spec.Top.ToyMark
module TC = GC.Spec.Top.ToyComps

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Edges
/// ---------------------------------------------------------------------------

/// A field of bytes points nowhere.
let pm_int (h: M.mheap) (n: int) (x: nat) : Lemma (TM.points_major h (M.VInt n) x == false) = ()

#push-options "--fuel 3 --z3rlimit 40"
let edge_A (st: wst) (x: nat)
  : Lemma (requires ff_room /\ Some? st.ca)
          (ensures TM.edge_b (mk st) xA x == (TM.points_major (mk st) st.a0 x || TM.points_major (mk st) st.a1 x))
  = xs ()

let edge_B (st: wst) (x: nat)
  : Lemma (requires ff_room /\ Some? st.cb) (ensures TM.edge_b (mk st) xB x == false)
  = xs ()

#push-options "--fuel 4"
let edge_K (st: wst) (x: nat)
  : Lemma (requires ff_room /\ Some? st.ck) (ensures TM.edge_b (mk st) xK x == false)
  = xs ();
    assert_norm (M.infix_word 2 == M.VInt 2297)
#pop-options
#pop-options

let pm_ptr (st: wst) (a x: nat)
  : Lemma (requires ff_room /\ present st a)
          (ensures TM.points_major (mk st) (M.VPtr (M.Major a)) x == (x = a))
  = blk st a

let pm_k2 (st: wst) (x: nat)
  : Lemma (requires ff_room /\ Some? st.ck)
          (ensures TM.points_major (mk st) (M.VPtr (M.Major (xK + 2))) x == (x = xK))
  = res_k2 st

/// ---------------------------------------------------------------------------
/// Slices
/// ---------------------------------------------------------------------------

/// A block whose fields point nowhere turns black.
#push-options "--z3rlimit 40"
let slice_leaf (st: wst) (t: nat)
  : Lemma (requires ff_room /\ present st t /\ (forall (x: nat). TM.edge_b (mk st) t x == false))
          (ensures R.heq (TM.tmslice_with (mk st) t) (mk (recol st t M.Black)))
  = recol_eq st t M.Black
#pop-options

let slice_B (st: wst)
  : Lemma (requires ff_room /\ Some? st.cb) (ensures R.heq (TM.tmslice_with (mk st) xB) (mk (recol st xB M.Black)))
  = xs ();
    FStar.Classical.forall_intro (FStar.Classical.move_requires (edge_B st));
    slice_leaf st xB

let slice_K (st: wst)
  : Lemma (requires ff_room /\ Some? st.ck) (ensures R.heq (TM.tmslice_with (mk st) xK) (mk (recol st xK M.Black)))
  = xs ();
    FStar.Classical.forall_intro (FStar.Classical.move_requires (edge_K st));
    slice_leaf st xK

/// A: its targets are K (white, greyed) and, when its first field points
/// to B, B (not white).
#push-options "--z3rlimit 40"
let slice_A_edge (st: wst) (x: nat)
  : Lemma (requires ff_room /\ Some? st.ca /\ Some? st.cb /\ st.ck == Some M.White /\
                    st.a1 == M.VPtr (M.Major (xK + 2)) /\
                    (st.a0 == M.VInt 1 \/ (st.a0 == M.VPtr (M.Major xB) /\ st.cb <> Some M.White)))
          (ensures TM.edge_b (mk st) xA x == (x = xK || (st.a0 = M.VPtr (M.Major xB) && x = xB)))
  = xs ();
    edge_A st x;
    pm_k2 st x;
    if st.a0 = M.VPtr (M.Major xB) then pm_ptr st xB x

let slice_A (st: wst)
  : Lemma (requires ff_room /\ Some? st.ca /\ Some? st.cb /\ st.ck == Some M.White /\
                    st.a1 == M.VPtr (M.Major (xK + 2)) /\
                    (st.a0 == M.VInt 1 \/ (st.a0 == M.VPtr (M.Major xB) /\ st.cb <> Some M.White)))
          (ensures R.heq (TM.tmslice_with (mk st) xA) (mk (recol (recol st xA M.Black) xK M.Grey)))
  = xs ();
    FStar.Classical.forall_intro (FStar.Classical.move_requires (slice_A_edge st))
#pop-options

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

let young_none (w: M.world) (x: nat)
  : Lemma (requires (forall (y: nat). w.M.yng.M.hd y == None)) (ensures TM.young_b w x == false)
  = TM.young_b_iff w x

/// The roots `[B; A]` (sequential) or `[A]` (incremental) are greyed.
#push-options "--fuel 3 --z3rlimit 40"
let start_two (st: wst) (y: M.mheap) (x: nat)
  : Lemma (requires ff_room /\ st.ca == Some M.White /\ st.cb == Some M.White /\ (forall (j: nat). y.M.hd j == None))
          (ensures TM.outside_b ({ M.maj = mk st; M.yng = y; M.roots = [M.VPtr (M.Major xB); M.VPtr (M.Major xA)]; M.rem = [] }) x
                   == (x = xA || x = xB))
  = young_none ({ M.maj = mk st; M.yng = y; M.roots = [M.VPtr (M.Major xB); M.VPtr (M.Major xA)]; M.rem = [] }) x;
    pm_ptr st xA x; pm_ptr st xB x

let start_one (st: wst) (y: M.mheap) (x: nat)
  : Lemma (requires ff_room /\ st.ca == Some M.White /\ (forall (j: nat). y.M.hd j == None))
          (ensures TM.outside_b ({ M.maj = mk st; M.yng = y; M.roots = [M.VPtr (M.Major xA)]; M.rem = [] }) x == (x = xA))
  = young_none ({ M.maj = mk st; M.yng = y; M.roots = [M.VPtr (M.Major xA)]; M.rem = [] }) x;
    pm_ptr st xA x
#pop-options

#push-options "--z3rlimit 40"
let start_seq (st: wst) (y: M.mheap)
  : Lemma (requires ff_room /\ st.ca == Some M.White /\ st.cb == Some M.White /\ (forall (j: nat). y.M.hd j == None))
          (ensures R.heq (TM.tmstart ({ M.maj = mk st; M.yng = y; M.roots = [M.VPtr (M.Major xB); M.VPtr (M.Major xA)]; M.rem = [] }))
                         (mk (recol (recol st xA M.Grey) xB M.Grey)))
  = xs ();
    FStar.Classical.forall_intro (FStar.Classical.move_requires (start_two st y))

let start_inc (st: wst) (y: M.mheap)
  : Lemma (requires ff_room /\ st.ca == Some M.White /\ (forall (j: nat). y.M.hd j == None))
          (ensures R.heq (TM.tmstart ({ M.maj = mk st; M.yng = y; M.roots = [M.VPtr (M.Major xA)]; M.rem = [] }))
                         (mk (recol st xA M.Grey)))
  = xs ();
    FStar.Classical.forall_intro (FStar.Classical.move_requires (start_one st y))
#pop-options

/// ---------------------------------------------------------------------------
/// What a slice needs of the block it scans
/// ---------------------------------------------------------------------------

let no_infix (st: wst) : Lemma (requires ff_room) (ensures GC.Spec.Top.ByteWrite.no_infix_tags (mk st))
  = xs ()

let scan_B (st: wst)
  : Lemma (requires ff_room /\ Some? st.cb) (ensures GC.Spec.Top.ByteMark.scan_ok (mk st) xB)
  = xs (); no_infix st

#push-options "--z3rlimit 40"
let scan_K (st: wst)
  : Lemma (requires ff_room /\ Some? st.ck) (ensures GC.Spec.Top.ByteMark.scan_ok (mk st) xK)
  = xs (); no_infix st;
    assert_norm (M.infix_word 2 == M.VInt 2297)

let scan_A (st: wst)
  : Lemma (requires ff_room /\ Some? st.ca /\ Some? st.ck /\ st.a1 == M.VPtr (M.Major (xK + 2)) /\
                    (st.a0 == M.VInt 1 \/ (st.a0 == M.VPtr (M.Major xB) /\ Some? st.cb)))
          (ensures GC.Spec.Top.ByteMark.scan_ok (mk st) xA)
  = xs (); no_infix st;
    res_k2 st;
    if Some? st.cb then blk st xB
#pop-options
