/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWStart - the witness heap when a cycle starts
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  Both first-fit witness runs start their cycle on the same
/// heap, `mk st6`: A (fields: a pointer to B, an infix pointer into K), B, C
/// (a pointer to B), K (a closure, its second field an infix header), every
/// block white, the nursery empty, and roots among A and B.  There:
///   - the reachable blocks are among A, B and K (`reach_S`): C, in use, is
///     unreachable;
///   - the mark's precondition holds (`start_pre`).

module GC.Spec.Top.FFWStart

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
module MK = GC.Spec.Top.FFWMark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let vA : M.value = M.VPtr (M.Major xA)
let vB : M.value = M.VPtr (M.Major xB)
let vK2 : M.value = M.VPtr (M.Major (xK + 2))

/// The heap the cycle starts on.
let st_start (st: wst) : prop =
  st.ca == Some M.White /\ st.cb == Some M.White /\ st.cc == Some M.White /\ st.ck == Some M.White /\
  st.cd == None /\ st.ce == None /\ st.a0 == vB /\ st.a1 == vK2

let sS (x: nat) : prop = x == xA \/ x == xB \/ x == xK

let roots_ok (rs: list M.value) : prop = forall (v: M.value). L.memP v rs ==> v == vA \/ v == vB

let empty_y (y: M.mheap) : prop = forall (j: nat). y.M.hd j == None

let wst_w (st: wst) (y: M.mheap) (rs: list M.value) : M.world = { M.maj = mk st; M.yng = y; M.roots = rs; M.rem = [] }

let out_S (st: wst) (y: M.mheap) (rs: list M.value) (x: nat)
  : Lemma (requires ff_room /\ st_start st /\ roots_ok rs /\ empty_y y)
          (ensures M.outside_ref (wst_w st y rs) x ==> sS x)
  = let w = wst_w st y rs in
    TM.outside_b_iff w x;
    TM.root_b_iff (mk st) rs x;
    MK.young_none w x;
    let one (a: nat) : Lemma (L.memP (M.VPtr (M.Major a)) rs /\ M.resolve (mk st) a == Some x ==> sS x)
      = if FStar.IndefiniteDescription.strong_excluded_middle (L.memP (M.VPtr (M.Major a)) rs) then begin
          assert (a == xA \/ a == xB);
          blk st a
        end in
    FStar.Classical.forall_intro one

let edge_S (st: wst) (x x': nat)
  : Lemma (requires ff_room /\ st_start st /\ sS x)
          (ensures M.major_edge (mk st) x x' ==> sS x')
  = xs ();
    TM.edge_b_iff (mk st) x x';
    if x = xA then begin MK.edge_A st x'; MK.pm_ptr st xB x'; MK.pm_k2 st x' end
    else if x = xB then MK.edge_B st x'
    else MK.edge_K st x'

/// **Reachable blocks are among A, B and K.**
let reach_S (st: wst) (y: M.mheap) (rs: list M.value) (o: nat)
  : Lemma (requires ff_room /\ st_start st /\ roots_ok rs /\ empty_y y /\ M.reachable (wst_w st y rs) o)
          (ensures sS o)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (out_S st y rs));
    FStar.Classical.forall_intro_2 (fun a b -> FStar.Classical.move_requires (edge_S st a) b);
    let r = FStar.IndefiniteDescription.indefinite_description_ghost (M.reach (wst_w st y rs) o) (fun _ -> True) in
    TC.reach_within (wst_w st y rs) sS o r

/// **C is unreachable.**
let c_unreachable (st: wst) (y: M.mheap) (rs: list M.value)
  : Lemma (requires ff_room /\ st_start st /\ roots_ok rs /\ empty_y y) (ensures ~(M.reachable (wst_w st y rs) xC))
  = xs ();
    FStar.Classical.move_requires (reach_S st y rs) xC

let brep_wf (m: M.mheap) : Lemma (requires brep_ok m) (ensures M.well_formed m)
  = reveal_opaque (`%brep_ok) (brep_ok m)

let no_dark1 (st: wst) (o: nat)
  : Lemma (requires ff_room /\ st_start st) (ensures M.is_block (mk st) o ==> not (M.dark (M.col_of (mk st) o)))
  = xs ()

let reach_white (st: wst) (y: M.mheap) (rs: list M.value) (o: nat)
  : Lemma (requires ff_room /\ st_start st /\ roots_ok rs /\ empty_y y)
          (ensures M.reachable (wst_w st y rs) o ==> M.is_block (mk st) o /\ M.col_of (mk st) o == M.White)
  = xs ();
    FStar.Classical.move_requires (reach_S st y rs) o

/// **The mark's precondition.**
let start_pre (st: wst) (y: M.mheap) (rs: list M.value)
  : Lemma (requires ff_room /\ st_start st /\ roots_ok rs /\ empty_y y /\ GC.Spec.Top.FFWModel.okm (mk st))
          (ensures T.mark_start_pre (wst_w st y rs))
  = GC.Spec.Top.FFWModel.okm_def (mk st);
    brep_wf (mk st);
    FStar.Classical.forall_intro (no_dark1 st);
    FStar.Classical.forall_intro (reach_white st y rs)

#push-options "--fuel 3"
let roots_two (_: unit) : Lemma (roots_ok [vB; vA]) = ()
let roots_one (_: unit) : Lemma (roots_ok [vA]) = ()
#pop-options

let empty_ywords (_: unit) : Lemma (empty_y (M.empty_heap ywords)) = ()
