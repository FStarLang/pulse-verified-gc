/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWOk - the witness heaps stay representable
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  The closed forms the witness runs move to by recolouring,
/// writing a field or freeing C are again heaps a byte heap can represent
/// (`brep_ok`, canonical): each is a same-shape update of the last
/// (GC.Spec.Top.FFWModel), read in closed form (GC.Spec.Top.FFWOps).

module GC.Spec.Top.FFWOk

open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.FFWModel
open GC.Spec.Top.FFWState
open GC.Spec.Top.FFWOps
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module FWS = GC.Spec.Top.FFWSweep
module FWStep = GC.Spec.Top.FFWStep

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let ok (st: wst) : prop = okm (mk st)

let recol_ok (st: wst) (x: nat) (c: M.colour)
  : Lemma (requires ff_room /\ ok st /\ present st x) (ensures ok (recol st x c))
  = reveal_opaque (`%okm) okm;
    recol_shape (mk st) x c;
    same_shape_ok (mk st) (M.set_col (mk st) x c);
    recol_eq st x c;
    FWStep.brep_of_heq (M.set_col (mk st) x c) (mk (recol st x c))

let field_ok (st: wst) (o i: nat) (v: M.value) (st': wst)
  : Lemma (requires ok st /\ M.is_block (mk st) o /\ i < M.wz_of (mk st) o /\ storable_w v /\
                    R.heq (M.set_field (mk st) o i v) (mk st'))
          (ensures ok st')
  = reveal_opaque (`%okm) okm;
    assert (M.covers (mk st) o (o + 1 + i));
    setb_shape (mk st) (o + 1 + i) v;
    same_shape_ok (mk st) (setb (mk st) (o + 1 + i) v);
    assert (R.heq (setb (mk st) (o + 1 + i) v) (M.set_field (mk st) o i v));
    FWStep.brep_of_heq (setb (mk st) (o + 1 + i) v) (mk st')

let a0_ok (st: wst) (v: M.value)
  : Lemma (requires ff_room /\ ok st /\ Some? st.ca /\ storable_w v) (ensures ok ({ st with a0 = v }))
  = reveal_opaque (`%okm) okm;
    xs (); blk st xA; set_a0 st v; field_ok st xA 0 v ({ st with a0 = v })

let a1_ok (st: wst) (v: M.value)
  : Lemma (requires ff_room /\ ok st /\ Some? st.ca /\ storable_w v) (ensures ok ({ st with a1 = v }))
  = reveal_opaque (`%okm) okm;
    xs (); blk st xA; set_a1 st v; field_ok st xA 1 v ({ st with a1 = v })

let d0_ok (st: wst) (v: M.value)
  : Lemma (requires ff_room /\ ok st /\ Some? st.cd /\ storable_w v) (ensures ok ({ st with d0 = v }))
  = reveal_opaque (`%okm) okm;
    xs (); blk st xD; set_d0 st v; field_ok st xD 0 v ({ st with d0 = v })

/// Freeing C.
#push-options "--z3rlimit 40"
let freed_ok (st: wst)
  : Lemma (requires ff_room /\ ok st /\ Some? st.cc /\ st.f >= 1)
          (ensures ok ({ st with cc = Some M.Blue; c0 = st.lk; lk = M.VPtr (M.Major xC) }))
  = reveal_opaque (`%okm) okm;
    xs ();
    let m = mk st in
    blk st xC;
    brep_block m xC;
    rehd_shape m xC ({ M.wz = M.wz_of m xC; M.tag = 0; M.col = M.Blue });
    same_shape_ok m (FWS.freed1 m xC);
    assert (M.covers (FWS.freed1 m xC) xC (xC + 1));
    brep_size m; brep_block m 0;
    assert (M.covers m 0 1);
    brep_store m 1;
    setb_shape (FWS.freed1 m xC) (xC + 1) (m.M.body 1);
    same_shape_ok (FWS.freed1 m xC) (FWS.freed2 m xC);
    assert (M.covers (FWS.freed2 m xC) 0 1);
    major_storable xC;
    setb_shape (FWS.freed2 m xC) 1 (M.VPtr (M.Major xC));
    same_shape_ok (FWS.freed2 m xC) (FWS.freed m xC);
    free_C st;
    FWStep.brep_of_heq (FWS.freed m xC) (mk ({ st with cc = Some M.Blue; c0 = st.lk; lk = M.VPtr (M.Major xC) }))
#pop-options
