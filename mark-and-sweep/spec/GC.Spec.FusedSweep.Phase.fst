module GC.Spec.FusedSweep.Phase

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FStep = GC.Spec.FusedSweep.Step

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Opening and closing the clauses
/// ---------------------------------------------------------------------------

let keeps_live_elim g0 g1 p = reveal_opaque (`%keeps_live) (keeps_live g0 g1)

let keeps_live_intro g0 g1 pf =
  reveal_opaque (`%keeps_live) (keeps_live g0 g1);
  FStar.Classical.forall_intro (FStar.Classical.move_requires pf)

let no_new_garbage_elim g0 g1 p = reveal_opaque (`%no_new_garbage) (no_new_garbage g0 g1)

let no_new_garbage_intro g0 g1 pf =
  reveal_opaque (`%no_new_garbage) (no_new_garbage g0 g1);
  FStar.Classical.forall_intro (FStar.Classical.move_requires pf)

let front_carved_elim g0 g1 c p = reveal_opaque (`%front_carved) (front_carved g0 g1 c)

let front_carved_intro g0 g1 c pf =
  reveal_opaque (`%front_carved) (front_carved g0 g1 c);
  FStar.Classical.forall_intro (FStar.Classical.move_requires pf)

let front_carved_mono g0 g1 c c' =
  front_carved_intro g0 g1 c' (fun p -> front_carved_elim g0 g1 c p)

/// ---------------------------------------------------------------------------
/// The reference heap marking left
/// ---------------------------------------------------------------------------

let ref_ok_refl (g0: heap) (fp: U64.t) (c: nat)
  : Lemma (requires sweep_pre g0 fp) (ensures ref_ok g0 g0 c)
  = wf_parts ();
    keeps_live_intro g0 g0 (fun _ -> ());
    no_new_garbage_intro g0 g0 (fun _ -> ());
    front_carved_intro g0 g0 c (fun _ -> ())

/// ---------------------------------------------------------------------------
/// Start, step, and the stop-the-world case
/// ---------------------------------------------------------------------------

let sweeping_start g0 fp =
  ref_ok_refl g0 fp (U64.v sweep_start.cursor);
  sweep_start_inv g0 fp

#push-options "--ifuel 1"
let sweeping_step g0 g1 g fp st =
  FStep.sweep_step_inv g1 g fp st;
  let (g', fp', st') = sweep_step g fp st in
  front_carved_mono g0 g1 (U64.v st.cursor) (U64.v st'.cursor)
#pop-options

let sweeping_stw g0 g fp0 fp st = ref_ok_refl g0 fp0 (U64.v st.cursor)

/// ---------------------------------------------------------------------------
/// In front of the cursor
/// ---------------------------------------------------------------------------

/// Two heaps whose walks both reach `c` and that agree from `c` on have the same
/// blocks from `c` on, with the same headers.
#push-options "--z3rlimit 30"
let front_pos (g1 g: heap) (c: nat) (p: hp_addr)
  : Lemma (requires W.reaches g1 zero_addr c /\ W.reaches g zero_addr c /\
                    front_same g1 g c /\ U64.v p >= c)
          (ensures (pos g p <==> pos g1 p) /\ read_word g p == read_word g1 p /\
                   W.bnext g p == W.bnext g1 p)
  = W.reaches_bounds g zero_addr c;
    front_same_elim g1 g c p;
    let ca = mk_hp_addr c in
    let fr (w: hp_addr) : Lemma (requires U64.v w >= U64.v ca) (ensures read_word g w == read_word g1 w)
      = front_same_elim g1 g c w in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
    W.walk_frame_from g1 g ca;
    if W.reaches g zero_addr (U64.v p) then begin
      W.reaches_det g zero_addr ca (U64.v p);
      W.reaches_trans g1 zero_addr ca (U64.v p)
    end;
    if W.reaches g1 zero_addr (U64.v p) then begin
      W.reaches_det g1 zero_addr ca (U64.v p);
      W.reaches_trans g zero_addr ca (U64.v p)
    end
#pop-options

let front_same_front_ok g0 g c =
  let aux (p: hp_addr)
    : Lemma (requires pos g p /\ U64.v p >= c)
            (ensures pos g0 p /\ read_word g p == read_word g0 p)
    = front_pos g0 g c p
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#push-options "--z3rlimit 30"
let sweeping_front_ok g0 g1 g fp st =
  sweep_inv_elim g1 g fp st;
  let c = U64.v st.cursor in
  let one (p: hp_addr)
    : Lemma (requires pos g p /\ U64.v p >= c)
            (ensures ((pos g0 p /\ read_word g p == read_word g0 p) \/
                      ((black_at g p \/ blue_at g p) /\ carved g0 g p)) /\
                     (not (black_at g p) /\ not (blue_at g p) ==>
                        pos g0 p /\ read_word g p == read_word g0 p))
    = front_pos g1 g c p;
      front_carved_elim g0 g1 c p;
      if not (black_at g1 p) && not (blue_at g1 p) then no_new_garbage_elim g0 g1 p
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options
