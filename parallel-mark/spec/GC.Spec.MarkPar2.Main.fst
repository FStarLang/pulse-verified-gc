/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Main — the main thread's step, and setup, keep the
/// invariant
///
/// `main_inv`: at the stop barrier (every worker stopped) the counter is 0
/// and every stack and inbox is empty.  With no flag set the step only marks
/// the run finished.  Otherwise the fix-up walk (`GC.Spec.MarkPar2.Fix`)
/// leaves every grey object on its owner's stack or overflow_main set, and
/// no black object pointing to a white one; whether it then finishes (it
/// pushed nothing) or starts a round, the invariant holds.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Main

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Lib.Header
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar.Recolour
open GC.Spec.MarkPar2.Model
open GC.Spec.MarkPar2.Inv
open GC.Spec.MarkPar2.Fix

module HeapGraph = GC.Spec.HeapGraph
module M1 = GC.Spec.MarkPar.Model
module I1 = GC.Spec.MarkPar.Inv
module Own = GC.Spec.MarkPar.Own
module LS = GC.Spec.MarkPar2.Lists
module U = GC.Spec.MarkPar2.Upd

/// ---------------------------------------------------------------------------
/// At the stop barrier
/// ---------------------------------------------------------------------------

let stopped_empty (k: cfg) (g: heap) (s: state)
  : Lemma (requires own_ok k g s /\ count_ok s /\ all_stopped s.wks)
          (ensures s.count == 0 /\
                   (forall (i: nat) (w: wk). wk_of s i == Some w ==>
                      w.stack == [] /\ w.inbox == [] /\ w.pc == Stopped))
  = U.own_len k g s;
    reveal_opaque (`%count_ok) (count_ok s);
    Own.nth_lt s.wks 0;
    let Some w0 = M1.nth s.wks 0 in
    LS.all_stopped_nth s.wks 0 w0;
    assert (wk_of s 0 == Some w0);
    assert (s.count == 0);
    let aux (i: nat) (w: wk)
      : Lemma (requires wk_of s i == Some w) (ensures w.stack == [] /\ w.inbox == [] /\ w.pc == Stopped)
      = LS.all_stopped_nth s.wks i w;
        LS.counted_zero s.wks i w
    in
    FStar.Classical.forall_intro_2 (fun i w -> FStar.Classical.move_requires (aux i) w)

let no_ovf (ws: list wk)
  : Lemma (requires forall (i: nat) (w: wk). M1.nth ws i == Some w ==> w.ovf == false)
          (ensures any_ovf ws == false)
  = FStar.Classical.move_requires LS.any_ovf_elim ws

/// ---------------------------------------------------------------------------
/// No flag set: done
/// ---------------------------------------------------------------------------

let fin (s: state) : state = { s with finished = true }

let own_fin (k: cfg) (g: heap) (s: state) : Lemma (requires own_ok k g s) (ensures own_ok k g (fin s)) =
  reveal_opaque (`%own_ok) (own_ok k g s); reveal_opaque (`%own_ok) (own_ok k g (fin s))
let count_fin (s: state) : Lemma (requires count_ok s) (ensures count_ok (fin s)) =
  reveal_opaque (`%count_ok) (count_ok s); reveal_opaque (`%count_ok) (count_ok (fin s));
  assert ((fin s).wks == s.wks /\ (fin s).count == s.count);
  assert (forall (i: nat). wk_of (fin s) i == wk_of s i)
let grey_fin (k: cfg) (g: heap) (s: state) : Lemma (requires grey_ok k g s) (ensures grey_ok k g (fin s)) =
  reveal_opaque (`%grey_ok) (grey_ok k g s); reveal_opaque (`%grey_ok) (grey_ok k g (fin s));
  assert ((fin s).wks == s.wks /\ (fin s).heap == s.heap /\ flagged (fin s) == flagged s);
  assert (forall (i: nat). stack_of (fin s) i == stack_of s i)
let sound_fin (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires sound g roots s) (ensures sound g roots (fin s)) =
  reveal_opaque (`%sound) (sound g roots s); reveal_opaque (`%sound) (sound g roots (fin s));
  assert ((fin s).wks == s.wks /\ (fin s).heap == s.heap);
  assert (forall (i: nat) (v: obj_addr). holds (fin s) i v <==> holds s i v)
let roots_fin (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires roots_ok g roots s) (ensures roots_ok g roots (fin s)) =
  reveal_opaque (`%roots_ok) (roots_ok g roots s); reveal_opaque (`%roots_ok) (roots_ok g roots (fin s))
let fin_fin (s: state)
  : Lemma (requires ~(flagged s) /\ all_stopped s.wks /\ s.count == 0) (ensures fin_ok (fin s)) =
  reveal_opaque (`%fin_ok) (fin_ok (fin s))
let black_fin (k: cfg) (g: heap) (s: state)
  : Lemma (requires black_ok k g s) (ensures black_ok k g (fin s)) =
  let kp () : Lemma (keeps k g s (fin s)) = () in
  kp ();
  black_keeps k g s (fin s) None

let main_done (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires ctx k g roots /\ inv k g roots s /\ ~s.finished /\ all_stopped s.wks /\
                    ~(flagged s))
          (ensures inv k g roots (main_step k s))
  = assert (main_step k s == fin s);
    stopped_empty k g s;
    own_fin k g s; count_fin s; grey_fin k g s; sound_fin g roots s; roots_fin g roots s;
    fin_fin s; black_fin k g s

/// ---------------------------------------------------------------------------
/// The walk, from start to end
/// ---------------------------------------------------------------------------

let start_fx (s: state) : fx =
  { fh = s.heap; fws = clear_ovf s.wks; fom = false; fn = 0 }

/// The records the walk starts from: stopped, empty, flags cleared.
let start_recs (k: cfg) (g: heap) (s: state)
  : Lemma (requires own_ok k g s /\ count_ok s /\ all_stopped s.wks)
          (ensures (let f = start_fx s in
                    L.length f.fws == nr k /\ f.fn == counted f.fws /\
                    (forall (i: nat) (w: wk). fwk f i == Some w ==> wrec_ok k g f.fh i w) /\
                    (forall (i: nat). fstack f i == [])))
  = stopped_empty k g s;
    U.own_len k g s;
    LS.length_clear_ovf s.wks;
    LS.counted_clear_ovf s.wks;
    reveal_opaque (`%count_ok) (count_ok s);
    let aux (i: nat) : Lemma ((match fwk (start_fx s) i with
                               | Some w -> wrec_ok k g s.heap i w | None -> True) /\
                              fstack (start_fx s) i == []) =
      LS.nth_clear_ovf s.wks i;
      match M1.nth s.wks i with
      | Some w -> assert (wk_of s i == Some w); assert (w.stack == [] /\ w.inbox == [] /\ w.pc == Stopped)
      | None -> ()
    in
    FStar.Classical.forall_intro aux

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let wbase_start (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires inv k g roots s /\ all_stopped s.wks)
          (ensures wbase k g roots (start_fx s))
  = start_recs k g s;
    U.own_heap k g s;
    reveal_opaque (`%sound) (sound g roots s);
    reveal_opaque (`%roots_ok) (roots_ok g roots s);
    reveal_opaque (`%wbase) (wbase k g roots (start_fx s))
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let wvis_start (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires inv k g roots s /\ all_stopped s.wks)
          (ensures wvis k g (start_fx s) (objs_list s.heap) (U64.v zero_addr))
  = start_recs k g s;
    U.own_heap k g s;
    LS.objs_list_above s.heap;
    FStar.Classical.forall_intro (LS.objs_list_mem s.heap);
    reveal_opaque (`%wvis) (wvis k g (start_fx s) (objs_list s.heap) (U64.v zero_addr))
#pop-options

let walk_start (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires ctx k g roots /\ inv k g roots s /\ all_stopped s.wks)
          (ensures wbase k g roots (start_fx s) /\
                   wvis k g (start_fx s) (objs_list s.heap) (U64.v zero_addr))
  = wbase_start k g roots s; wvis_start k g roots s

let walk_end (k: cfg) (g: heap) (roots: list obj_addr) (f: fx)
  : Lemma (requires exists (lo: int). wvis k g f [] lo)
          (ensures (forall (x: obj_addr). Seq.mem x (objs g) /\ is_gray x f.fh ==>
                      L.memP x (fstack f (own k x)) \/ f.fom) /\
                   (forall (x: obj_addr) (j: U64.t{U64.v j >= 1}).
                      I1.is_field g x j /\ is_black x f.fh ==>
                      ~(is_white (I1.field_target g x j) f.fh)))
  = let lo = FStar.IndefiniteDescription.indefinite_description_ghost int (fun lo -> wvis k g f [] lo) in
    reveal_opaque (`%wvis) (wvis k g f [] lo)

/// ---------------------------------------------------------------------------
/// The two ends of a fix-up
/// ---------------------------------------------------------------------------

/// What the walk leaves, as the two cases use it.
let walked (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (f: fx) : prop =
  wbase k g roots f /\
  (forall (x: obj_addr). Seq.mem x (objs g) /\ is_gray x f.fh ==>
     L.memP x (fstack f (own k x)) \/ f.fom) /\
  (forall (x: obj_addr) (j: U64.t{U64.v j >= 1}).
     I1.is_field g x j /\ is_black x f.fh ==> ~(is_white (I1.field_target g x j) f.fh)) /\
  ~s.finished /\ s.count == 0

let walked_black (k: cfg) (g: heap) (s': state) (f: fx)
  : Lemma (requires s'.heap == f.fh /\
                    (forall (x: obj_addr) (j: U64.t{U64.v j >= 1}).
                       I1.is_field g x j /\ is_black x f.fh ==> ~(is_white (I1.field_target g x j) f.fh)))
          (ensures black_ok k g s')
  = reveal_opaque (`%black_ok_but) (black_ok_but k g s' None)

/// The records after the walk, as the next state holds them: the walk's
/// stacks, empty inboxes, clear flags, stopped or at the top of the loop.
let like1 (k: cfg) (g: heap) (f: fx) (ws: list wk) (i: nat) : prop =
  match M1.nth ws i with
  | Some w -> w.inbox == [] /\ w.ovf == false /\ (w.pc == Stopped \/ w.pc == Loop) /\
             stack_ok k g f.fh i w.stack /\ w.stack == fstack f i
  | None -> True

[@@"opaque_to_smt"]
let wks_like (k: cfg) (g: heap) (f: fx) (ws: list wk) : prop =
  L.length ws == nr k /\ counted ws == f.fn /\ (forall (i: nat). like1 k g f ws i)

/// The record facts of wbase, without the rest.
let wbase_recs (k: cfg) (g: heap) (roots: list obj_addr) (f: fx)
  : Lemma (requires wbase k g roots f)
          (ensures L.length f.fws == nr k /\ counted f.fws == f.fn /\
                   (forall (i: nat) (w: wk). fwk f i == Some w ==> wrec_ok k g f.fh i w))
  = reveal_opaque (`%wbase) (wbase k g roots f)

let like_walk (k: cfg) (g: heap) (roots: list obj_addr) (f: fx)
  : Lemma (requires wbase k g roots f) (ensures wks_like k g f f.fws)
  = wbase_recs k g roots f;
    reveal_opaque (`%wks_like) (wks_like k g f f.fws);
    let aux (i: nat) : Lemma (like1 k g f f.fws i) =
      match M1.nth f.fws i with
      | Some w -> assert (fwk f i == Some w); assert (wrec_ok k g f.fh i w)
      | None -> ()
    in
    FStar.Classical.forall_intro aux

/// One record of the walk, as wks_like gives it.
let like_at (k: cfg) (g: heap) (f: fx) (ws: list wk) (i: nat) (w: wk)
  : Lemma (requires wks_like k g f ws /\ M1.nth ws i == Some w)
          (ensures w.inbox == [] /\ w.ovf == false /\ (w.pc == Stopped \/ w.pc == Loop) /\
                   stack_ok k g f.fh i w.stack /\ w.stack == fstack f i /\ held w.pc == 0)
  = reveal_opaque (`%wks_like) (wks_like k g f ws);
    assert (like1 k g f ws i)

let like_restart (k: cfg) (g: heap) (roots: list obj_addr) (f: fx)
  : Lemma (requires wbase k g roots f) (ensures wks_like k g f (restart f.fws))
  = like_walk k g roots f;
    reveal_opaque (`%wks_like) (wks_like k g f f.fws);
    reveal_opaque (`%wks_like) (wks_like k g f (restart f.fws));
    LS.length_restart f.fws;
    introduce forall (i: nat) (w: wk). M1.nth f.fws i == Some w ==> held w.pc == 0
    with introduce _ ==> _ with like_at k g f f.fws i w;
    LS.counted_restart f.fws;
    let aux (i: nat) : Lemma (like1 k g f (restart f.fws) i) =
      LS.nth_restart f.fws i;
      match M1.nth f.fws i with
      | Some w0 -> like_at k g f f.fws i w0
      | None -> ()
    in
    FStar.Classical.forall_intro aux

let like_flagged (k: cfg) (g: heap) (f: fx) (s': state)
  : Lemma (requires wks_like k g f s'.wks /\ s'.ovf_main == f.fom)
          (ensures flagged s' == f.fom)
  = reveal_opaque (`%wks_like) (wks_like k g f s'.wks);
    no_ovf s'.wks

let like_own (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (s': state)
  : Lemma (requires wbase k g roots f /\ wks_like k g f s'.wks /\ s'.heap == f.fh)
          (ensures own_ok k g s')
  = reveal_opaque (`%wks_like) (wks_like k g f s'.wks);
    reveal_opaque (`%wbase) (wbase k g roots f);
    reveal_opaque (`%own_ok) (own_ok k g s')

let like_grey (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (f: fx) (s': state)
  : Lemma (requires walked k g roots s f /\ wks_like k g f s'.wks /\ s'.heap == f.fh /\
                    s'.ovf_main == f.fom)
          (ensures grey_ok k g s')
  = reveal_opaque (`%wks_like) (wks_like k g f s'.wks);
    like_flagged k g f s';
    reveal_opaque (`%grey_ok) (grey_ok k g s');
    wbase_recs k g roots f;
    let st (i: nat) : Lemma (stack_of s' i == fstack f i) =
      assert (like1 k g f s'.wks i);
      Own.nth_lt s'.wks i; Own.nth_lt f.fws i in
    FStar.Classical.forall_intro st

let like_sound (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (s': state)
  : Lemma (requires wbase k g roots f /\ wks_like k g f s'.wks /\ s'.heap == f.fh)
          (ensures sound g roots s' /\ roots_ok g roots s')
  = reveal_opaque (`%wks_like) (wks_like k g f s'.wks);
    reveal_opaque (`%wbase) (wbase k g roots f);
    reveal_opaque (`%sound) (sound g roots s');
    reveal_opaque (`%roots_ok) (roots_ok g roots s')

let like_count (k: cfg) (g: heap) (f: fx) (s': state)
  : Lemma (requires wks_like k g f s'.wks /\ s'.count == f.fn /\
                    (f.fn > 0 ==> (forall (i: nat) (w: wk). M1.nth s'.wks i == Some w ==> w.pc == Loop)))
          (ensures count_ok s')
  = reveal_opaque (`%wks_like) (wks_like k g f s'.wks);
    reveal_opaque (`%count_ok) (count_ok s')

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let fix_done (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (f: fx)
  : Lemma (requires walked k g roots s f /\ f.fn == 0)
          (ensures inv k g roots { s with heap = f.fh; wks = f.fws; ovf_main = f.fom; finished = true })
  = let s' = { s with heap = f.fh; wks = f.fws; ovf_main = f.fom; finished = true } in
    reveal_opaque (`%wbase) (wbase k g roots f);
    like_walk k g roots f;
    like_own k g roots f s';
    like_count k g f s';
    like_grey k g roots s f s';
    like_sound k g roots f s';
    like_flagged k g f s';
    let st (i: nat) (w: wk) : Lemma (requires M1.nth f.fws i == Some w) (ensures Stopped? w.pc) =
      assert (fwk f i == Some w); assert (wrec_ok k g f.fh i w) in
    FStar.Classical.forall_intro_2 (fun i w -> FStar.Classical.move_requires (st i) w);
    LS.all_stopped_intro f.fws;
    reveal_opaque (`%fin_ok) (fin_ok s');
    walked_black k g s' f
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let fix_round (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (f: fx)
  : Lemma (requires walked k g roots s f /\ f.fn > 0)
          (ensures inv k g roots { s with heap = f.fh; wks = restart f.fws; count = f.fn; ovf_main = f.fom })
  = let s' = { s with heap = f.fh; wks = restart f.fws; count = f.fn; ovf_main = f.fom } in
    like_restart k g roots f;
    FStar.Classical.forall_intro (LS.nth_restart f.fws);
    like_own k g roots f s';
    like_count k g f s';
    like_grey k g roots s f s';
    like_sound k g roots f s';
    reveal_opaque (`%fin_ok) (fin_ok s');
    walked_black k g s' f
#pop-options

/// ---------------------------------------------------------------------------
/// The main step
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let main_fix (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires ctx k g roots /\ inv k g roots s /\ ~s.finished /\ all_stopped s.wks /\ flagged s)
          (ensures inv k g roots (main_step k s))
  = let f0 = start_fx s in
    walk_start k g roots s;
    walk_step k g roots f0 (objs_list s.heap) (U64.v zero_addr);
    let f = fix_walk k f0 (objs_list s.heap) in
    walk_end k g roots f;
    stopped_empty k g s;
    if f.fn = 0 then fix_done k g roots s f else fix_round k g roots s f
#pop-options

let main_inv (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires ctx k g roots /\ inv k g roots s /\ ~s.finished /\ all_stopped s.wks)
          (ensures inv k g roots (main_step k s))
  = if flagged s then main_fix k g roots s else main_done k g roots s
