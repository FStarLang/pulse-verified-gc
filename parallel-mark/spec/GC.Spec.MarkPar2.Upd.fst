/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Upd — one worker's record replaced
///
/// Every worker step, and every action inside one, replaces one worker's
/// record, may recolour the heap, and may change the counter: the state
/// `upd t i w' h' n`.  For each part of the invariant, one lemma here says
/// what the replacement must satisfy for that part to carry over.  The
/// action lemmas (`GC.Spec.MarkPar2.Act`, `.Step`) only discharge those
/// obligations.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Upd

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
open FStar.List.Tot { (@) }

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar.Recolour
open GC.Spec.MarkPar2.Model
open GC.Spec.MarkPar2.Inv

module M1 = GC.Spec.MarkPar.Model
module Own = GC.Spec.MarkPar.Own
module LS = GC.Spec.MarkPar2.Lists

let upd (t: state) (i: nat) (w': wk) (h': heap) (n: nat) : state =
  { t with heap = h'; wks = M1.set_nth t.wks i w'; count = n }

let holds_w (w: wk) (v: obj_addr) : prop = L.memP v w.inbox \/ w.pc == Got v

let upd_wk (t: state) (i: nat) (w': wk) (h': heap) (n: nat)
  : Lemma (requires i < L.length t.wks)
          (ensures L.length (upd t i w' h' n).wks == L.length t.wks /\
                   (forall (j: nat). wk_of (upd t i w' h' n) j == (if j = i then Some w' else wk_of t j)))
  = FStar.Classical.forall_intro (LS.nth_upd t.wks i w')

/// The old record of worker i.
let old (t: state) (i: nat{i < L.length t.wks}) : wk =
  Own.nth_lt t.wks i; Some?.v (M1.nth t.wks i)

let old_eq (t: state) (i: nat)
  : Lemma (requires i < L.length t.wks) (ensures wk_of t i == Some (old t i))
  = Own.nth_lt t.wks i

/// ---------------------------------------------------------------------------
/// own_ok
/// ---------------------------------------------------------------------------

let own_upd (k: cfg) (g: heap) (t: state) (i: nat) (w': wk) (h': heap) (n: nat)
  : Lemma (requires own_ok k g t /\ i < L.length t.wks /\ recoloured g h' /\ wk_ok k g h' i w' /\
                    (forall (j: nat) (w: wk). j <> i /\ wk_of t j == Some w ==> wk_ok k g h' j w))
          (ensures own_ok k g (upd t i w' h' n))
  = reveal_opaque (`%own_ok) (own_ok k g t);
    reveal_opaque (`%own_ok) (own_ok k g (upd t i w' h' n));
    upd_wk t i w' h' n

/// The heap unchanged: recoloured comes from own_ok itself.
let own_upd_same (k: cfg) (g: heap) (t: state) (i: nat) (w': wk) (n: nat)
  : Lemma (requires own_ok k g t /\ i < L.length t.wks /\ wk_ok k g t.heap i w' /\
                    (forall (j: nat) (w: wk). j <> i /\ wk_of t j == Some w ==> wk_ok k g t.heap j w))
          (ensures own_ok k g (upd t i w' t.heap n))
  = reveal_opaque (`%own_ok) (own_ok k g t);
    own_upd k g t i w' t.heap n

/// Every other record, as own_ok gives it.
let own_others (k: cfg) (g: heap) (t: state) (i: nat)
  : Lemma (requires own_ok k g t)
          (ensures forall (j: nat) (w: wk). j <> i /\ wk_of t j == Some w ==> wk_ok k g t.heap j w)
  = reveal_opaque (`%own_ok) (own_ok k g t)

let own_rec (k: cfg) (g: heap) (t: state) (i: nat) (w: wk)
  : Lemma (requires own_ok k g t /\ wk_of t i == Some w) (ensures wk_ok k g t.heap i w)
  = reveal_opaque (`%own_ok) (own_ok k g t)

let own_len (k: cfg) (g: heap) (t: state)
  : Lemma (requires own_ok k g t) (ensures L.length t.wks == nr k)
  = reveal_opaque (`%own_ok) (own_ok k g t)

let own_heap (k: cfg) (g: heap) (t: state)
  : Lemma (requires own_ok k g t) (ensures recoloured g t.heap)
  = reveal_opaque (`%own_ok) (own_ok k g t)

let size_append (w: wk) (v: obj_addr)
  : Lemma (LS.size ({ w with inbox = w.inbox @ [v] }) == LS.size w + 1 /\
           (forall (u: obj_addr). L.memP u (w.inbox @ [v]) <==> L.memP u w.inbox \/ u == v))
  = L.append_length w.inbox [v];
    FStar.Classical.forall_intro (L.append_memP w.inbox [v])

/// ---------------------------------------------------------------------------
/// count_ok
/// ---------------------------------------------------------------------------

let count_upd (t: state) (i: nat) (w': wk) (h': heap) (n: nat)
  : Lemma (requires count_ok t /\ i < L.length t.wks /\
                    n + LS.size (old t i) == t.count + LS.size w' /\
                    (n == 0 \/ t.count > 0) /\ (Stopped? w'.pc ==> n == 0))
          (ensures count_ok (upd t i w' h' n))
  = reveal_opaque (`%count_ok) (count_ok t);
    reveal_opaque (`%count_ok) (count_ok (upd t i w' h' n));
    upd_wk t i w' h' n;
    old_eq t i;
    LS.counted_set t.wks i w'

/// A worker holding a counted item: the counter is positive, no worker has
/// stopped.
let busy_count (s: state) (me: nat)
  : Lemma (requires count_ok s /\ held (pc_of s me) == 1)
          (ensures s.count >= 1 /\
                   (forall (j: nat) (w: wk). wk_of s j == Some w ==> ~(Stopped? w.pc)))
  = reveal_opaque (`%count_ok) (count_ok s);
    LS.counted_ge s.wks me

let count_pos (s: state) (i: nat)
  : Lemma (requires count_ok s /\ i < L.length s.wks)
          (ensures LS.size (old s i) <= s.count)
  = reveal_opaque (`%count_ok) (count_ok s);
    old_eq s i;
    LS.counted_ge s.wks i

/// ---------------------------------------------------------------------------
/// flagged
/// ---------------------------------------------------------------------------

let flagged_upd (t: state) (i: nat) (w': wk) (h': heap) (n: nat)
  : Lemma (requires i < L.length t.wks)
          (ensures ((old t i).ovf == w'.ovf ==> flagged (upd t i w' h' n) == flagged t) /\
                   ((old t i).ovf ==> w'.ovf ==> flagged t ==> flagged (upd t i w' h' n)) /\
                   (w'.ovf ==> flagged (upd t i w' h' n)))
  = old_eq t i;
    LS.any_ovf_set t.wks i w';
    LS.any_ovf_set_same t.wks i w'

/// ---------------------------------------------------------------------------
/// grey_ok
/// ---------------------------------------------------------------------------

let grey_upd (k: cfg) (g: heap) (t t': state)
  : Lemma (requires grey_ok k g t /\
                    (forall (x: obj_addr). Seq.mem x (objs g) /\ is_gray x t'.heap ==>
                       (is_gray x t.heap /\
                        (L.memP x (stack_of t (own k x)) ==> L.memP x (stack_of t' (own k x))) /\
                        (flagged t ==> flagged t')) \/
                       L.memP x (stack_of t' (own k x)) \/ flagged t'))
          (ensures grey_ok k g t')
  = reveal_opaque (`%grey_ok) (grey_ok k g t);
    reveal_opaque (`%grey_ok) (grey_ok k g t')

/// ---------------------------------------------------------------------------
/// sound, roots_ok, fin_ok
/// ---------------------------------------------------------------------------

let sound_upd (g: heap) (roots: list obj_addr) (t: state) (i: nat) (w': wk) (h': heap) (n: nat)
  : Lemma (requires sound g roots t /\ i < L.length t.wks /\
                    (forall (x: obj_addr). Seq.mem x (objs g) /\ (is_gray x h' \/ is_black x h') ==>
                       is_gray x t.heap \/ is_black x t.heap \/ M1.reachable g roots x) /\
                    (forall (v: obj_addr). holds_w w' v ==>
                       holds_w (old t i) v \/ M1.reachable g roots (resolve_object v g)))
          (ensures sound g roots (upd t i w' h' n))
  = let t' = upd t i w' h' n in
    reveal_opaque (`%sound) (sound g roots t);
    reveal_opaque (`%sound) (sound g roots t');
    upd_wk t i w' h' n;
    old_eq t i;
    let hl (j: nat) (v: obj_addr)
      : Lemma (requires holds t' j v) (ensures M1.reachable g roots (resolve_object v g))
      = if j = i then begin
          assert (holds_w w' v);
          let a () : Lemma (requires holds_w (old t i) v) (ensures holds t i v) = () in
          FStar.Classical.move_requires a ()
        end else assert (holds t j v)
    in
    FStar.Classical.forall_intro_2 (fun j v -> FStar.Classical.move_requires (hl j) v)

let roots_upd (g: heap) (roots: list obj_addr) (t t': state)
  : Lemma (requires roots_ok g roots t /\
                    (forall (x: obj_addr). ~(is_white x t.heap) ==> ~(is_white x t'.heap)))
          (ensures roots_ok g roots t')
  = reveal_opaque (`%roots_ok) (roots_ok g roots t);
    reveal_opaque (`%roots_ok) (roots_ok g roots t')

let fin_running (t: state)
  : Lemma (requires ~t.finished) (ensures fin_ok t)
  = reveal_opaque (`%fin_ok) (fin_ok t)

/// ---------------------------------------------------------------------------
/// keeps
/// ---------------------------------------------------------------------------

let keeps_upd (k: cfg) (g: heap) (t: state) (i: nat) (w': wk) (h': heap) (n: nat)
  : Lemma (requires i < L.length t.wks /\
                    (forall (x: obj_addr). is_black x h' ==> is_black x t.heap) /\
                    (forall (x: obj_addr). ~(is_white x t.heap) ==> ~(is_white x h')) /\
                    (forall (v: obj_addr). holds_w (old t i) v ==> holds_w w' v) /\
                    (Scan? (old t i).pc ==> w'.pc == (old t i).pc) /\
                    (flagged t ==> flagged (upd t i w' h' n)))
          (ensures keeps k g t (upd t i w' h' n))
  = upd_wk t i w' h' n;
    old_eq t i;
    let t' = upd t i w' h' n in
    let hl (j: nat) (v: obj_addr) : Lemma (requires holds t j v) (ensures holds t' j v) = () in
    FStar.Classical.forall_intro_2 (fun j v -> FStar.Classical.move_requires (hl j) v);
    let us (x: obj_addr) (j: nat) : Lemma (requires unscanned k t x j) (ensures unscanned k t' x j) = () in
    FStar.Classical.forall_intro_2 (fun x j -> FStar.Classical.move_requires (us x) j)
