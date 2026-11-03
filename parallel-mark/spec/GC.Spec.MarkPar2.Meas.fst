/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Meas — how each action moves the measure
///
/// With om the objects' weight and wm the workers' weight (both computed
/// against g's layout, which recolouring keeps), from a state whose counter
/// is not 0 (the acting worker holds an item):
///   send       om unchanged; wm up by the entry's weight (at most 7) plus 1
///              (an idle target), or 0 if the inbox was full
///   grey_push  om not up (white -> grey); wm unchanged
///   accept     om not up; wm up by 4 if it sends the closure on, else 0
///   route      om not up; wm up by at most 8
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Meas

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
open FStar.List.Tot { (@) }

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar.Recolour
open GC.Spec.MarkPar2.Model
open GC.Spec.MarkPar2.Inv

module M1 = GC.Spec.MarkPar.Model
module I1 = GC.Spec.MarkPar.Inv
module Own = GC.Spec.MarkPar.Own
module LS = GC.Spec.MarkPar2.Lists
module U = GC.Spec.MarkPar2.Upd
module W = GC.Spec.MarkPar2.Weight

let om (k: cfg) (g: heap) (s: state) : nat = objs_w k s.heap s.wks (objs_list g)
let wm (k: cfg) (g: heap) (s: state) : nat = wks_w k g s.count s.wks

let measure_parts (k: cfg) (g: heap) (s: state)
  : Lemma (requires recoloured g s.heap)
          (ensures measure k s == om k g s + wm k g s + (if s.finished then 0 else 1))
  = W.wks_w_rec k g s.heap s.count s.wks

/// ---------------------------------------------------------------------------
/// Stacks and object weights
/// ---------------------------------------------------------------------------

/// The stacks of two record lists agree.
let same_stacks (ws1 ws2: list wk) : prop =
  L.length ws1 == L.length ws2 /\
  (forall (i: nat). match M1.nth ws1 i, M1.nth ws2 i with
               | Some w1, Some w2 -> w1.stack == w2.stack
               | _ -> True)

let on_stack_same (k: cfg) (ws1 ws2: list wk) (x: obj_addr)
  : Lemma (requires same_stacks ws1 ws2) (ensures on_stack k ws1 x == on_stack k ws2 x)
  = Own.nth_lt ws1 (own k x); Own.nth_lt ws2 (own k x)

/// Same heap, same stacks: same objects' weight.
let om_same (k: cfg) (g: heap) (t1 t2: state)
  : Lemma (requires t1.heap == t2.heap /\ same_stacks t1.wks t2.wks)
          (ensures om k g t2 == om k g t1)
  = let aux (x: obj_addr) : Lemma (obj_w k t2.heap t2.wks x <= obj_w k t1.heap t1.wks x /\
                                   obj_w k t1.heap t1.wks x <= obj_w k t2.heap t2.wks x) =
      on_stack_same k t1.wks t2.wks x in
    FStar.Classical.forall_intro aux;
    W.objs_w_mono k t1.heap t2.heap t1.wks t2.wks (objs_list g);
    W.objs_w_mono k t2.heap t1.heap t2.wks t1.wks (objs_list g)

/// Replacing a record by one with the same stack keeps the stacks.
let set_same_stacks (ws: list wk) (i: nat) (w': wk)
  : Lemma (requires (match M1.nth ws i with Some w -> w.stack == w'.stack | None -> True))
          (ensures same_stacks ws (M1.set_nth ws i w'))
  = Own.length_set_nth ws i w';
    FStar.Classical.forall_intro (fun j -> Own.nth_set_nth ws i j w')

/// ---------------------------------------------------------------------------
/// send
/// ---------------------------------------------------------------------------

let send_m (k: cfg) (g: heap) (t: state) (me j: nat) (v: obj_addr)
  : Lemma (requires me < L.length t.wks /\ j < L.length t.wks /\ t.count > 0)
          (ensures om k g (send k t me j v) == om k g t /\
                   wm k g (send k t me j v) <= wm k g t + entry_w k g v + 1 /\
                   (send k t me j v).count > 0)
  = let t' = send k t me j v in
    Own.nth_lt t.wks j; Own.nth_lt t.wks me;
    let Some wj = M1.nth t.wks j in
    let Some wm0 = M1.nth t.wks me in
    if L.length wj.inbox >= k.cap_q then begin
      set_same_stacks t.wks me { wm0 with ovf = true };
      W.wks_w_set k g t.count t.wks me { wm0 with ovf = true };
      om_same k g t t'
    end else begin
      let wj' = { wj with inbox = wj.inbox @ [v] } in
      set_same_stacks t.wks j wj';
      W.wks_w_set k g t.count t.wks j wj';
      W.wkw_append k g t.count wj v;
      W.wks_w_count k g t.count (t.count + 1) t'.wks;
      om_same k g t t'
    end

/// ---------------------------------------------------------------------------
/// grey_push
/// ---------------------------------------------------------------------------

/// Pushing c on its owner's stack changes only c's membership.
let push_other (k: cfg) (ws: list wk) (me: nat) (w: wk) (c x: obj_addr)
  : Lemma (requires M1.nth ws me == Some w /\ own k c == me /\ x <> c)
          (ensures on_stack k (M1.set_nth ws me { w with stack = c :: w.stack }) x == on_stack k ws x)
  = Own.nth_lt ws me;
    Own.nth_set_nth ws me (own k x) { w with stack = c :: w.stack }

let push_self (k: cfg) (ws: list wk) (me: nat) (w: wk) (c: obj_addr)
  : Lemma (requires M1.nth ws me == Some w /\ own k c == me)
          (ensures on_stack k (M1.set_nth ws me { w with stack = c :: w.stack }) c == true)
  = Own.nth_lt ws me;
    Own.nth_set_nth ws me (own k c) { w with stack = c :: w.stack }

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let grey_push_m (k: cfg) (g: heap) (t: state) (me: nat) (c: obj_addr)
  : Lemma (requires recoloured g t.heap /\ me < L.length t.wks /\ own k c == me /\
                    Seq.mem c (objs g) /\ ~(is_blue c g) /\ t.count > 0)
          (ensures om k g (grey_push k t me c) <= om k g t /\
                   wm k g (grey_push k t me c) == wm k g t /\ (grey_push k t me c).count > 0)
  = let t' = grey_push k t me c in
    Own.nth_lt t.wks me;
    let Some w = M1.nth t.wks me in
    if is_white_x c t.heap then begin
      let h' = makeGray_x c t.heap in
      makeGray_eq c t.heap;
      recoloured_makeGray g t.heap c;
      makeGray_is_gray c t.heap;
      I1.others_keep t.heap c Gray;
      colors c t.heap; colors c h';
      let full = L.length w.stack >= k.cap_s in
      let w' = if full then { w with ovf = true } else { w with stack = c :: w.stack } in
      W.wks_w_set k g t.count t.wks me w';
      W.wks_w_count k g t.count t'.count t'.wks;
      let aux (x: obj_addr)
        : Lemma (requires L.memP x (objs_list g))
                (ensures obj_w k t'.heap t'.wks x <= obj_w k t.heap t.wks x)
        = LS.objs_list_mem g x;
          W.fields_rec g t.heap x;
          W.fields_rec g h' x;
          if full then begin
            set_same_stacks t.wks me w';
            on_stack_same k t.wks t'.wks x
          end else if x = c then push_self k t.wks me w c
          else push_other k t.wks me w c x
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
      W.objs_w_mono k t.heap t'.heap t.wks t'.wks (objs_list g)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// accept and route
/// ---------------------------------------------------------------------------

let accept_m (k: cfg) (g: heap) (t: state) (me: nat) (v: obj_addr)
  : Lemma (requires recoloured g t.heap /\ well_formed_heap g /\ me < L.length t.wks /\
                    L.length t.wks == nr k /\ own k v == me /\
                    Seq.mem (resolve_object v g) (objs g) /\ ~(is_blue (resolve_object v g) g) /\
                    t.count > 0)
          (ensures om k g (accept k t me v) <= om k g t /\
                   wm k g (accept k t me v) <= wm k g t + (if fwd k g v then 4 else 0))
  = let c = resolve_x v t.heap in
    assert (c == resolve_object v g);
    own_lt k c;
    if own k c <> me then begin
      send_m k g t me (own k c) c;
      resolve_self g c;
      assert (entry_w k g c == 3)
    end else grey_push_m k g t me c

let route_m (k: cfg) (g: heap) (t: state) (me: nat) (v: obj_addr)
  : Lemma (requires recoloured g t.heap /\ well_formed_heap g /\ me < L.length t.wks /\
                    L.length t.wks == nr k /\
                    Seq.mem (resolve_object v g) (objs g) /\ ~(is_blue (resolve_object v g) g) /\
                    t.count > 0)
          (ensures om k g (route k t me v) <= om k g t /\ wm k g (route k t me v) <= wm k g t + 8)
  = own_lt k v;
    if own k v = me then accept_m k g t me v
    else begin send_m k g t me (own k v) v; W.entry_w_le k g v end
